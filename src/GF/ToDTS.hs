{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

Translation from GF abstract syntax trees (@PGF.Expr@) into UDTT pretermes.

@
  PN                      Entity
  N, CN, VP, Comp         Entity -> type
  A, AP, RCl, RS          Entity -> type
  RP                      (Entity -> type) -> Entity -> type
  NP                      (Entity -> type) -> type
  Det, Quant              (Entity -> type) -> (Entity -> type) -> type
  V2, Prep                Entity -> Entity -> type
  VV                      (Entity -> type) -> Entity -> type
  VPSlash                 ((Entity -> type) -> type) -> Entity -> type
  Cl, S, Phr              type
  Num, Pol, Temp          ignored
@

The fragment grows problem by problem over FraCaS Section 1; the tests in
@test\/GF\/testFraCaS.hs@ list the problems it covers end to end.
-}

module GF.ToDTS (
  -- * Errors
  TranslationError(..)
  -- * Translation
  , gfToDts
  , interpret
  -- * Signature
  , signatureOf
  ) where

import qualified Data.Map as M
import qualified Data.Text.Lazy as T
import qualified PGF
import qualified DTS.UDTTdeBruijn as U
import qualified DTS.UDTTwithName as UwN
import qualified DTS.DTTdeBruijn as DTT

-- | Reasons why an abstract syntax tree cannot be translated.
data TranslationError =
  UnsupportedFunction String    -- ^ An RGL abstract function with no interpretation (name/arity)
  | MalformedTree String        -- ^ A tree which is not an application of an abstract function
  deriving (Eq, Show)

-- | Translates a GF abstract syntax tree into a UDTT preterm.
gfToDts :: PGF.Expr -> Either TranslationError U.Preterm
gfToDts expr = U.betaReduce <$> translate expr

translate :: PGF.Expr -> Either TranslationError U.Preterm
translate expr = case PGF.unApp expr of
  Nothing -> Left $ MalformedTree $ PGF.showExpr [] expr
  Just (fun, args) -> case interpret fun of
    Nothing -> Left $ UnsupportedFunction $
                 PGF.showCId fun ++ "/" ++ show (length args)
    Just meaning -> foldl U.App meaning <$> mapM translate args

-- | The interpretation of an abstract function, if the fragment covers it.
interpret :: PGF.CId -> Maybe U.Preterm
interpret cid = case M.lookup name structural of -- structural を引く
  Just meaning -> Just $ UwN.toDeBruijn [] meaning -- 当たれば de Bruijn に変換して返す
  Nothing -> lexical name -- 外れれば lexical に回す
  where name = PGF.showCId cid -- PGF.CId を showCId で String にする("DetCN")

-- | The interpretation of the structural functions of the grammar.
-- | Todo: データセットで使われている関数に対応する
structural :: M.Map String UwN.Preterm
structural = M.fromList [
  -- phrases and clauses
  ("Sentence", lam s (var s))                                    -- S -> Phr
  , ("UseCl", lam t $ lam pl $ lam c $ var c)                    -- Temp -> Pol -> Cl -> S
  , ("PredVP", lam np $ lam vp $                                 -- NP -> VP -> Cl
      app (UwN.Proj UwN.Snd (var np)) (var vp))
  -- noun phrases
  , ("UseN", lam p $ var p)                                      -- N -> CN
  , ("DetCN", lam d $ lam p $                                    -- Det -> CN -> NP
      UwN.Pair (var p) (app (var d) (var p)))
  , ("UsePN", lam x $ UwN.Pair                                   -- PN -> NP
      (lam y (UwN.Eq UwN.Entity (var y) (var x)))
      (lam p (app (var p) (var x))))
  , ("DetQuant", lam q $ lam n $ var q)                          -- Quant -> Num -> Det
  , ("IndefArt", lam p $ lam q $                                 -- Quant
      UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var p) (var x)) (app (var q) (var x))))
  -- The definite article presupposes an entity of which the restrictor
  -- holds: the presupposition is an underspecified term, whose resolution
  -- (anaphoric, or accommodated for premises) is the business of
  -- 'GF.Inference'.
  , ("DefArt", lam p $ lam q $                                   -- Quant
      app (var q) (UwN.Proj UwN.Fst
        (UwN.Asp (UwN.Sigma x UwN.Entity (app (var p) (var x))))))
  -- plurality is ignored, so "some" is plain existential quantification
  , ("somePl_Det", lam p $ lam q $                               -- Det
      UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var p) (var x)) (app (var q) (var x))))
  , ("someSg_Det", lam p $ lam q $                               -- Det
      UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var p) (var x)) (app (var q) (var x))))
  -- negation is spelled out as a function into the bottom type, since the
  -- type checker has no rule for the Not constructor
  , ("no_Quant", lam p $ lam q $                                 -- Quant
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (UwN.Pi y (app (var q) (var x)) UwN.Bot)))
  , ("every_Det", lam p $ lam q $                                -- Det
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (app (var q) (var x))))
  -- "both" is read with universal force; its presupposition that the
  -- restrictor holds of exactly two entities is left to the @ machinery.
  , ("both_Det", lam p $ lam q $                                 -- Det
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (app (var q) (var x))))
  , ("each_Det", lam p $ lam q $                                 -- Det
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (app (var q) (var x))))
  -- The cardinality determiners are approximated existentially, which keeps
  -- their upward entailments and stays silent on the counts they state.
  , ("many_Det", existential), ("several_Det", existential)      -- Det
  , ("a_few_Det", existential), ("a_lot_of_Det", existential)    -- Det
  -- "neither" is "no" restricted to two: the universal denial is kept and
  -- the two-ness presupposition is left to the @ machinery.
  , ("neither_Det", lam p $ lam q $                              -- Det
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (UwN.Pi y (app (var q) (var x)) UwN.Bot)))
  -- adjectival modification, read intersectively
  , ("PositA", lam a $ var a)                                    -- A -> AP
  , ("AdjCN", lam a $ lam p $ lam x $                            -- AP -> CN -> CN
      UwN.Sigma u (app (var a) (var x)) (app (var p) (var x)))
  -- Degree adverbs are read as one more predicate of the modified entity,
  -- which keeps "really A" strictly stronger than "A".
  , ("AdAP", lam a $ lam p $ lam x $                             -- AdA -> AP -> AP
      UwN.Sigma u (app (var a) (var x)) (app (var p) (var x)))
  , ("PositAdvAdj", lam a $ var a)                               -- A -> Adv
  , ("AdvCN", lam p $ lam a $ lam x $                            -- CN -> Adv -> CN
      UwN.Sigma u (app (var p) (var x)) (app (var a) (var x)))
  , ("AdvAP", lam p $ lam a $ lam x $                            -- AP -> Adv -> AP
      UwN.Sigma u (app (var p) (var x)) (app (var a) (var x)))
  -- Predeterminers act on the enriched noun phrase: all_Predet rebuilds
  -- universal force from the restrictor, which is why noun phrases carry
  -- one (the pair never reaches the prover: projections disappear under
  -- beta reduction).  "at least" keeps the lower-bound reading of its
  -- noun phrase; "most" falls back to it, joining the existential
  -- approximations of the cardinality determiners.
  -- a bare determiner quantifies over the trivial restrictor ("one ...")
  , ("DetNP", lam d $ UwN.Pair                                   -- Det -> NP
      (lam y UwN.Top) (app (var d) (lam y UwN.Top)))
  , ("AdvNP", lam np $ lam a $ UwN.Pair                          -- NP -> Adv -> NP
      (lam x (UwN.Sigma u (app (UwN.Proj UwN.Fst (var np)) (var x)) (app (var a) (var x))))
      (lam q (app (UwN.Proj UwN.Snd (var np)) (lam x
        (UwN.Sigma u (app (var a) (var x)) (app (var q) (var x)))))))
  -- PROTOTYPE: the possessive presupposes its possessor, but nesting one
  -- underspecified term inside another defeats the global accommodation of
  -- GF.Inference, so the possessor is dropped: "the world's greatest tenor"
  -- is read as "the greatest tenor".  Iterated accommodation is future work.
  , ("GenNP", lam np $ lam p $ lam q $                           -- NP -> Quant
      app (var q) (UwN.Proj UwN.Fst
        (UwN.Asp (UwN.Sigma x UwN.Entity (app (var p) (var x))))))
  , ("DetQuantOrd", lam d $ lam n $ lam o $ lam p $              -- Quant -> Num -> Ord -> Det
      app (var d) (lam x (UwN.Sigma u (app (var o) (var x)) (app (var p) (var x)))))
  -- PROTOTYPE: the superlative is read as its positive, pending a
  -- treatment of comparison.
  , ("OrdSuperl", lam a $ var a)                                 -- A -> Ord
  , ("PredetNP", lam d $ lam np $ app (var d) (var np))          -- Predet -> NP -> NP
  , ("all_Predet", lam np $ UwN.Pair                             -- Predet
      (UwN.Proj UwN.Fst (var np))
      (lam q $ UwN.Pi x UwN.Entity
        (UwN.Pi u (app (UwN.Proj UwN.Fst (var np)) (var x))
          (app (var q) (var x)))))
  , ("at_least_Predet", lam np $ var np)                         -- Predet
  , ("most_Predet", lam np $ var np)                             -- Predet
  -- relative clauses: a restrictive relative is one more intersective
  -- restriction on the noun, and the relative pronoun adds nothing
  , ("IdRP", lam p $ var p)                                      -- RP
  , ("RelVP", lam r $ lam vp $ app (var r) (var vp))             -- RP -> VP -> RCl
  , ("UseRCl", lam t $ lam pl $ lam c $ var c)                   -- Temp -> Pol -> RCl -> RS
  , ("RelCN", lam p $ lam c $ lam x $                            -- CN -> RS -> CN
      UwN.Sigma u (app (var p) (var x)) (app (var c) (var x)))
  -- verb phrases
  , ("UseComp", lam co $ var co)                                 -- Comp -> VP
  , ("CompCN", lam p $ var p)                                    -- CN -> Comp
  , ("CompAP", lam a $ var a)                                    -- AP -> Comp
  , ("CompAdv", lam a $ var a)                                   -- Adv -> Comp
  -- "there is NP": the noun phrase applied to the trivial property
  , ("ExistNP", lam np $                                         -- NP -> Cl
      app (UwN.Proj UwN.Snd (var np)) (lam x UwN.Top))
  -- prepositions are two place relations between the subject and the
  -- object of the preposition
  , ("PrepNP", lam p $ lam np $ lam x $                          -- Prep -> NP -> Adv
      app (UwN.Proj UwN.Snd (var np)) (lam y (app (app (var p) (var y)) (var x))))
  -- a bare mass noun is read existentially, like the bare plurals
  , ("MassNP", lam n $ UwN.Pair (var n) (lam q $                 -- CN -> NP
      UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var n) (var x)) (app (var q) (var x)))))
  , ("SlashV2a", lam v $ lam np $ lam x $                        -- V2 -> VPSlash
      app (UwN.Proj UwN.Snd (var np)) (lam y (app (app (var v) (var y)) (var x))))
  , ("ComplSlash", lam vs $ lam np $ app (var vs) (var np))      -- VPSlash -> NP -> VP
  , ("UseV", lam v $ var v)                                      -- V -> VP
  , ("Slash3V3", lam v $ lam np $ lam q $ lam x $                -- V3 -> NP -> VPSlash
      app (UwN.Proj UwN.Snd (var q)) (lam y (app (UwN.Proj UwN.Snd (var np)) (lam z
        (app (app (app (var v) (var y)) (var z)) (var x))))))
  -- "be NP": the subject is identified with a witness of the noun phrase
  , ("CompNP", lam np $ lam x $                                  -- NP -> Comp
      app (UwN.Proj UwN.Snd (var np)) (lam y (UwN.Eq UwN.Entity (var y) (var x))))
  -- past participles restrict the noun phrase: "the results published"
  -- are results which someone published
  , ("PPartNP", lam np $ lam v $ UwN.Pair                        -- NP -> V2 -> NP
      (lam x (UwN.Sigma u (app (UwN.Proj UwN.Fst (var np)) (var x))
        (UwN.Sigma y UwN.Entity (app (app (var v) (var x)) (var y)))))
      (lam q (app (UwN.Proj UwN.Snd (var np)) (lam x (UwN.Sigma u
        (UwN.Sigma y UwN.Entity (app (app (var v) (var x)) (var y)))
        (app (var q) (var x)))))))
  , ("ComplVV", lam v $ lam vp $ app (var v) (var vp))           -- VV -> VP -> VP
  -- Verb phrase adverbs are read as predicates of the subject, conjoined
  -- with the verb phrase; without an event argument this is as close as
  -- the fragment comes to "x finished [it] on time".
  , ("AdvVP", lam vp $ lam a $ lam x $                           -- VP -> Adv -> VP
      UwN.Sigma u (app (var vp) (var x)) (app (var a) (var x)))
  -- "used to" marks tense and aspect, which the fragment ignores, so it
  -- denotes the identity on verb phrases.  Intensional complement verbs
  -- such as want_VV are deliberately left out.
  , ("use_VV", lam vp $ var vp)                                  -- VV
  -- PROTOTYPE: "can" is read transparently, which overgenerates in
  -- principle (can P would entail P); the right-to problems only need the
  -- phrase to translate uniformly.  A modal treatment is future work.
  , ("can_VV", lam vp $ var vp)                                  -- VV
  -- PROTOTYPE: the content of "the right to P" is applied to the right
  -- itself, which is absurd but deterministic: distinct contents stay
  -- distinct and identical phrases translate identically.  A proper
  -- intensional treatment is future work.
  , ("EmbedVP", lam vp $ var vp)                                 -- VP -> SC
  , ("ComplN2", lam n $ lam np $ lam x $                         -- N2 -> NP -> CN
      app (UwN.Proj UwN.Snd (var np)) (lam y (app (app (var n) (var y)) (var x))))
  , ("SentCN", lam n $ lam c $ lam x $                           -- CN -> SC -> CN
      UwN.Sigma u (app (var n) (var x)) (app (var c) (var x)))
  -- The fragment ignores number, polarity and tense.  Ignoring number
  -- reads a bare plural existentially; the generic reading some premises
  -- call for (e.g. problem 013) is a known limitation.
  , ("NumSg", UwN.Unit)
  , ("NumPl", UwN.Unit)
  -- PROTOTYPE: cardinalities are ignored, so "three N" is read as bare
  -- existential; sound only as a lower bound (under at_least).  at_most
  -- is deliberately left unsupported, since the reading would be unsound.
  , ("NumCard", lam n $ UwN.Unit)
  , ("NumNumeral", lam n $ UwN.Unit)
  , ("N_two", UwN.Unit), ("N_three", UwN.Unit), ("N_ten", UwN.Unit)
  , ("PPos", UwN.Unit)
  , ("Past", UwN.Unit)
  , ("Present", UwN.Unit)
  , ("Future", UwN.Unit)
  ]

-- | Existential quantification: the reading the fragment gives "some" like
-- determiners whose cardinality it cannot state.
existential :: UwN.Preterm
existential = lam p $ lam q $
  UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var p) (var x)) (app (var q) (var x)))

-- | The signature of the constants which the translation of the given trees introduces.
-- | The arity of a content word is read off its category tag, so that a two place verb such as @win_V2@ is given the type
-- @entity -> entity -> type@.
signatureOf :: [PGF.Expr] -> DTT.Signature
signatureOf exprs = M.toList $ M.fromList $
  [ ("of", nPlacePred 2) ] ++
  [ (T.pack stem, typ)
  | name <- concatMap names exprs
  , (stem, tag) <- maybe [] (:[]) (splitTag name)
  , typ <- maybe [] (:[]) (lookup tag types) ]
  where
    names expr = case PGF.unApp expr of
                   Just (fun, args) -> PGF.showCId fun : concatMap names args
                   Nothing -> []
    types = [("PN", DTT.Entity)                     -- a proper name denotes an entity
            ,("N", nPlacePred 1), ("A", nPlacePred 1)
            ,("V", nPlacePred 1), ("Adv", nPlacePred 1)
            ,("AdA", nPlacePred 1), ("VP", nPlacePred 1)
            ,("N2", nPlacePred 1)  -- decomposed: the bare noun plus "of"
            ,("A2", nPlacePred 2), ("V2", nPlacePred 2)
            ,("Prep", nPlacePred 2)
            ,("V3", nPlacePred 3)]
    nPlacePred k = iterate (DTT.Pi DTT.Entity) DTT.Type !! k

-- | Splits @win_V2@ into the stem and the category tag.
splitTag :: String -> Maybe (String, String)
splitTag name = case break (== '_') (reverse name) of
  (revTag, '_':revStem) -> Just (reverse revStem, reverse revTag)
  _ -> Nothing

-- | Content words are interpreted as constants of the same name.  Function words are excluded, since they call for an interpretation of their own.
-- A relational noun is decomposed into the bare noun and a generic "of"
-- relation to its complement, so that "Nobel prize for literature" entails
-- "Nobel prize" and the N and N2 readings of one stem share a constant.
lexical :: String -> Maybe U.Preterm
lexical name = case splitTag name of
  Just (stem, "N2") -> Just $ U.Lam $ U.Lam $
    U.Sigma (U.App (U.Con (T.pack stem)) (U.Var 0))
            (U.App (U.App (U.Con "of") (U.Var 1)) (U.Var 2))
  Just (stem, tag) | tag `elem` contentTags -> Just $ U.Con $ T.pack stem
  _ -> Nothing
  where contentTags = ["N", "N2", "A", "A2", "V", "V2", "V3", "PN", "Adv", "AdA", "Prep", "VP"]

-- variable names, kept distinct within each interpretation

a, c, co, d, n, np, o, p, pl, q, r, s, t, u, v, vp, vs, x, y, z :: UwN.VarName
a = UwN.VarName 'a' 0
c = UwN.VarName 'c' 0
r = UwN.VarName 'r' 0
co = UwN.VarName 'C' 0
d = UwN.VarName 'd' 0
n = UwN.VarName 'n' 0
np = UwN.VarName 'N' 0
o = UwN.VarName 'o' 0
p = UwN.VarName 'p' 0
pl = UwN.VarName 'l' 0
q = UwN.VarName 'q' 0
s = UwN.VarName 's' 0
t = UwN.VarName 't' 0
u = UwN.VarName 'u' 0
v = UwN.VarName 'v' 0
vp = UwN.VarName 'V' 0
vs = UwN.VarName 'S' 0
x = UwN.VarName 'x' 0
y = UwN.VarName 'y' 0
z = UwN.VarName 'z' 0

lam :: UwN.VarName -> UwN.Preterm -> UwN.Preterm
lam = UwN.Lam

var :: UwN.VarName -> UwN.Preterm
var = UwN.Var

app :: UwN.Preterm -> UwN.Preterm -> UwN.Preterm
app = UwN.App
