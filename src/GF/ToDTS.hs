{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

Translation from GF abstract syntax trees (@PGF.Expr@) into UDTT pretermes.

@
  N, CN, A, VP, RCl, RS   Entity -> type
  NP                      (Entity -> type) -> type
  Det, Quant              (Entity -> type) -> (Entity -> type) -> type
  Ord                     (Entity -> type) -> (Entity -> type)
  V2                      Entity -> Entity -> type
  VPSlash                 ((Entity -> type) -> type) -> Entity -> type
  Comp                    Entity -> type
  Cl, S, Phr              type
  Num, Pol, Temp, RP      ignored
@

The fragment currently covers the abstract functions of FraCaS problems 001 and 049.
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
interpret cid = case M.lookup name structural of
  Just meaning -> Just $ UwN.toDeBruijn [] meaning
  Nothing -> lexical name
  where name = PGF.showCId cid

-- | The interpretation of the structural functions of the grammar.
structural :: M.Map String UwN.Preterm
structural = M.fromList [
  -- phrases and clauses
  ("Sentence", lam s (var s))                                    -- S -> Phr
  , ("UseCl", lam t $ lam pl $ lam c $ var c)                    -- Temp -> Pol -> Cl -> S
  , ("PredVP", lam np $ lam vp $ app (var np) (var vp))          -- NP -> VP -> Cl
  , ("ExistNP", lam np $ app (var np) (lam x UwN.Top))           -- NP -> Cl
  -- noun phrases
  , ("UseN", lam p $ var p)                                      -- N -> CN
  , ("DetCN", lam d $ lam p $ app (var d) (var p))               -- Det -> CN -> NP
  , ("DetQuant", lam q $ lam n $ var q)                          -- Quant -> Num -> Det
  , ("DetQuantOrd", lam q $ lam n $ lam o $ lam p $              -- Quant -> Num -> Ord -> Det
      app (var q) (app (var o) (var p)))
  -- quantifiers.  The definite article introduces an @ operator, whose
  -- resolution is left to the prover.
  , ("IndefArt", lam p $ lam q $                                 -- Quant
      UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var p) (var x)) (app (var q) (var x))))
  , ("DefArt", lam p $ lam q $                                   -- Quant
      app (var q) (definite (var p)))
  , ("GenNP", lam np $ lam p $ lam q $                           -- NP -> Quant
      app (var np) (lam y (app (var q)
        (definite (lam x (UwN.Sigma u (app (var p) (var x))
                                      (app (app (UwN.Con "of") (var y)) (var x))))))))
  , ("OrdSuperl", lam a $ lam p $ lam x $                        -- A -> Ord
      UwN.Sigma u (app (var p) (var x)) (app (var a) (var x)))
  , ("every_Det", lam p $ lam q $                                -- Det
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (app (var q) (var x))))
  -- verb phrases
  , ("UseComp", lam co $ var co)                                 -- Comp -> VP
  , ("CompCN", lam p $ var p)                                    -- CN -> Comp
  , ("SlashV2a", lam v $ lam np $ lam x $                        -- V2 -> VPSlash
      app (var np) (lam y (app (app (var v) (var y)) (var x))))
  , ("ComplSlash", lam vs $ lam np $ app (var vs) (var np))      -- VPSlash -> NP -> VP
  -- relative clauses
  , ("UseRCl", lam t $ lam pl $ lam r $ var r)                   -- Temp -> Pol -> RCl -> RS
  , ("RelVP", lam rp $ lam vp $ var vp)                          -- RP -> VP -> RCl
  , ("RelCN", lam p $ lam r $ lam x $                            -- CN -> RS -> CN
      UwN.Sigma u (app (var p) (var x)) (app (var r) (var x)))
  -- the fragment ignores number, polarity, tense and the relative pronoun
  , ("NumSg", UwN.Unit)
  , ("NumPl", UwN.Unit)
  , ("PPos", UwN.Unit)
  , ("Past", UwN.Unit)
  , ("Present", UwN.Unit)
  , ("IdRP", UwN.Unit)
  ]

-- | @definite p@ is the first projection of an underspecified term of the
-- type of the entities which satisfy @p@, i.e. the DTS treatment of a
-- presupposition triggered by a definite noun phrase.
definite :: UwN.Preterm -> UwN.Preterm
definite p = UwN.Proj UwN.Fst (UwN.Asp (UwN.Sigma x UwN.Entity (app p (var x))))

-- | The signature of the constants which the translation of the given trees
-- introduces.  The arity of a content word is read off its category tag, so
-- that a two place verb such as @win_V2@ is given the type
-- @entity -> entity -> type@.
signatureOf :: [PGF.Expr] -> DTT.Signature
signatureOf exprs = M.toList $ M.fromList
  [ (T.pack stem, nPlacePred arity)
  | name <- concatMap names exprs
  , (stem, tag) <- maybe [] (:[]) (splitTag name)
  , arity <- maybe [] (:[]) (lookup tag arities) ]
  where
    names expr = case PGF.unApp expr of
                   Just (fun, args) -> PGF.showCId fun : concatMap names args
                   Nothing -> []
    arities = [("N", 1), ("A", 1), ("V", 1), ("Adv", 1)
              ,("N2", 2), ("A2", 2), ("V2", 2), ("V3", 3), ("PN", 0)]
    nPlacePred k = iterate (DTT.Pi DTT.Entity) DTT.Type !! k

-- | Splits @win_V2@ into the stem and the category tag.
splitTag :: String -> Maybe (String, String)
splitTag name = case break (== '_') (reverse name) of
  (revTag, '_':revStem) -> Just (reverse revStem, reverse revTag)
  _ -> Nothing

-- | Content words are interpreted as constants of the same name.  Function
-- words are excluded, since they call for an interpretation of their own.
lexical :: String -> Maybe U.Preterm
lexical name = case splitTag name of
  Just (stem, tag) | tag `elem` contentTags -> Just $ U.Con $ T.pack stem
  _ -> Nothing
  where contentTags = ["N", "N2", "A", "A2", "V", "V2", "V3", "PN", "Adv"]

-- variable names, kept distinct within each interpretation

a, c, co, d, n, np, o, p, pl, q, r, rp, s, t, u, v, vp, vs, x, y :: UwN.VarName
a = UwN.VarName 'a' 0
c = UwN.VarName 'c' 0
co = UwN.VarName 'C' 0
d = UwN.VarName 'd' 0
n = UwN.VarName 'n' 0
np = UwN.VarName 'N' 0
o = UwN.VarName 'o' 0
p = UwN.VarName 'p' 0
pl = UwN.VarName 'l' 0
q = UwN.VarName 'q' 0
r = UwN.VarName 'r' 0
rp = UwN.VarName 'R' 0
s = UwN.VarName 's' 0
t = UwN.VarName 't' 0
u = UwN.VarName 'u' 0
v = UwN.VarName 'v' 0
vp = UwN.VarName 'V' 0
vs = UwN.VarName 'S' 0
x = UwN.VarName 'x' 0
y = UwN.VarName 'y' 0

lam :: UwN.VarName -> UwN.Preterm -> UwN.Preterm
lam = UwN.Lam

var :: UwN.VarName -> UwN.Preterm
var = UwN.Var

app :: UwN.Preterm -> UwN.Preterm -> UwN.Preterm
app = UwN.App
