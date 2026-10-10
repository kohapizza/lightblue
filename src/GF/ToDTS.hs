{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

Translation from GF abstract syntax trees (@PGF.Expr@) into UDTT pretermes.

@
  PN                      Entity
  N, CN, VP, Comp         Entity -> type
  NP                      (Entity -> type) -> type
  Det, Quant              (Entity -> type) -> (Entity -> type) -> type
  V2                      Entity -> Entity -> type
  VPSlash                 ((Entity -> type) -> type) -> Entity -> type
  Cl, S, Phr              type
  Num, Pol, Temp          ignored
@

The fragment currently covers the abstract functions of FraCaS problem 049.
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
  , ("PredVP", lam np $ lam vp $ app (var np) (var vp))          -- NP -> VP -> Cl
  -- noun phrases
  , ("UseN", lam p $ var p)                                      -- N -> CN
  , ("DetCN", lam d $ lam p $ app (var d) (var p))               -- Det -> CN -> NP
  , ("UsePN", lam x $ lam p $ app (var p) (var x))               -- PN -> NP
  , ("DetQuant", lam q $ lam n $ var q)                          -- Quant -> Num -> Det
  , ("IndefArt", lam p $ lam q $                                 -- Quant
      UwN.Sigma x UwN.Entity (UwN.Sigma u (app (var p) (var x)) (app (var q) (var x))))
  , ("every_Det", lam p $ lam q $                                -- Det
      UwN.Pi x UwN.Entity (UwN.Pi u (app (var p) (var x)) (app (var q) (var x))))
  -- verb phrases
  , ("UseComp", lam co $ var co)                                 -- Comp -> VP
  , ("CompCN", lam p $ var p)                                    -- CN -> Comp
  , ("SlashV2a", lam v $ lam np $ lam x $                        -- V2 -> VPSlash
      app (var np) (lam y (app (app (var v) (var y)) (var x))))
  , ("ComplSlash", lam vs $ lam np $ app (var vs) (var np))      -- VPSlash -> NP -> VP
  -- the fragment ignores number, polarity and tense
  , ("NumSg", UwN.Unit)
  , ("PPos", UwN.Unit)
  , ("Past", UwN.Unit)
  , ("Present", UwN.Unit)
  ]

-- | The signature of the constants which the translation of the given trees introduces.
-- | The arity of a content word is read off its category tag, so that a two place verb such as @win_V2@ is given the type
-- @entity -> entity -> type@.
signatureOf :: [PGF.Expr] -> DTT.Signature
signatureOf exprs = M.toList $ M.fromList
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
            ,("N2", nPlacePred 2), ("A2", nPlacePred 2), ("V2", nPlacePred 2)
            ,("V3", nPlacePred 3)]
    nPlacePred k = iterate (DTT.Pi DTT.Entity) DTT.Type !! k

-- | Splits @win_V2@ into the stem and the category tag.
splitTag :: String -> Maybe (String, String)
splitTag name = case break (== '_') (reverse name) of
  (revTag, '_':revStem) -> Just (reverse revStem, reverse revTag)
  _ -> Nothing

-- | Content words are interpreted as constants of the same name.  Function words are excluded, since they call for an interpretation of their own.
lexical :: String -> Maybe U.Preterm
lexical name = case splitTag name of
  Just (stem, tag) | tag `elem` contentTags -> Just $ U.Con $ T.pack stem
  _ -> Nothing
  where contentTags = ["N", "N2", "A", "A2", "V", "V2", "V3", "PN", "Adv"]

-- variable names, kept distinct within each interpretation

c, co, d, n, np, p, pl, q, s, t, u, v, vp, vs, x, y :: UwN.VarName
c = UwN.VarName 'c' 0
co = UwN.VarName 'C' 0
d = UwN.VarName 'd' 0
n = UwN.VarName 'n' 0
np = UwN.VarName 'N' 0
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

lam :: UwN.VarName -> UwN.Preterm -> UwN.Preterm
lam = UwN.Lam

var :: UwN.VarName -> UwN.Preterm
var = UwN.Var

app :: UwN.Preterm -> UwN.Preterm -> UwN.Preterm
app = UwN.App
