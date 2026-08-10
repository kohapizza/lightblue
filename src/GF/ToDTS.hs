{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

Translation from GF abstract syntax trees (@PGF.Expr@) into UDTT pretermes.

The target of the translation is an /underspecified/ preterm, i.e. anaphora
and presuppositions are left as @Asp@ (the \@ operator) and their resolution
is delegated to the theorem prover wani.
-}

module GF.ToDTS (
  -- * Errors
  TranslationError(..)
  -- * Translation
  , gfToDts
  ) where

import qualified PGF
import qualified DTS.UDTTdeBruijn as U

-- | Reasons why an abstract syntax tree cannot be translated.
data TranslationError =
  UnsupportedFunction String    -- ^ An RGL abstract function with no interpretation (name/arity)
  | MalformedTree String        -- ^ A tree which is not an application of an abstract function
  deriving (Eq, Show)

-- | Translates a GF abstract syntax tree into a UDTT preterm.
gfToDts :: PGF.Expr -> Either TranslationError U.Preterm
gfToDts expr = case PGF.unApp expr of
  Just (fun, args) -> Left $ UnsupportedFunction $
                        PGF.showCId fun ++ "/" ++ show (length args)
  Nothing          -> Left $ MalformedTree $ PGF.showExpr [] expr
