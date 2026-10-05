{-# LANGUAGE OverloadedStrings #-}

{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

End-to-end tests of the GF pipeline over the FraCaS treebank: each problem is
loaded, translated with 'GF.ToDTS.gfToDts', and run through 'GF.Inference.infer'
with the wani prover, and the verdict is compared with the expectation below.

The treebank is distributed separately under GPL v3, so its location is taken
from the environment, as in the @gf@ command of the lightblue executable:

* @FRACAS_TREEBANK@ — path of @FraCaSBankI.gf@
* @FRACAS_XML@ — path of @fracas.xml@

When either variable is unset the suite reports every test as skipped and
exits successfully, so that @stack test@ stays green on machines without the
treebank.
-}

module Main where

import Control.Monad (forM)
import Data.List (find)
import System.Environment (lookupEnv)
import System.Exit (exitFailure)
import qualified System.IO as S
import qualified DTS.QueryTypes as QT             --lightblue
import qualified DTS.NaturalLanguageInference as NLI --lightblue
import qualified GF.Inference as GFI              --lightblue
import qualified GF.TreebankLoader as GFTB        --lightblue

-- | A test case: a problem of the treebank and the verdict wani must reach.
-- The expectation is the gold answer of @fracas.xml@, written out here so that
-- a change of the gold data cannot silently weaken the suite.
data Case = Case {
  caseName :: String
  , caseProblem :: Int
  , expected :: GFTB.Answer
  }

cases :: [Case]
cases = [
  Case { caseName = "fracas_049", caseProblem = 49, expected = GFTB.Yes }
  ]

-- | The proof search runs with the defaults of the @gf@ command of
-- @lightblueMain@, so that a test failure is reproducible from the shell with
-- @lightblue gf --problem N@.
prover :: QT.Prover
prover = NLI.getProver NLI.Wani $ QT.defaultProofSearchSetting {
  QT.maxDepth = Just 5
  , QT.maxTime = Just 100000
  }

main :: IO ()
main = do
  S.hSetBuffering S.stdout S.NoBuffering
  treebank <- lookupEnv "FRACAS_TREEBANK"
  answers <- lookupEnv "FRACAS_XML"
  case (,) <$> treebank <*> answers of
    Nothing -> putStrLn $ "SKIP: set FRACAS_TREEBANK and FRACAS_XML to run "
                          ++ "the FraCaS tests (" ++ show (length cases)
                          ++ " cases skipped)"
    Just (treebankPath, xmlPath) -> do
      problems <- GFTB.loadFraCaS treebankPath xmlPath
      results <- forM cases $ \c -> do
        putStr $ caseName c ++ ": "
        outcome <- runCase problems c
        putStrLn $ either ("FAIL: " ++) (const "ok") outcome
        return outcome
      case [err | Left err <- results] of
        [] -> putStrLn $ show (length results) ++ " case(s) passed"
        errs -> do
          putStrLn $ show (length errs) ++ " of " ++ show (length results)
                     ++ " case(s) failed"
          exitFailure

-- | Runs one problem end to end.  'Left' describes the failure.
runCase :: [GFTB.Problem] -> Case -> IO (Either String ())
runCase problems c =
  case find ((== caseProblem c) . GFTB.problemId) problems of
    Nothing -> return $ Left $ "no problem numbered " ++ show (caseProblem c)
    Just problem -> case GFI.translateProblem problem of
      Left err -> return $ Left $ "translation failed: " ++ err
      Right translation -> do
        verdict <- GFI.infer prover 1 False translation
        return $ case verdict of
          GFI.Infelicitous name ->
            Left $ "the felicity check of " ++ name ++ " failed"
          GFI.Felicitous result
            | GFI.answer result == expected c -> Right ()
            | otherwise -> Left $ "expected " ++ show (expected c)
                                  ++ " but inferred "
                                  ++ show (GFI.answer result)
