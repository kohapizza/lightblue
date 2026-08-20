{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

Inference over the FraCaS GF treebank.  The abstract syntax trees of a problem
are translated into UDTT pretermes, the semantic felicity of each sentence is
checked, and the DTT context which the checks build is handed to a prover as a
proof search query.
-}

module GF.Inference (
  -- * Translation
  Sentence(..)
  , Translation(..)
  , translateProblem
  -- * Inference
  , Verdict(..)
  , Result(..)
  , FelicityCheck(..)
  , infer
  ) where

import qualified ListT                    --list-t
import qualified PGF                      --gf
import qualified DTS.UDTTdeBruijn as U    --lightblue
import qualified DTS.DTTdeBruijn as DTT   --lightblue
import qualified DTS.QueryTypes as QT     --lightblue
import qualified DTS.TypeChecker as TY    --lightblue
import qualified Interface.Tree as Tree   --lightblue
import qualified GF.ToDTS as ToDTS        --lightblue
import qualified GF.TreebankLoader as TB  --lightblue

-- | A sentence of a problem, with the representations the translation gives it.
data Sentence = Sentence {
  role :: String          -- ^ @Premise n@ or @Hypothesis@
  , tree :: PGF.Expr      -- ^ The abstract syntax tree of the treebank
  , preterm :: U.Preterm  -- ^ Its UDTT semantic representation
  }

-- | The translation of a whole problem.
data Translation = Translation {
  signature :: DTT.Signature  -- ^ The constants which the sentences introduce
  , sentences :: [Sentence]   -- ^ The premises, followed by the hypothesis
  }

-- | Translates the premises and the hypothesis of a problem.  The question is
-- left out, since it states the proposition the hypothesis states.
translateProblem :: TB.Problem -> Either String Translation
translateProblem problem = do
  hypo <- maybe (Left "the problem has no hypothesis") Right $ TB.hypothesis problem
  let trees = TB.premises problem ++ [hypo]
      roles = [ "Premise " ++ show i
              | i <- [(1::Int) .. length (TB.premises problem)] ] ++ ["Hypothesis"]
  preterms <- mapM translate trees
  return Translation { signature = ToDTS.signatureOf trees
                     , sentences = zipWith3 Sentence roles trees preterms }
  where
    translate expr = case ToDTS.gfToDts expr of
                       Right preterm' -> Right preterm'
                       Left err -> Left $ show err ++ " in " ++ PGF.showExpr [] expr

-- | The outcome of running a problem.
data Verdict =
  Infelicitous String  -- ^ The named sentence yielded no type check diagram.
  | Felicitous Result

-- | The semantic felicity check of one sentence.
data FelicityCheck = FelicityCheck {
  checkedRole :: String            -- ^ The role of the sentence checked
  , checkQuery :: U.TypeCheckQuery -- ^ The judgment built before the check
  , checkDiagram :: QT.DTTProofDiagram
  }

-- | Every query and diagram the inference builds, so that a caller can show them.
data Result = Result {
  answer :: TB.Answer
  -- ^ 'TB.Yes' if the premises prove the hypothesis, 'TB.No' if they refute it.
  , contxt :: DTT.Context
  -- ^ The context the felicity checks built.  Its head is the hypothesis and
  -- its tail is the premises, as in
  -- 'DTS.NaturalLanguageInference.sequentialTypeCheck'.
  , felicityChecks :: [FelicityCheck]
  -- ^ One per sentence, in the order the sentences are given.
  , positive :: (DTT.ProofSearchQuery, [QT.DTTProofDiagram])
  -- ^ The query which asks for the hypothesis, and the proofs found.
  , negative :: (DTT.ProofSearchQuery, [QT.DTTProofDiagram])
  -- ^ The query which asks for its negation, and the proofs found.
  }

-- | Checks the semantic felicity of each sentence in turn, and then asks the
-- prover whether the premises prove the hypothesis, and whether they refute it.
infer :: QT.Prover
         -> Int   -- ^ How many proof diagrams to keep (a negative value: all)
         -> Bool  -- ^ Whether to log the type checking
         -> Translation
         -> IO Verdict
infer prover nProof verbose translation = do
    checked <- felicityCheck [] (sentences translation)
    case checked of
      Left name -> return $ Infelicitous name
      Right checks -> case contextOf checks of
        [] -> return $ Infelicitous "(no sentence)"
        terms@(hypo:prems) -> do
          let psqPos = DTT.ProofSearchQuery sig prems hypo
              psqNeg = DTT.ProofSearchQuery sig prems $ DTT.Pi hypo DTT.Bot
          proofs <- takeNbest $ prover psqPos
          refutations <- takeNbest $ prover psqNeg
          return $ Felicitous Result {
              answer = answerOf proofs refutations
            , contxt = terms
            , felicityChecks = reverse checks
            , positive = (psqPos, proofs)
            , negative = (psqNeg, refutations)
            }
  where
    sig = signature translation
    takeNbest = ListT.toList . (if nProof >= 0 then ListT.take nProof else id)
    -- | The checks are accumulated in reverse, which is the order a context
    -- takes: the sentence checked last comes first.
    contextOf = map (DTT.trm . Tree.node . checkDiagram)
    answerOf proofs refutations
      | not (null proofs) = TB.Yes
      | not (null refutations) = TB.No
      | otherwise = TB.Unknown
    -- | Extends the context with the first type check diagram of each sentence.
    felicityCheck checks [] = return $ Right checks
    felicityCheck checks (sentence:rest) = do
      let query = U.Judgment sig (contextOf checks) (preterm sentence) DTT.Type
      diagrams <- ListT.uncons $ TY.typeCheck prover verbose query
      case diagrams of
        Nothing -> return $ Left $ role sentence
        Just (diagram, _) ->
          felicityCheck (FelicityCheck (role sentence) query diagram : checks) rest
