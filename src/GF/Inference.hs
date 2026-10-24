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

import qualified Data.List as L           --base
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
  -- 'DTS.NaturalLanguageInference.sequentialTypeCheck', with any
  -- accommodated presuppositions below the premise which called for them.
  , felicityChecks :: [FelicityCheck]
  -- ^ One per sentence, in the order the sentences are given.
  , accommodations :: [(String, [DTT.Preterm])]
  -- ^ The premises whose felicity check succeeded only after their
  -- presuppositions were added to the context, with the types added.
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
    checked <- felicityCheck [] [] [] (sentences translation)
    case checked of
      Left name -> return $ Infelicitous name
      Right (ctx, accs, checks) -> case ctx of
        [] -> return $ Infelicitous "(no sentence)"
        terms@(hypo:prems) -> do
          let psqPos = DTT.ProofSearchQuery sig prems hypo
              psqNeg = DTT.ProofSearchQuery sig prems $ DTT.Pi hypo DTT.Bot
          proofs <- takeNbest $ prover psqPos
          refutations <- takeNbest $ prover psqNeg
          return $ Felicitous Result {
              answer = answerOf proofs refutations
            , contxt = terms
            , felicityChecks = checks
            , accommodations = accs
            , positive = (psqPos, proofs)
            , negative = (psqNeg, refutations)
            }
  where
    sig = signature translation
    takeNbest = ListT.toList . (if nProof >= 0 then ListT.take nProof else id)
    typeOf = DTT.trm . Tree.node . checkDiagram
    answerOf proofs refutations
      | not (null proofs) = TB.Yes
      | not (null refutations) = TB.No
      | otherwise = TB.Unknown
    -- | Checks each sentence in the context the previous ones built (the
    -- sentence checked last comes first).  Underspecified terms resolve
    -- against that context during the check; when the check of a premise
    -- fails, its closed presuppositions are accommodated: added to the
    -- context, and the check is run once more.  The hypothesis is never
    -- accommodated, since an assumption added for its own presupposition
    -- could feed the proof of the hypothesis itself.
    felicityCheck ctx accs checks [] = return $ Right (ctx, reverse accs, reverse checks)
    felicityCheck ctx accs checks (sentence:rest) = do
      first <- runCheck ctx sentence
      case first of
        Just check -> felicityCheck (typeOf check : ctx) accs (check : checks) rest
        Nothing
          | role sentence /= "Hypothesis"
          , presups@(_:_) <- closedPresuppositions (preterm sentence) -> do
              let ctx' = presups ++ ctx
              retry <- runCheck ctx' sentence
              case retry of
                Just check -> felicityCheck (typeOf check : ctx')
                                            ((role sentence, presups) : accs)
                                            (check : checks) rest
                Nothing -> return $ Left $ role sentence
          | otherwise -> return $ Left $ role sentence
    runCheck ctx sentence = do
      let query = U.Judgment sig ctx (preterm sentence) DTT.Type
      diagrams <- ListT.uncons $ TY.typeCheck prover verbose query
      return $ fmap (FelicityCheck (role sentence) query . fst) diagrams

-- | The types of the underspecified terms of a sentence which do not depend on
-- any variable bound around them.  Only those can be accommodated globally: a
-- presupposition under a binder would escape it.  A type which another
-- underspecified term lies within is left out, since it cannot be stated
-- before that inner term is resolved.
closedPresuppositions :: U.Preterm -> [DTT.Preterm]
closedPresuppositions = L.nub . collect
  where
    collect term = case term of
      U.Asp t -> [t' | closed 0 t, Just t' <- [U.toDTT t]] ++ collect t
      U.Pi a b -> collect a ++ collect b
      U.Lam m -> collect m
      U.App m n -> collect m ++ collect n
      U.Not m -> collect m
      U.Sigma a b -> collect a ++ collect b
      U.Pair m n -> collect m ++ collect n
      U.Proj _ m -> collect m
      U.Disj a b -> collect a ++ collect b
      U.Iota _ m -> collect m
      U.Unpack p l m n -> concatMap collect [p, l, m, n]
      U.Succ m -> collect m
      U.Natrec p l m n -> concatMap collect [p, l, m, n]
      U.Eq a m n -> concatMap collect [a, m, n]
      U.Refl a m -> collect a ++ collect m
      U.Idpeel p l m -> concatMap collect [p, l, m]
      U.Lamvec m -> collect m
      U.Appvec _ m -> collect m
      U.Ann m _ -> collect m
      _ -> []
    -- | Whether no variable of the term escapes it, counting the binders of
    -- the fragment ('Pi', 'Lam', 'Sigma' and 'Lamvec' bind one variable).
    closed d term = case term of
      U.Var i -> i < d
      U.Pi a b -> closed d a && closed (d + 1) b
      U.Lam m -> closed (d + 1) m
      U.App m n -> closed d m && closed d n
      U.Not m -> closed d m
      U.Sigma a b -> closed d a && closed (d + 1) b
      U.Pair m n -> closed d m && closed d n
      U.Proj _ m -> closed d m
      U.Disj a b -> closed d a && closed d b
      U.Iota _ m -> closed d m
      U.Unpack p l m n -> all (closed d) [p, l, m, n]
      U.Succ m -> closed d m
      U.Natrec p l m n -> all (closed d) [p, l, m, n]
      U.Eq a m n -> all (closed d) [a, m, n]
      U.Refl a m -> closed d a && closed d m
      U.Idpeel p l m -> all (closed d) [p, l, m]
      U.Asp m -> closed d m
      U.Lamvec m -> closed (d + 1) m
      U.Appvec i m -> i < d && closed d m
      U.Ann m _ -> closed d m
      _ -> True
