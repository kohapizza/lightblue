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
  -- * Felicity checks
  , FelicityCheck(..)
  , Discourse(..)
  , Branch(..)
  , discourse
  -- * Inference
  , Verdict(..)
  , Result(..)
  , paths
  , verdictOf
  , inferAll
  , infer
  ) where

import Control.Monad.IO.Class (liftIO)    --base
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

-- | The semantic felicity check of one sentence.
data FelicityCheck = FelicityCheck {
  checkedRole :: String            -- ^ The role of the sentence checked
  , checkQuery :: U.TypeCheckQuery -- ^ The judgment built before the check
  , checkDiagram :: QT.DTTProofDiagram
  }

-- | The felicity checks of a discourse as a tree, as
-- 'DTS.NaturalLanguageInference.ParseResult' without the level of parse
-- trees, since the treebank gives one tree per sentence.  Each result of the
-- check of a sentence is a branch, and becomes the context of the rest of the
-- discourse on that branch.  The branches are computed only when a caller
-- walks them.
data Discourse =
  Next Sentence (ListT.ListT IO Branch)
  -- ^ The next sentence, and the results of its felicity check.
  | Final DTT.ProofSearchQuery DTT.ProofSearchQuery
  -- ^ The queries which ask for the hypothesis and for its negation.
  | NoSentence

-- | One result of the felicity check of a sentence.
data Branch = Branch {
  branchCheck :: FelicityCheck
  , branchAccommodated :: [DTT.Preterm]
  -- ^ The presuppositions added to the context for this result, if any.
  , branchRest :: Discourse
  -- ^ The rest of the discourse, in the context this result extends.
  }

-- | Checks each sentence in the context the previous ones built (the sentence
-- checked last comes first), keeping up to the given number of results per
-- sentence (a negative value: all).  Underspecified terms resolve against that
-- context during the check.  When the check of a sentence yields no result on
-- a branch, its closed presuppositions are accommodated on that branch: added
-- to the context, and the check is run once more.  The hypothesis is no
-- exception, as in 'DTS.NaturalLanguageInference.sequentialTypeCheck', where
-- every sentence is just the next sentence of the discourse: accommodating a
-- presupposition supplies an entity, not the assertion about it, so the
-- hypothesis does not become provable by its own presupposition (the
-- accommodation is still recorded, so that an evaluation can report it).
discourse :: QT.Prover
             -> Int   -- ^ How many type check results to keep per sentence
             -> Bool  -- ^ Whether to log the type checking
             -> DTT.Signature
             -> DTT.Context
             -> [Sentence]
             -> Discourse
discourse _ _ _ sig ctx [] = case ctx of
  [] -> NoSentence
  (hypo:prems) -> Final (DTT.ProofSearchQuery sig prems hypo)
                        (DTT.ProofSearchQuery sig prems $ DTT.Pi hypo DTT.Bot)
discourse prover nTypeCheck verbose sig ctx (sentence:rest) =
  Next sentence $ do
    (presups, ctx', check) <- candidates
    let ctx'' = DTT.trm (Tree.node (checkDiagram check)) : ctx'
    return $ Branch check presups (discourse prover nTypeCheck verbose sig ctx'' rest)
  where
    candidates = do
      first <- liftIO $ ListT.uncons $ checksIn ctx
      case first of
        Just (check, more) -> fmap (\c -> ([], ctx, c)) $ ListT.cons check more
        Nothing -> case closedPresuppositions (preterm sentence) of
          [] -> ListT.fromFoldable []
          presups -> let ctx' = presups ++ ctx
                     in fmap (\c -> (presups, ctx', c)) $ checksIn ctx'
    checksIn c =
      let query = U.Judgment sig c (preterm sentence) DTT.Type
      in fmap (FelicityCheck (role sentence) query)
              $ takeNbest nTypeCheck $ TY.typeCheck prover verbose query

-- | The outcome of running a problem.
data Verdict =
  Infelicitous String  -- ^ The named sentence yielded no type check diagram.
  | Felicitous Result

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
  -- ^ The sentences whose felicity check succeeded only after their
  -- presuppositions were added to the context, with the types added.
  , positive :: (DTT.ProofSearchQuery, [QT.DTTProofDiagram])
  -- ^ The query which asks for the hypothesis, and the proofs found.
  , negative :: (DTT.ProofSearchQuery, [QT.DTTProofDiagram])
  -- ^ The query which asks for its negation, and the proofs found.
  }

-- | Walks the tree depth first, and asks the prover at the end of each path.
-- A path on which a sentence yields no result ends with the role of that
-- sentence.
paths :: QT.Prover
         -> Int   -- ^ How many proof diagrams to keep (a negative value: all)
         -> Discourse
         -> ListT.ListT IO (Either String Result)
paths prover nProof = go [] []
  where
    go _ _ NoSentence = ListT.fromFoldable [Left "(no sentence)"]
    go checks accs (Next sentence branches) = do
      first <- liftIO $ ListT.uncons branches
      case first of
        Nothing -> return $ Left $ role sentence
        Just (branch, more) -> do
          Branch check presups rest <- ListT.cons branch more
          let accs' = if null presups then accs else (role sentence, presups) : accs
          go (check : checks) accs' rest
    go checks accs (Final psqPos psqNeg@(DTT.ProofSearchQuery _ prems _)) = liftIO $ do
      proofs <- ListT.toList $ takeNbest nProof $ prover psqPos
      refutations <- ListT.toList $ takeNbest nProof $ prover psqNeg
      let DTT.ProofSearchQuery _ _ hypo = psqPos
      return $ Right Result {
          answer = answerOf proofs refutations
        , contxt = hypo : prems
        , felicityChecks = reverse checks
        , accommodations = reverse accs
        , positive = (psqPos, proofs)
        , negative = (psqNeg, refutations)
        }
    answerOf proofs refutations
      | not (null proofs) = TB.Yes
      | not (null refutations) = TB.No
      | otherwise = TB.Unknown

-- | The verdict of a problem from the outcomes of its paths: the first path
-- which reaches the prover, as 'DTS.NaturalLanguageInference.trawlParseResult'
-- skips the paths which end in a failed check, or else the sentence at which
-- the first path ended.
verdictOf :: [Either String Result] -> Verdict
verdictOf outcomes = case [r | Right r <- outcomes] of
  (r:_) -> Felicitous r
  [] -> Infelicitous $ case outcomes of
          (Left name:_) -> name
          _ -> "(no sentence)"

-- | Runs every path of a problem.  The paths are computed once, so that a
-- caller can show them and count their labels without running the prover
-- again.
inferAll :: QT.Prover
            -> Int   -- ^ How many type check results to keep per sentence
            -> Int   -- ^ How many proof diagrams to keep
            -> Bool  -- ^ Whether to log the type checking
            -> Translation
            -> IO [Either String Result]
inferAll prover nTypeCheck nProof verbose translation =
  ListT.toList $ paths prover nProof
               $ discourse prover nTypeCheck verbose (signature translation) []
               $ sentences translation

-- | Checks the semantic felicity of each sentence in turn, and then asks the
-- prover whether the premises prove the hypothesis, and whether they refute it.
infer :: QT.Prover
         -> Int   -- ^ How many type check results to keep per sentence
         -> Int   -- ^ How many proof diagrams to keep
         -> Bool  -- ^ Whether to log the type checking
         -> Translation
         -> IO Verdict
infer prover nTypeCheck nProof verbose translation =
  verdictOf <$> inferAll prover nTypeCheck nProof verbose translation

-- | Takes n elements from the top of the list (a negative n: all of them).
takeNbest :: Int -> ListT.ListT IO a -> ListT.ListT IO a
takeNbest n = if n >= 0 then ListT.take n else id

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
