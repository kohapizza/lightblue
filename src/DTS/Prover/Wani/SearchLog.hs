{-# LANGUAGE OverloadedStrings #-}
{-|
  Module      : DTS.Prover.Wani.SearchLog
  Description : Structured event logging for wani proof search visualization
-}
module DTS.Prover.Wani.SearchLog (
  -- * Event types
  SearchEventKind(..),
  SearchEvent(..),
  SearchOutcome(..),
  -- * Search log handle
  SearchLog(..),
  newSearchLog,
  recordEvent,
  recordEventWithIdx,
  recordGoalStart,
  recordEventForGoal,
  recordGoalEnd,
  getEvents,
  -- * Search tree construction
  SearchTreeNode(..),
  buildSearchTree,
  -- * Statistics
  RuleStats(..),
  computeRuleStats,
  -- * Failure analysis
  FailureInfo(..),
  analyzeFailures,
  -- * Flame graph data
  FlameNode(..),
  buildFlameGraph
) where

import Data.IORef
import qualified Data.Sequence as Seq
import Data.Sequence (Seq, (|>))
import qualified Data.Text.Lazy as T
import qualified Data.Time.Clock as Time
import qualified Data.Map.Strict as Map
import qualified Data.List as L
import Data.Aeson (ToJSON(..), object, (.=))

-- | Event kinds corresponding to debug log points in BackwardWithRules.hs
data SearchEventKind
  = EvGoalStart        -- ^ entering deduce' for a goal ("current goal")
  | EvGoalEnd          -- ^ leaving deduce' (with results or failure)
  | EvDepthExceeded    -- ^ depth > maxdepth guard
  | EvAvoidLoop        -- ^ failedlst match (loop avoidance)
  | EvTimeLimit        -- ^ time limit exceeded
  | EvRuleAttempt      -- ^ "with [rule], want to prove [subgoals]"
  | EvRuleReject       -- ^ rule was tried but not applicable (with exit reason)
  | EvRuleAccept       -- ^ rule was applicable and produced subgoals
  | EvRuleExit         -- ^ exitMessage (rule mismatch)
  | EvDeduced          -- ^ "deduced:" success
  | EvDeduceFailed     -- ^ "deduce failed"
  | EvGoalUpdate       -- ^ "update ... with clue"
  | EvIterDeepen       -- ^ "d=N / timeLimit" in iterative deepening
  | EvSpecialCase      -- ^ Bot/Top/Type/Kind special handling
  deriving (Show, Eq)

-- | A single structured event recorded during proof search
data SearchEvent = SearchEvent
  { evId        :: !Int
  , evKind      :: !SearchEventKind
  , evDepth     :: !Int
  , evTimestamp :: !Time.UTCTime
  , evGoalStr   :: !T.Text
  , evRuleName  :: !(Maybe T.Text)
  , evMessage   :: !T.Text
  , evGoalId    :: !Int           -- ^ unique ID of the deduce' call (= GoalStart evId)
  , evSubgoalIndex :: !(Maybe Int) -- ^ for GoalStart: index within parent SubGoalSet
  , evParentGoalId :: !(Maybe Int) -- ^ for GoalStart: goalId of the parent deduce' call
  , evSubgoalSetId :: !(Maybe Int) -- ^ for GoalStart: evId of the EvRuleAttempt that spawned it
  } deriving (Show)

-- | Handle for recording proof search events (IORef-based, thread-safe)
data SearchLog = SearchLog
  { slEvents  :: !(IORef (Seq SearchEvent))
  , slCounter :: !(IORef Int)
  }

-- | Create a new empty search log
newSearchLog :: IO SearchLog
newSearchLog = do
  events <- newIORef Seq.empty
  counter <- newIORef 0
  return $ SearchLog events counter

-- | Record an event. Returns the event ID. No-op if the SearchLog is Nothing.
recordEvent :: Maybe SearchLog -> SearchEventKind -> Int -> T.Text -> Maybe T.Text -> T.Text -> IO Int
recordEvent mLog kind depth goalStr ruleName message =
  recordEventWithIdx mLog kind depth goalStr ruleName message Nothing

-- | Record an event with subgoalIndex (for GoalStart). Returns the event ID.
recordEventWithIdx :: Maybe SearchLog -> SearchEventKind -> Int -> T.Text -> Maybe T.Text -> T.Text -> Maybe Int -> IO Int
recordEventWithIdx mLog kind depth goalStr ruleName message mIdx =
  recordGoalStart mLog kind depth goalStr ruleName message mIdx Nothing Nothing

-- | Record a GoalStart event with its explicit parent goalId and the
-- EvRuleAttempt (SubGoalSet) that spawned it, so the search tree can be
-- reconstructed exactly instead of via depth heuristics. Returns the event ID.
recordGoalStart :: Maybe SearchLog -> SearchEventKind -> Int -> T.Text -> Maybe T.Text -> T.Text -> Maybe Int -> Maybe Int -> Maybe Int -> IO Int
recordGoalStart Nothing _ _ _ _ _ _ _ _ = return (-1)
recordGoalStart (Just sl) kind depth goalStr ruleName message mIdx mParent mSubgoalSet = do
  ts <- Time.getCurrentTime
  eid <- atomicModifyIORef' (slCounter sl) (\n -> (n + 1, n))
  let ev = SearchEvent
        { evId = eid
        , evKind = kind
        , evDepth = depth
        , evTimestamp = ts
        , evGoalStr = goalStr
        , evRuleName = ruleName
        , evMessage = message
        , evGoalId = eid  -- for GoalStart, goalId = own id
        , evSubgoalIndex = mIdx
        , evParentGoalId = mParent
        , evSubgoalSetId = mSubgoalSet
        }
  atomicModifyIORef' (slEvents sl) (\s -> (s |> ev, ()))
  return eid

-- | Record an event associated with a specific goal (using its GoalStart ID).
recordEventForGoal :: Maybe SearchLog -> Int -> SearchEventKind -> Int -> T.Text -> Maybe T.Text -> T.Text -> IO ()
recordEventForGoal Nothing _ _ _ _ _ _ = return ()
recordEventForGoal (Just sl) goalStartId kind depth goalStr ruleName message = do
  ts <- Time.getCurrentTime
  eid <- atomicModifyIORef' (slCounter sl) (\n -> (n + 1, n))
  let ev = SearchEvent
        { evId = eid
        , evKind = kind
        , evDepth = depth
        , evTimestamp = ts
        , evGoalStr = goalStr
        , evRuleName = ruleName
        , evMessage = message
        , evGoalId = goalStartId
        , evSubgoalIndex = Nothing
        , evParentGoalId = Nothing
        , evSubgoalSetId = Nothing
        }
  atomicModifyIORef' (slEvents sl) (\s -> (s |> ev, ()))

-- | Record a GoalEnd event with the matching GoalStart's ID.
recordGoalEnd :: Maybe SearchLog -> Int -> Int -> T.Text -> T.Text -> IO ()
recordGoalEnd Nothing _ _ _ _ = return ()
recordGoalEnd (Just sl) goalStartId depth goalStr message = do
  ts <- Time.getCurrentTime
  eid <- atomicModifyIORef' (slCounter sl) (\n -> (n + 1, n))
  let ev = SearchEvent
        { evId = eid
        , evKind = EvGoalEnd
        , evDepth = depth
        , evTimestamp = ts
        , evGoalStr = goalStr
        , evRuleName = Nothing
        , evMessage = message
        , evGoalId = goalStartId  -- references the matching GoalStart
        , evSubgoalIndex = Nothing
        , evParentGoalId = Nothing
        , evSubgoalSetId = Nothing
        }
  atomicModifyIORef' (slEvents sl) (\s -> (s |> ev, ()))

-- | Retrieve all recorded events as a list
getEvents :: SearchLog -> IO [SearchEvent]
getEvents sl = do
  s <- readIORef (slEvents sl)
  return $ foldr (:) [] s

-- | Outcome of a search node
data SearchOutcome
  = OutcomeSuccess
  | OutcomeFail
  | OutcomeDepthExceeded
  | OutcomeLoopAvoided
  | OutcomeTimeLimitHit
  | OutcomePending
  deriving (Show, Eq)

-- | A rule trial result (accepted or rejected)
data RuleTrial = RuleTrial
  { rtRule    :: !T.Text
  , rtStatus  :: !T.Text   -- "accept" or "reject"
  , rtMessage :: !T.Text
  } deriving (Show)

-- | A node in the reconstructed search tree (for visualization)
data SearchTreeNode = SearchTreeNode
  { stnId         :: !Int
  , stnGoal       :: !T.Text
  , stnDepth      :: !Int
  , stnRule       :: !(Maybe T.Text)
  , stnOutcome    :: !SearchOutcome
  , stnDurationMs :: !(Maybe Double)
  , stnStartTime  :: !Time.UTCTime
  , stnEndTime    :: !(Maybe Time.UTCTime)
  , stnChildren   :: ![SearchTreeNode]
  , stnMessage    :: !T.Text
  , stnRuleTrials :: ![RuleTrial]  -- ^ rules tried in order (reject/accept)
  , stnSubgoalSetId :: !Int        -- ^ ID of the EvRuleAttempt that spawned this node (siblings with same ID are AND)
  , stnSubgoalIndex :: !(Maybe Int) -- ^ index within parent SubGoalSet (0-based)
  } deriving (Show)

-- | Build search tree from flat event list.
-- Uses goalId for GoalStart/GoalEnd matching and the explicitly recorded
-- parentGoalId / subgoalSetId for structure, so the reconstruction is exact
-- and does not depend on sequential (depth-monotone) event ordering.
buildSearchTree :: [SearchEvent] -> [SearchTreeNode]
buildSearchTree events =
  let goalStarts = filter (\e -> evKind e == EvGoalStart) events
      -- GoalEnd matched by goalId
      endMap :: Map.Map Int SearchEvent
      endMap = Map.fromList [(evGoalId e, e) | e <- events, evKind e == EvGoalEnd]
      -- Outcome events: use goalId for those after GoalStart, evId for standalone
      outcomeKinds = [EvDeduced, EvDeduceFailed, EvDepthExceeded, EvAvoidLoop, EvTimeLimit, EvSpecialCase]
      outcomeMap :: Map.Map Int [SearchEvent]
      outcomeMap = Map.fromListWith (++) [(evGoalId e, [e]) | e <- events, evKind e `elem` outcomeKinds]
      -- Parent-child from the explicitly recorded parent goalId
      childrenMap :: Map.Map Int [SearchEvent]
      childrenMap = Map.fromListWith (++)
        [(pid, [e]) | e <- goalStarts, Just pid <- [evParentGoalId e]]
      -- Rule trial events (reject/accept), attached to their goal via goalId
      trialMap :: Map.Map Int [SearchEvent]
      trialMap = Map.fromListWith (++)
        [(evGoalId e, [e]) | e <- events, evKind e `elem` [EvRuleReject, EvRuleAccept]]
      -- Build node
      buildNode :: SearchEvent -> SearchTreeNode
      buildNode startEv =
        let gid = evId startEv
            mEndEv = Map.lookup gid endMap
            children = map buildNode $ L.sortOn evId $ maybe [] id (Map.lookup gid childrenMap)
            outcomes = maybe [] id (Map.lookup gid outcomeMap)
            outcome = determineOutcome outcomes
            duration = case mEndEv of
              Just endEv' -> Just $ realToFrac (Time.diffUTCTime (evTimestamp endEv') (evTimestamp startEv)) * 1000
              Nothing    -> Nothing
            trials = [RuleTrial
                        (maybe "?" id (evRuleName e))
                        (if evKind e == EvRuleAccept then "accept" else "reject")
                        (evMessage e)
                     | e <- L.sortOn evId (maybe [] id (Map.lookup gid trialMap))]
            ssId = maybe (-1) id (evSubgoalSetId startEv)
        in SearchTreeNode
             { stnId = gid
             , stnGoal = evGoalStr startEv
             , stnDepth = evDepth startEv
             , stnRule = evRuleName startEv
             , stnOutcome = outcome
             , stnDurationMs = duration
             , stnStartTime = evTimestamp startEv
             , stnEndTime = fmap evTimestamp mEndEv
             , stnChildren = children
             , stnMessage = evMessage startEv
             , stnRuleTrials = trials
             , stnSubgoalSetId = ssId
             , stnSubgoalIndex = evSubgoalIndex startEv
             }
      roots = filter (\e -> evParentGoalId e == Nothing) goalStarts
  in map buildNode roots

-- | Determine outcome from outcome events for a specific goal
determineOutcome :: [SearchEvent] -> SearchOutcome
determineOutcome evts
  | any (\e -> evKind e == EvDeduced) evts = OutcomeSuccess
  | any (\e -> evKind e == EvDepthExceeded) evts = OutcomeDepthExceeded
  | any (\e -> evKind e == EvAvoidLoop) evts = OutcomeLoopAvoided
  | any (\e -> evKind e == EvTimeLimit) evts = OutcomeTimeLimitHit
  | any (\e -> evKind e == EvDeduceFailed) evts = OutcomeFail
  | otherwise = OutcomePending

-- | Rule statistics
data RuleStats = RuleStats
  { rsRule           :: !T.Text
  , rsAttempts       :: !Int
  , rsSuccesses      :: !Int
  , rsFailures       :: !Int
  , rsDepthExceeded  :: !Int
  , rsLoopAvoided    :: !Int
  , rsTimeLimitHit   :: !Int
  , rsPending        :: !Int
  , rsTotalMs        :: !Double
  } deriving (Show)

-- | Compute rule statistics from an already-built search tree
-- (consistent counting, no duplicate tree reconstruction)
computeRuleStats :: [SearchTreeNode] -> [RuleStats]
computeRuleStats treeNodes =
  let allNodes = concatMap flattenTree treeNodes
      -- Group all nodes by rule name
      ruleGroups = Map.fromListWith (++) [(r, [n]) | n <- allNodes, Just r <- [stnRule n]]
      countOutcome o ns = length $ filter (\n -> stnOutcome n == o) ns
  in map (\(rule, nodes) ->
      let attempts = length nodes
          totalMs = sum [maybe 0 id (stnDurationMs n) | n <- nodes]
      in RuleStats rule attempts
                   (countOutcome OutcomeSuccess nodes)
                   (countOutcome OutcomeFail nodes)
                   (countOutcome OutcomeDepthExceeded nodes)
                   (countOutcome OutcomeLoopAvoided nodes)
                   (countOutcome OutcomeTimeLimitHit nodes)
                   (countOutcome OutcomePending nodes)
                   totalMs
    ) (Map.toList ruleGroups)

-- | Flatten tree to list of all nodes
flattenTree :: SearchTreeNode -> [SearchTreeNode]
flattenTree n = n : concatMap flattenTree (stnChildren n)

-- | Failure analysis info
data FailureInfo = FailureInfo
  { fiCategory :: !T.Text
  , fiGoal     :: !T.Text
  , fiDepth    :: !Int
  , fiCount    :: !Int
  , fiEventId  :: !Int
  } deriving (Show)

-- | Analyze failure patterns from events
analyzeFailures :: [SearchEvent] -> [FailureInfo]
analyzeFailures events =
  let failures = filter (\e -> evKind e `elem` [EvDepthExceeded, EvAvoidLoop, EvTimeLimit, EvDeduceFailed]) events
      categorize e = case evKind e of
        EvDepthExceeded -> "depth_exceeded"
        EvAvoidLoop     -> "loop_avoided"
        EvTimeLimit     -> "time_limit"
        EvDeduceFailed  -> "deduce_failed"
        _               -> "unknown"
      grouped = Map.fromListWith (++)
        [(categorize e, [e]) | e <- failures]
      -- Group by (category, goal) for counting duplicates
      goalGrouped = Map.fromListWith (++)
        [((categorize e, evGoalStr e), [e]) | e <- failures]
  in map (\((cat, goal), es) ->
      FailureInfo cat goal (evDepth (head es)) (length es) (evId (head es))
    ) (Map.toList goalGrouped)

-- | Flame graph node (for D3 partition layout)
data FlameNode = FlameNode
  { fnName     :: !T.Text
  , fnValue    :: !Double    -- duration in ms
  , fnOutcome  :: !SearchOutcome
  , fnEventId  :: !Int
  , fnChildren :: ![FlameNode]
  } deriving (Show)

-- | Build flame graph data from search tree
buildFlameGraph :: [SearchTreeNode] -> FlameNode
buildFlameGraph roots =
  let totalMs = sum $ map (maybe 0 id . stnDurationMs) roots
      children = map treeToFlame roots
  in FlameNode "root" totalMs OutcomePending 0 children
  where
    treeToFlame :: SearchTreeNode -> FlameNode
    treeToFlame node = FlameNode
      { fnName = T.concat [maybe "" id (stnRule node), " d=", T.pack (show (stnDepth node))]
      , fnValue = maybe 0 id (stnDurationMs node)
      , fnOutcome = stnOutcome node
      , fnEventId = stnId node
      , fnChildren = map treeToFlame (stnChildren node)
      }

-- ToJSON instances

instance ToJSON SearchEventKind where
  toJSON kind = toJSON $ case kind of
    EvGoalStart     -> "goal_start" :: T.Text
    EvGoalEnd       -> "goal_end"
    EvDepthExceeded -> "depth_exceeded"
    EvAvoidLoop     -> "avoid_loop"
    EvTimeLimit     -> "time_limit"
    EvRuleAttempt   -> "rule_attempt"
    EvRuleReject    -> "rule_reject"
    EvRuleAccept    -> "rule_accept"
    EvRuleExit      -> "rule_exit"
    EvDeduced       -> "deduced"
    EvDeduceFailed  -> "deduce_failed"
    EvGoalUpdate    -> "goal_update"
    EvIterDeepen    -> "iter_deepen"
    EvSpecialCase   -> "special_case"

instance ToJSON SearchOutcome where
  toJSON outcome = toJSON $ case outcome of
    OutcomeSuccess       -> "success" :: T.Text
    OutcomeFail          -> "fail"
    OutcomeDepthExceeded -> "depth_exceeded"
    OutcomeLoopAvoided   -> "loop_avoided"
    OutcomeTimeLimitHit  -> "time_limit"
    OutcomePending       -> "pending"

instance ToJSON SearchEvent where
  toJSON e = object
    [ "id"        .= evId e
    , "kind"      .= evKind e
    , "depth"     .= evDepth e
    , "timestamp" .= (realToFrac (Time.utctDayTime (evTimestamp e)) :: Double)
    , "goal"      .= evGoalStr e
    , "rule"      .= evRuleName e
    , "message"   .= evMessage e
    , "goalId"    .= evGoalId e
    , "parentGoalId" .= evParentGoalId e
    , "subgoalSetId" .= evSubgoalSetId e
    ]

instance ToJSON SearchTreeNode where
  toJSON n = object
    [ "id"         .= stnId n
    , "goal"       .= stnGoal n
    , "depth"      .= stnDepth n
    , "rule"       .= stnRule n
    , "outcome"    .= stnOutcome n
    , "durationMs" .= stnDurationMs n
    , "startTime"  .= (realToFrac (Time.utctDayTime (stnStartTime n)) :: Double)
    , "endTime"    .= fmap (\t -> realToFrac (Time.utctDayTime t) :: Double) (stnEndTime n)
    , "children"   .= stnChildren n
    , "message"    .= stnMessage n
    , "ruleTrials" .= stnRuleTrials n
    , "subgoalSetId" .= stnSubgoalSetId n
    , "subgoalIndex" .= stnSubgoalIndex n
    ]

instance ToJSON RuleTrial where
  toJSON rt = object
    [ "rule"    .= rtRule rt
    , "status"  .= rtStatus rt
    , "message" .= rtMessage rt
    ]

instance ToJSON RuleStats where
  toJSON s = object
    [ "rule"           .= rsRule s
    , "attempts"       .= rsAttempts s
    , "successes"      .= rsSuccesses s
    , "failures"       .= rsFailures s
    , "depthExceeded"  .= rsDepthExceeded s
    , "loopAvoided"    .= rsLoopAvoided s
    , "timeLimitHit"   .= rsTimeLimitHit s
    , "pending"        .= rsPending s
    , "totalMs"        .= rsTotalMs s
    , "avgMs"          .= if rsAttempts s > 0 then rsTotalMs s / fromIntegral (rsAttempts s) else (0 :: Double)
    , "rate"           .= if rsAttempts s > 0 then fromIntegral (rsSuccesses s) / fromIntegral (rsAttempts s) :: Double else (0 :: Double)
    ]

instance ToJSON FailureInfo where
  toJSON f = object
    [ "category" .= fiCategory f
    , "goal"     .= fiGoal f
    , "depth"    .= fiDepth f
    , "count"    .= fiCount f
    , "eventId"  .= fiEventId f
    ]

instance ToJSON FlameNode where
  toJSON n = object
    [ "name"     .= fnName n
    , "value"    .= fnValue n
    , "outcome"  .= fnOutcome n
    , "eventId"  .= fnEventId n
    , "children" .= fnChildren n
    ]
