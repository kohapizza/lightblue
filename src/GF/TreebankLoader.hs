{-|
Copyright   : (c) Koharu Saeki, 2026
Licence     : All right reserved
Maintainer  : Koharu Saeki
Stability   : experimental

Loader for the FraCaS GF treebank (Ljunglöf and Siverbo 2011).

The treebank itself is distributed separately under GPL v3, so the files are
read from paths given by the caller:

* @src\/FraCaSBankI.gf@ of <https://github.com/heatherleaf/FraCaS-treebank>,
  which holds the language independent abstract syntax trees.
* @fracas.xml@ of Bill MacCartney, which holds the gold answers.
-}

module GF.TreebankLoader (
  -- * Problems
  Answer(..)
  , Problem(..)
  -- * Loading
  , loadFraCaS
  , loadTrees
  , loadAnswers
  -- * Sections
  , sectionOf
  ) where

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Char (isDigit)
import Data.List (sortOn)
import Data.Maybe (mapMaybe)
import qualified PGF
import qualified Text.XML as X
import Text.XML.Cursor (($//), (&|), attribute, element, fromDocument)

-- | The gold answer of a FraCaS problem.  @Undef@ marks the problems whose
-- answer the FraCaS report itself leaves open.
data Answer = Yes | No | Unknown | Undef deriving (Eq, Show)

-- | A FraCaS problem, with its sentences given as GF abstract syntax trees.
-- Four problems have no question, and one has no hypothesis.
data Problem = Problem {
  problemId :: Int                -- ^ 1 to 346
  , section :: Int                -- ^ 1 to 9, see 'sectionOf'
  , premises :: [PGF.Expr]        -- ^ In the order they appear in the problem
  , question :: Maybe PGF.Expr
  , hypothesis :: Maybe PGF.Expr
  , answer :: Maybe Answer
  }

-- | Loads the treebank and the gold answers, and pairs them up by problem id.
loadFraCaS :: FilePath          -- ^ Path of @FraCaSBankI.gf@
              -> FilePath       -- ^ Path of @fracas.xml@
              -> IO [Problem]
loadFraCaS treebankPath xmlPath = do
  trees <- loadTrees treebankPath
  answers <- loadAnswers xmlPath
  return $ assemble trees answers

-- | Reads the abstract syntax trees of @FraCaSBankI.gf@, keyed by the
-- identifiers of the treebank (e.g. @s_001_2_q@).
loadTrees :: FilePath -> IO (M.Map T.Text PGF.Expr)
loadTrees path = do
  txt <- T.readFile path
  let lins = M.fromList $ mapMaybe parseLin $ T.lines txt
  return $ M.mapMaybe (\body -> PGF.readExpr . T.unpack =<< dealias lins body) lins

-- | Reads the @fracas_answer@ attributes of @fracas.xml@.
loadAnswers :: FilePath -> IO (M.Map Int Answer)
loadAnswers path = do
  doc <- X.readFile X.def path
  let rows = fromDocument doc $// element "problem"
               &| \c -> (attribute "id" c, attribute "fracas_answer" c)
  return $ M.fromList [(i, a) | (ids, as) <- rows
                              , i <- mapMaybe (readInt . T.unpack) ids
                              , a <- mapMaybe toAnswer as]

-- | The section of the FraCaS test suite a problem belongs to.  The boundaries
-- are those of the section markers of @fracas.xml@.
sectionOf :: Int -> Int
sectionOf i
  | i < 81 = 1    -- generalized quantifiers
  | i < 114 = 2   -- plurals
  | i < 142 = 3   -- (nominal) anaphora
  | i < 197 = 4   -- ellipsis
  | i < 220 = 5   -- adjectives
  | i < 251 = 6   -- comparatives
  | i < 326 = 7   -- temporal reference
  | i < 334 = 8   -- verbs
  | otherwise = 9 -- attitudes

-- | Splits a line of the form @lin \<identifier\> = \<body\>;@.
parseLin :: T.Text -> Maybe (T.Text, T.Text)
parseLin line = do
  rest <- T.stripPrefix "lin " (T.strip line)
  let (key, body) = T.breakOn "=" rest
  body' <- T.stripPrefix "=" body
  return (T.strip key, T.strip (T.dropWhileEnd (== ';') (T.strip body')))

-- | Follows the definitions which are aliases of another entry, such as
-- @lin s_003_2_p = s_002_2_p;@.  Cyclic definitions yield 'Nothing'.
dealias :: M.Map T.Text T.Text -> T.Text -> Maybe T.Text
dealias lins = go (M.size lins)
  where go :: Int -> T.Text -> Maybe T.Text
        go n body
          | n < 0 = Nothing
          | otherwise = case M.lookup body lins of
                          Just body' -> go (n - 1) body'
                          Nothing -> Just body

-- | Collects the trees of each problem.  Identifiers are of the form
-- @s_\<problem\>_\<index\>_\<role\>@, the role being @p@, @q@ or @h@.
assemble :: M.Map T.Text PGF.Expr -> M.Map Int Answer -> [Problem]
assemble trees answers =
  [ Problem { problemId = i
            , section = sectionOf i
            , premises = [e | (_, "p", e) <- entries]
            , question = listToMaybe' [e | (_, "q", e) <- entries]
            , hypothesis = listToMaybe' [e | (_, "h", e) <- entries]
            , answer = M.lookup i answers
            }
  | (i, unsorted) <- M.toAscList grouped
  , let entries = sortOn (\(idx, _, _) -> idx) unsorted ]
  where
    grouped = M.fromListWith (++)
                [(i, [(idx, role, e)]) | (key, e) <- M.toList trees
                                       , Just (i, idx, role) <- [parseKey key]]
    listToMaybe' xs = case xs of
                        (x:_) -> Just x
                        [] -> Nothing

-- | Splits @s_001_2_q@ into the problem number, the index and the role.
-- The treebank leaves fourteen sentences unannotated as @variants{}@, six of
-- which are superseded by an entry with a @_NEW@ suffix.  Only the latter is
-- readable as a tree, so the two are not in conflict.
parseKey :: T.Text -> Maybe (Int, Int, T.Text)
parseKey key = case T.splitOn "_" key of
  ["s", num, idx, role] -> build num idx role
  ["s", num, idx, role, "NEW"] -> build num idx role
  _ -> Nothing
  where build num idx role = do
          i <- readInt (T.unpack num)
          j <- readInt (T.unpack idx)
          return (i, j, role)

readInt :: String -> Maybe Int
readInt s = if not (null s) && all isDigit s then Just (read s) else Nothing

toAnswer :: T.Text -> Maybe Answer
toAnswer a = case a of
  "yes" -> Just Yes
  "no" -> Just No
  "unknown" -> Just Unknown
  "undef" -> Just Undef
  _ -> Nothing
