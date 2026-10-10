{-# OPTIONS -Wall #-}
{-# LANGUAGE OverloadedStrings, RecordWildCards #-}

import Options.Applicative hiding (style) --optparse-applicative
import Control.Applicative (optional,(<|>)) --base
import Control.Monad (forM,forM_)         --base
import Control.Exception (catch,IOException) --base
import Data.Char (toLower)
import System.Exit (exitFailure)          --base
import System.Info (os)                   --base
import System.Process (callCommand)       --process
import ListT (toList)                     --list-t
import qualified Data.Text.Lazy as T      --text
import qualified Data.Text.Lazy.IO as T   --text
import qualified Data.Text as StrictT     --text
import qualified Data.Text.IO as StrictT  --text
import Data.Ratio ((%))                   --base
import qualified Data.List as L           --base
import qualified Data.Fixed as F          --base
import qualified System.IO as S           --base
import qualified System.Environment as E -- base
import qualified Data.Map as M            --container
import qualified Data.Time as Time        --time
import qualified Parser.ChartParser as CP
import qualified Parser.PartialParsing as CP
import qualified Parser.Language.Japanese.Lexicon as JLEX
import qualified Parser.Language.Japanese.MyLexicon as JLEX
import qualified Parser.Language.Japanese.Juman.CallJuman as Juman
import qualified Parser.Language.Japanese.Filter as JFilter
import Parser.Language.Japanese.Filter.KNPFilter (knpFilter)    --lightblue
import Parser.Language.Japanese.Filter.KWJAFilter (kwjaFilter)  --lightblue
import qualified Parser.Language.English.Lexicon as ELEX
import Parser.Language (LangOptions(..))
import Parser.LangOptions (defaultJpOptions,defaultEnOptions)
import qualified Interface as I
import qualified System.Environment as Env
import qualified Interface.Text as T
import qualified Interface.HTML as I
import qualified Interface.PrintParseResult as PPR
import qualified Interface.Express.Express as Express
import qualified JSeM as J
import qualified JSeM.XML as J
import qualified DTS.UDTTdeBruijn as UDTT
import qualified DTS.UDTTwithName as UDTTwN
import qualified DTS.DTTdeBruijn as DTT
import qualified DTS.DTTwithName as DTTwN
import DTS.TypeChecker (typeCheck,typeInfer,nullProver)
import qualified DTS.QueryTypes as QT
import qualified DTS.NaturalLanguageInference as NLI
import qualified JSeM as JSeM                         --jsem
import qualified ML.Exp.Classification.Bounded as NLP --nlp-tools
import qualified PGF                                  --gf
import qualified GF.TreebankLoader as GFTB            --lightblue
import qualified GF.Inference as GFI                  --lightblue

data Options = Options Lang Command I.Style NLI.ProverName FilePath Int Int Int Int Int Int Bool Bool Bool Bool (Maybe Int) Bool Bool Bool (Maybe ExpressBrowser) (Maybe LexicalPos)

data Command =
  Parse I.ParseOutput
  | JSeM String Int
  | Numeration 
  | Demo
  | Version
  | Stat
  | Test
    deriving (Show, Eq)

data Lang = JP Juman.MorphAnalyzerName JFilter.FilterName | EN deriving (Show, Eq)

-- | The lightblue command is either an inference over the FraCaS GF treebank,
-- which needs no morphological analyzer and no input text, or one of the
-- commands which parse a text in a natural language.
data Invocation = RunGF GFOptions | RunStandard Options

-- | Local options of the gf command.
data GFOptions = GFOptions {
  gfTreebank :: FilePath        -- ^ Path of FraCaSBankI.gf
  , gfAnswers :: FilePath       -- ^ Path of fracas.xml
  , gfProblem :: Int            -- ^ The number of the problem to run
  , gfStyle :: I.Style
  , gfOutput :: FilePath        -- ^ Where to write, or stdout when empty
  , gfOpen :: Bool              -- ^ Whether to open the result in a browser
  , gfProverName :: NLI.ProverName
  , gfNProof :: Int
  , gfMaxDepth :: Int
  , gfMaxTime :: Int
  , gfNoDiagram :: Bool
  , gfVerbose :: Bool
  }

-- | Browser selection for Express mode
data ExpressBrowser = BrowserDefault | BrowserChrome | BrowserFirefox
  deriving (Show, Eq)

-- | Lexical Items position for Express
data LexicalPos = LexTop | LexBottom | LexNone
  deriving (Show, Eq)

lexicalPosReader :: ReadM LexicalPos
lexicalPosReader = eitherReader $ \s ->
  case map toLower s of
    "top"    -> Right LexTop
    "bottom" -> Right LexBottom
    "none"   -> Right LexNone
    _        -> Left "Expected one of: top|bottom|none"

expressBrowserReader :: ReadM ExpressBrowser
expressBrowserReader = eitherReader $ \s ->
  case map toLower s of
    "default" -> Right BrowserDefault
    "chrome"  -> Right BrowserChrome
    "firefox" -> Right BrowserFirefox
    _         -> Left "Expected one of: default|chrome|firefox"

-- <$> :: (a -> b) -> Parser a -> Parser b
-- <*> :: Parser (a -> b) -> Parser a -> Parser b

jpParser :: Parser Lang
jpParser = JP
  <$> option auto
    ( long "ma"
      <> short 'm' 
      <> metavar "juman|jumanpp|kwja"
      <> value Juman.KWJA
      <> help "Specify morphological analyzer (default: KWJA)" )
  <*> option auto
    ( long "filter"
      <> metavar "knp|kwja|none"
      <> value JFilter.NONE
      <> help "Specify node filter (default: NONE)" )

enParser :: Parser Lang
enParser = pure EN

--commandReader :: String -> a -> String -> [(a,String)]
--commandReader r command option = [(command,s) | (x,s) <- lex r, map C.toLower x == option]

optionParser :: Parser Options
optionParser = 
  -- flag' Version ( long "version" 
  --               <> short 'v' 
  --               <> hidden
  --               <> help "Print the lightblue version" )
  -- <|> 
  -- flag' Stat ( long "stat"
  --            <> hidden 
  --            <> help "Print the lightblue statistics" )
  -- <|> 
  -- flag' Test ( long "test"
  --            <> hidden 
  --            <> internal
  --            <> help "Execute the test code" )
  -- <|> 
  Options
    <$> subparser
      (command "jp"
           (info jpParser
                 (progDesc "Local options: [-m juman|jumanpp|kwja] [--filter knp|kwja|none] (The default values: -m kwja --filter none" ))
      <> command "en"
           (info enParser
                 (progDesc "No local options" ))
      )
    <*> subparser 
      (command "parse"
           (info parseOptionParser
                 (progDesc "Local options: [-o|--output tree|postag] (The default values: -o tree)" ))
      <> command "jsem"
           (info jsemOptionParser
                 (progDesc "Local options: [--jsemid <int>] [--nSample <int>] (The default values:)" ))
      <> command "numeration"
           (info (pure Numeration)
                 (progDesc "Shows all the lexical items in each of the numeration for the inupt sentences." ))
      <> command "demo"
           (info (pure Demo)
                 (progDesc "Sequentially shows parsing results of a given corpus. No local options." ))
      <> command "version"
           (info (pure Version)
                 (progDesc "Print the lightblue version." ))
      <> command "stat"
           (info (pure Stat)
                 (progDesc "Print the lightblue statistics." ))
      <> command "test"
           (info (pure Test)
                 (progDesc "Execute the test code." ))
      -- <> command "debug"
      --      (info debugOptionParser
      --            (progDesc "shows all the parsing results between the two pivots. Local options: INT INT (No default values)" ))
      <> metavar "COMMAND (=parse|jsem|numeration|demo|version|stat)"
      <> commandGroup "Available COMMANDs and thier local options"
      <> help "specifies the task to execute.  See 'Available COMMANDs ...' below about local options for each command"
      )
    <*> option auto
      ( long "style"
      <> short 's'
      <> metavar "text|tex|xml|html|express"
      <> help "Print results in the specified format"
      <> showDefault
      <> value I.HTML )
    <*> option auto
      ( long "prover"
      <> short 'p'
      <> metavar "Wani|Null"
      <> showDefault
      <> value NLI.Wani
      <> help "Choose prover" )
    <*> strOption 
      ( long "file"
      <> short 'f'
      <> metavar "FILEPATH"
      <> help "Reads input texts from FILEPATH (Specify '-' to use stdin)"
      <> showDefault
      <> value "-" )
    <*> option auto 
      ( long "beam"
      <> short 'b'
      <> help "Specify the beam width"
      <> showDefault
      <> value 32
      <> metavar "INT" )
    <*> option auto 
      ( long "nparse"
      -- <> short 'n'
      <> help "Show N-best parse trees for each sentence"
      <> showDefault
      <> value 1
      <> metavar "INT" )
    <*> option auto 
      ( long "ntypecheck"
      -- <> short 'n'
      <> help "Show N-best type check diagram for each logical form"
      <> showDefault
      <> value 1
      <> metavar "INT" )
    <*> option auto 
      ( long "nproof"
      -- <> short 'n'
      <> help "Show N-best proof diagram for each proof search"
      <> showDefault
      <> value (-1)
      <> metavar "INT" )
    <*> option auto 
      ( long "maxdepth"
      <> help "Set the maximum search depth in proof search"
      <> showDefault
      <> value 5
      <> metavar "INT" )
    <*> option auto 
      ( long "maxtime"
      <> help "Set the maximum search time in proof search"
      <> showDefault
      <> value 100000
      <> metavar "INT" )
    <*> switch 
      ( long "noTypeCheck"
      <> help "If True, execute no type checking for LFs" )
    <*> switch 
      ( long "noInference"
      <> help "If true, execute no inference" )
    <*> switch 
      ( long "time"
      <> help "Show the execution time in stderr" )
    <*> switch 
      ( long "verbose"
      <> help "Show logs of type inferer and type checker" )
    <*> optional (option auto
      ( long "depth"
      <> metavar "INT"
      <> help "Set the expand depth for Express view" ))
    <*> switch
      ( long "noShowCat"
      <> help "If True, hide categories in Express view" )
    <*> switch
      ( long "noShowSem"
      <> help "If True, hide semantics in Express view" )
    <*> switch
      ( long "leafVertical"
      <> help "If True, list lexical items vertically in Express view" )
    <*> optional (option expressBrowserReader
      ( long "browser"
      <> metavar "chrome|firefox|default"
      <> help "Choose browser for Express view (default: system default)" ))
    <*> optional (option lexicalPosReader
      ( long "lexicalPos"
      <> metavar "top|bottom|none"
      <> help "Set Lexical Items position in Express view" ))

parseOptionParser :: Parser Command
parseOptionParser = Parse
  <$> option auto
    ( long "output"
    <> short 'o'
    <> metavar "tree|postag"
    <> help "Specify the output content"
    <> showDefault
    <> value I.TREE )

gfOptionParser :: Parser GFOptions
gfOptionParser = GFOptions
  <$> strOption
    ( long "treebank"
    <> metavar "FILEPATH"
    <> value ""
    <> help "Path of FraCaSBankI.gf (default: the value of $FRACAS_TREEBANK)" )
  <*> strOption
    ( long "answers"
    <> metavar "FILEPATH"
    <> value ""
    <> help "Path of fracas.xml (default: the value of $FRACAS_XML)" )
  <*> option auto
    ( long "problem"
    <> metavar "INT"
    <> help "The number of the FraCaS problem to run" )
  <*> option auto
    ( long "style"
    <> short 's'
    <> metavar "text|html"
    <> showDefault
    <> value I.TEXT
    <> help "Print results in the specified format" )
  <*> strOption
    ( long "output"
    <> short 'o'
    <> metavar "FILEPATH"
    <> value ""
    <> help "Write results to FILEPATH instead of stdout" )
  <*> switch
    ( long "open"
    <> help "Write an html file and open it in a browser (implies -s html)" )
  <*> option auto
    ( long "prover"
    <> short 'p'
    <> metavar "Wani|Null"
    <> showDefault
    <> value NLI.Wani
    <> help "Choose prover" )
  <*> option auto
    ( long "nproof"
    <> showDefault
    <> value 1
    <> metavar "INT"
    <> help "Show N-best proof diagram for each proof search" )
  <*> option auto
    ( long "maxdepth"
    <> showDefault
    <> value 5
    <> metavar "INT"
    <> help "Set the maximum search depth in proof search" )
  <*> option auto
    ( long "maxtime"
    <> showDefault
    <> value 100000
    <> metavar "INT"
    <> help "Set the maximum search time in proof search" )
  <*> switch
    ( long "noDiagram"
    <> help "If specified, show no type check and proof diagram" )
  <*> switch
    ( long "verbose"
    <> help "Show logs of type inferer and type checker" )

jsemOptionParser :: Parser Command
jsemOptionParser = JSeM
  <$> strOption
    ( long "jsemid"
      <> metavar "STRING"
      <> showDefault
      <> value "all"
      <> help "Skip JSeM data the JSeM ID of which is not equial to this value")
  <*> option auto
    ( long "nsample"
      <> showDefault
      <> value (-1)
      <> metavar "INT"
      <> help "How many data to process")

-- debugOptionParser :: Parser Command
-- debugOptionParser = Debug
--   <$> argument auto idm
--   <*> argument auto idm

-- | Main function.  Check README.md for the usage.
main :: IO ()
main = customExecParser p opts >>= run
  where opts = info (helper <*> invocationParser)
                 ( fullDesc
                 <> progDesc "Usage: lightblue LANG COMMAND <local options> <global options>, or lightblue gf <local options>"
                 <> header "lightblue - a CCG parser with DTS (c) Daisuke Bekki and Bekki Laboratory" )
        p = prefs showHelpOnEmpty
        run (RunGF gfOptions) = gfMain gfOptions
        run (RunStandard options) = lightblueMain options

invocationParser :: Parser Invocation
invocationParser =
  (RunGF <$> subparser
    (command "gf"
       (info (helper <*> gfOptionParser)
             (progDesc "Runs an inference of the FraCaS GF treebank.  Needs no morphological analyzer." ))
    <> metavar "gf"
    <> commandGroup "Inference over the FraCaS GF treebank"))
  <|> (RunStandard <$> optionParser)

-- | Renders a result of the gf command.  Only text and html are supported,
-- since the remaining styles have no notation for a proof diagram.
gfPrinter :: (T.SimpleText a, I.MathML a) => I.Style -> a -> T.Text
gfPrinter I.HTML obj = T.concat [I.startMathML, I.toMathML obj, I.endMathML]
gfPrinter _ obj = T.toText obj

-- | Renders an abstract syntax tree over several lines, so that the structure
-- can be read off the indentation.  A subtree which fits on one line is kept
-- on one line, since a leaf on a line of its own only adds noise.
showTree :: Int -> PGF.Expr -> String
showTree indent expr
  | length flat <= 64 = flat
  | otherwise = case PGF.unApp expr of
      Just (fun, args@(_:_)) ->
        "(" ++ PGF.showCId fun
            ++ concatMap (\arg -> "\n" ++ pad ++ showTree (indent+2) arg) args ++ ")"
      _ -> flat
  where
    -- | An application needs the parentheses which showExpr omits at the top.
    flat = case PGF.unApp expr of
             Just (_, []) -> PGF.showExpr [] expr
             _ -> "(" ++ PGF.showExpr [] expr ++ ")"
    pad = replicate (indent+2) ' '

-- | Escapes the characters which would be markup in an html page.
escapeHtml :: String -> String
escapeHtml = concatMap $ \c -> case c of
  '&' -> "&amp;"
  '<' -> "&lt;"
  '>' -> "&gt;"
  _ -> [c]

-- | Runs one problem of the FraCaS GF treebank.
gfMain :: GFOptions -> IO ()
gfMain GFOptions{..} = do
  treebankPath <- resolvePath "FRACAS_TREEBANK" "--treebank" gfTreebank
  answersPath <- resolvePath "FRACAS_XML" "--answers" gfAnswers
  problems <- GFTB.loadFraCaS treebankPath answersPath
  case L.find ((== gfProblem) . GFTB.problemId) problems of
    Nothing -> abort $ "No FraCaS problem is numbered " ++ show gfProblem
    Just problem -> case GFI.translateProblem problem of
      Left err -> abort $ "Translation failed: " ++ err
      Right translation -> do
        -- | The inference runs before anything is written, so that the answer
        -- can be put at the top where it is read without scrolling.
        let prover = NLI.getProver gfProverName $ QT.defaultProofSearchSetting {
              QT.maxDepth = (Just gfMaxDepth),
              QT.maxTime = (Just gfMaxTime)
              }
        verdict <- GFI.infer prover gfNProof gfVerbose translation
        handle <- if null outputPath
                    then return S.stdout
                    else do h <- S.openFile outputPath S.WriteMode
                            S.hSetEncoding h S.utf8
                            return h
        S.hPutStrLn handle $ I.headerOf style
        section handle $ "[FraCaS " ++ show (GFTB.problemId problem)
                         ++ ", section " ++ show (GFTB.section problem) ++ "]"
        -- | The sentences of the test suite, which the treebank does not hold.
        case GFTB.gold problem of
          Nothing -> plain handle "(fracas.xml has no entry for this problem)"
          Just g -> plain handle $ L.intercalate "\n" $
            [ "Premise " ++ show i ++ ": " ++ StrictT.unpack text
            | (text,i) <- zip (GFTB.premiseTexts g) [(1::Int)..] ]
            ++ [ "Hypothesis: " ++ maybe "(none)" StrictT.unpack
                                     (GFTB.hypothesisText g) ]
        section handle "[Result]"
        plain handle $ L.intercalate "\n"
          [ "Prediction: " ++ case verdict of
              GFI.Felicitous result -> show (GFI.answer result)
              GFI.Infelicitous name -> "(the felicity check of " ++ name ++ " failed)"
          , "Gold: " ++ maybe "(none)" show (GFTB.answer problem) ]
        section handle "[Settings]"
        plain handle $ L.intercalate "\n"
          [ "prover: " ++ show gfProverName
          , "nproof: " ++ show gfNProof
          , "maxdepth: " ++ show gfMaxDepth
          , "maxtime: " ++ show gfMaxTime
          , "treebank: " ++ treebankPath
          , "answers: " ++ answersPath ]
        section handle "[Abstract syntax trees]"
        forM_ (GFI.sentences translation) $ \sentence ->
          plain handle $ GFI.role sentence ++ ":\n  "
                       ++ showTree 2 (GFI.tree sentence)
        section handle "[Signature]"
        T.hPutStrLn handle $ gfPrinter style $ DTTwN.fromDeBruijnSignature
                           $ GFI.signature translation
        section handle "[Semantic representations]"
        forM_ (GFI.sentences translation) $ \sentence -> do
          plain handle $ GFI.role sentence ++ " ="
          T.hPutStrLn handle $ gfPrinter style $ UDTTwN.fromDeBruijn []
                             $ GFI.preterm sentence
        case verdict of
          -- | The sections above are written even when the check fails, since
          -- they are what tells which sentence to look at.
          GFI.Infelicitous name -> do
            finish handle
            abort $ "The semantic felicity check of " ++ name ++ " found no diagram."
          GFI.Felicitous result -> do
            forM_ (GFI.felicityChecks result) $ \check -> do
              section handle $ "[Type check query for " ++ GFI.checkedRole check ++ "]"
              T.hPutStrLn handle $ gfPrinter style $ UDTTwN.fromDeBruijnJudgment
                                 $ GFI.checkQuery check
              showDiagram handle ("Type check diagram for " ++ GFI.checkedRole check)
                          (GFI.checkDiagram check)
            showQuery handle "Positive" $ GFI.positive result
            showQuery handle "Negative" $ GFI.negative result
            finish handle
  where
    -- | An explicit path wins; otherwise --open needs one, and picks its own.
    outputPath | not (null gfOutput) = gfOutput
               | gfOpen = "fracas" ++ show gfProblem ++ ".html"
               | otherwise = ""
    -- | Opening a page in a browser only makes sense for the html style.
    style = if gfOpen then I.HTML else gfStyle
    finish handle =
      if null outputPath
        then return ()
        else do S.hClose handle
                S.hPutStrLn S.stderr $ "Wrote " ++ outputPath
                if gfOpen then openInBrowser outputPath else return ()
    -- | interimOf draws a rule but drops the heading in html, so the heading
    -- is written out separately, or the sections would carry no label at all.
    section handle heading = S.hPutStrLn handle $ case style of
      I.HTML -> I.interimOf style heading ++ "<h3>" ++ escapeHtml heading ++ "</h3>"
      _ -> I.interimOf style heading
    -- | Writes plain text, which an html page has to keep the line breaks of.
    plain handle text = S.hPutStrLn handle $ case style of
                          I.HTML -> "<pre>" ++ escapeHtml text ++ "</pre>"
                          _ -> text
    -- | Both queries are shown even when no proof is found, since an empty
    -- result is what tells Unknown apart from Yes and No.
    showQuery handle name (query, diagrams) = do
      section handle $ "[" ++ name ++ " proof search query]"
      T.hPutStrLn handle $ gfPrinter style $ DTTwN.fromDeBruijnProofSearchQuery query
      plain handle $ show (length diagrams) ++ " proof diagram(s) found"
      forM_ (zip diagrams [(1::Int)..]) $ \(diagram,i) ->
        showDiagram handle (name ++ " proof diagram " ++ show i) diagram
    showDiagram handle heading diagram =
      if gfNoDiagram
        then return ()
        else do section handle $ "[" ++ heading ++ "]"
                T.hPutStrLn handle $ gfPrinter style
                                   $ fmap DTTwN.fromDeBruijnJudgment diagram
    abort message = S.hPutStrLn S.stderr message >> exitFailure
    -- | Falls back on an environment variable when the option is not given.
    resolvePath envName optName given
      | not (null given) = return given
      | otherwise = do
          fromEnv <- E.lookupEnv envName
          case fromEnv of
            Just path | not (null path) -> return path
            _ -> abort $ "Specify " ++ optName ++ " or set the $" ++ envName
                         ++ " environment variable."

-- | Hands a file to the browser of the platform.  A failure to open one is not
-- an error, since the file itself has been written by then.
openInBrowser :: FilePath -> IO ()
openInBrowser path = callCommand cmd `catch` \e ->
    S.hPutStrLn S.stderr $ "Failed to open a browser: " ++ show (e::IOException)
  where cmd = case os of
                "darwin" -> "open " ++ show path
                "mingw32" -> "start " ++ show path
                _ -> "xdg-open " ++ show path

lightblueMain :: Options -> IO ()
lightblueMain (Options lang commands style proverName filepath beamW nParse nTypeCheck nProof maxDepth maxTime noTypeCheck noInference ifTime verbose mDepth noShowCat noShowSem leafVertical mExpressBrowser mLexPos) = do
  start <- Time.getCurrentTime
  langOptions <- case lang of
                   JP morphaName filterName -> do
                        jpo <- defaultJpOptions
                        return $ jpo {
                          morphaName = morphaName,
                          nodeFilterBuilder = case filterName of
                                                JFilter.KNP  -> knpFilter
                                                JFilter.KWJA -> kwjaFilter
                                                JFilter.NONE -> \_ -> return (\_ _ -> id) 
                          }
                   EN -> return defaultEnOptions
  contents <- case filepath of
                "-" -> T.getContents
                _   -> T.readFile filepath
  let ifPurify = True
      ifDebug = Nothing
      parseSetting = CP.ParseSetting langOptions beamW nParse nTypeCheck nProof ifPurify ifDebug noInference verbose
  -- | Main routine
  lightblueMainLocal commands parseSetting contents
  -- | Show execution time
  stop <- Time.getCurrentTime
  if ifTime
     then S.hPutStrLn S.stderr $ "Total Execution Time: " ++ (show $ Time.diffUTCTime stop start)
     else return ()
  where
    -- |
    -- | Parse command
    -- |
    lightblueMainLocal (Parse output) parseSetting contents = do
      let handle = S.stdout
          prover = NLI.getProver proverName $ QT.defaultProofSearchSetting {
            QT.maxDepth = (Just maxDepth),
            QT.maxTime = (Just maxTime)
            }
          parseResult = NLI.parseWithTypeCheck parseSetting prover [("dummy",DTT.Entity)] [] $ T.lines contents
          posTagOnly = case output of 
                         I.TREE -> False
                         I.POSTAG -> True
      case style of
        I.EXPRESS -> do
          case mDepth of
            Just d -> Env.setEnv "LB_EXPRESS_DEPTH" (show d)
            Nothing -> return ()
          Env.setEnv "LB_EXPRESS_NOSHOWCAT" (if noShowCat then "1" else "0")
          Env.setEnv "LB_EXPRESS_NOSHOWSEM" (if noShowSem then "1" else "0")
          Env.setEnv "LB_EXPRESS_LEAFVERTICAL" (if leafVertical then "1" else "0")
          -- Lexical Items position
          case mLexPos of
            Just LexTop    -> Env.setEnv "LB_EXPRESS_LEXICALPOS" "top"
            Just LexBottom -> Env.setEnv "LB_EXPRESS_LEXICALPOS" "bottom"
            Just LexNone   -> Env.setEnv "LB_EXPRESS_LEXICALPOS" "none"
            Nothing        -> return ()
          Env.setEnv "LB_EXPRESS_START" "parsing"
          -- Browser selection for Express
          case mExpressBrowser of
            Just BrowserChrome  -> Env.setEnv "LB_EXPRESS_BROWSER" "chrome"
            Just BrowserFirefox -> Env.setEnv "LB_EXPRESS_BROWSER" "firefox"
            Just BrowserDefault -> Env.setEnv "LB_EXPRESS_BROWSER" "default"
            Nothing             -> return ()
        _ -> return ()
      S.hPutStrLn handle $ I.headerOf style
      PPR.printParseResult handle style 1 noTypeCheck posTagOnly "input" parseResult
      S.hPutStrLn handle $ I.footerOf style
    --
    -- | JSeM command
    -- 
    lightblueMainLocal (JSeM jsemID nSample) parseSetting contents = do
      parsedJSeM <- J.xml2jsemData $ T.toStrict contents
      let parsedJSeM'
            | jsemID == "all" = parsedJSeM
            | otherwise = dropWhile (\j -> (J.jsem_id j) /= (StrictT.pack jsemID)) parsedJSeM
          parsedJSeM''
            | nSample < 0 = parsedJSeM'
            | otherwise = take nSample parsedJSeM'
          handle = S.stdout
          prover = NLI.getProver proverName $ QT.defaultProofSearchSetting {
            QT.maxDepth = Just maxDepth, 
            QT.maxTime = Just maxTime
            }
      case style of
        I.EXPRESS -> do
          case parsedJSeM'' of
            [] -> do
              S.hPutStrLn handle $ "No JSeM data matched."
            (j:_) -> do
              let sentences = postpend (map T.fromStrict $ J.premises j) (T.fromStrict $ J.hypothesis j)
              -- 表示オプション
              case mDepth of
                Just d -> Env.setEnv "LB_EXPRESS_DEPTH" (show d)
                Nothing -> return ()
              Env.setEnv "LB_EXPRESS_NOSHOWCAT" (if noShowCat then "1" else "0")
              Env.setEnv "LB_EXPRESS_NOSHOWSEM" (if noShowSem then "1" else "0")
              Env.setEnv "LB_EXPRESS_LEAFVERTICAL" (if leafVertical then "1" else "0")
              Env.setEnv "LB_EXPRESS_START" "inference"
              -- Browser selection for Express
              case mExpressBrowser of
                Just BrowserChrome  -> Env.setEnv "LB_EXPRESS_BROWSER" "chrome"
                Just BrowserFirefox -> Env.setEnv "LB_EXPRESS_BROWSER" "firefox"
                Just BrowserDefault -> Env.setEnv "LB_EXPRESS_BROWSER" "default"
                Nothing             -> return ()
              -- Express を起動
              Express.showExpressInference parseSetting prover [("dummy",DTT.Entity)] [] sentences
        _ -> do
          S.hPutStrLn handle $ I.headerOf style
          pairs <- forM parsedJSeM'' $ \j -> do
            let title = "JSeM-ID " ++ (StrictT.unpack $ J.jsem_id j)
            S.putStr $ "[" ++ title ++ "] "
            mapM_ StrictT.putStr $ J.premises j
            S.putStr " ==> "
            StrictT.putStrLn $ J.hypothesis j
            S.putStr "\n"
            let sentences = postpend (map T.fromStrict $ J.premises j) (T.fromStrict $ J.hypothesis j)
                parseResult = NLI.parseWithTypeCheck parseSetting prover [("dummy",DTT.Entity)] [] sentences
            PPR.printParseResult handle style 1 noTypeCheck False title parseResult
            inferenceLabels <- toList $ NLI.trawlParseResult parseResult
            let groundTruth = J.jsemLabel2YesNo $ J.answer j
                prediction = case inferenceLabels of
                  [] -> J.Other
                  (bestLabel:_) -> bestLabel
            S.putStrLn $ "\nPrediction: " ++ (show prediction) ++ "\nGround truth: " ++ (show groundTruth) ++ "\n"
            return (prediction, groundTruth)
          T.putStrLn $ T.fromStrict $ NLP.showClassificationReport pairs
          S.hPutStrLn handle $ I.footerOf style
    -- | 
    -- | Numeration command
    -- | 
    lightblueMainLocal Numeration parseSetting@CP.ParseSetting{..} contents = do
      let handle = S.stdout
          sentences = T.lines contents
      S.hPutStrLn handle $ I.headerOf style
      case langOptions of
        JpOptions _ _ _ _ _ _ _ _ _ -> 
          mapM_ (\(sid,sentence) -> do
            (_,numeration) <- JLEX.setupLexicon langOptions sentence
            S.hPutStrLn handle $ I.interimOf style $ "[" ++ (show sid) ++ "]"
            mapM_ ((T.hPutStrLn handle) . (I.printLexicalItem style)) numeration
            ) $ zip ([1..]::[Int]) sentences
        EnOptions _ _ _ _ _ -> 
          putStrLn "English version of printNumeration function will be implemented soon."
      S.hPutStrLn handle $ I.footerOf style
    -- |
    -- | Demo command (sequential parsing of a given corpus)
    -- |
    lightblueMainLocal Demo parseSetting contents = processCorpus parseSetting $ T.lines contents
    -- |
    -- | Other commands
    -- |
    lightblueMainLocal Version _ _ = showVersion
    lightblueMainLocal Stat _ _ = showStat
    lightblueMainLocal Test _ _ = test
    -- -- |
    -- -- | Debug 
    -- -- |
    -- --lightblueMainLocal (Debug i j) contents = do
    -- lightblueMainLocal (Debug _ _) contents = do
    --   parsedJSeM <- J.xml2jsemData $ T.toStrict contents
    --   let sentences = T.lines contents
    --   forM_ () $ 
    --     (\(_,sentence) -> do
    --       chart <- CP.parse (CP.ParseSetting jpOptions morphaName beamW nParse nTypeCheck nProof True Nothing Nothing False False) sentence
    --       --let filterednodes = concat $ map snd $ filter (\((x,y),_) -> i <= x && y <= j) $ M.toList chart
    --       --I.printNodes S.stdout I.HTML sid sentence False filterednodes
    --       mapM_ (\((x,y),node) -> do
    --                               S.putStr $ "(" ++ (show x) ++ "," ++ (show y) ++ ") "
    --                               if null node
    --                                  then S.putStrLn ""
    --                                  else T.putStrLn $ T.toText $ CP.cat $ head node
    --                               ) $ M.toList chart
    --       ) $ zip ([0..]::[Int]) sentences
    -- --
    -- -- | Treebank Builder
    -- --
    -- lightblueMainLocal Treebank contents = do
    --   I.treebankBuilder beamw $ T.lines contents

postpend :: [a] -> a -> [a]
postpend [] y = [y]
postpend (x:xs) y = x:(postpend xs y)

-- |
-- | lightblue --version
-- |
showVersion :: IO ()
showVersion = do
  T.putStr "lightblue version: "
  lightbluepath <- E.getEnv "LIGHTBLUE"
  cabal <- T.readFile $ lightbluepath ++ "lightblue.cabal"
  T.putStrLn $ last $ T.words $ head $ filter (T.isPrefixOf "version:") $ T.lines cabal

-- |
-- | lightblue --status
-- |
showStat :: IO ()
showStat = do
  putStrLn "lightblue: "
  putStr "  "
  putStr $ show $ length $ JLEX.emptyCategories
  putStrLn " empty categories from CCG book (Bekki 2010)"
  putStr "  "
  putStr $ show $ length $ JLEX.myLexicon
  putStrLn " lexical entries for closed words from CCG book (Bekki 2010)"
  jumandicpath <- E.getEnv "LIGHTBLUE"
  jumandic <- T.readFile $ jumandicpath ++ "src/Parser/Language/Japanese/Juman/Juman.dic"
  putStr "  "
  putStr $ show $ length $ T.lines jumandic
  putStrLn " lexical entries for open words from JUMAN++ dictionary + Kyoto case frame"

-- | lightblue --test
-- | 
test :: IO ()
test = do
  let signature = [("f", DTT.Pi DTT.Entity DTT.Type)]
      context = []
      termM = UDTT.Sigma UDTT.Entity (UDTT.App (UDTT.Con "f") (UDTT.Var 0))
      typeA = DTT.Type
      tcq = UDTT.Judgment signature context termM typeA
      prover = NLI.getProver NLI.Wani QT.defaultProofSearchSetting
  typeCheckResults <- toList $ typeCheck prover False tcq
  T.putStrLn $ I.startMathML
  T.putStrLn $ I.toMathML $ DTTwN.fromDeBruijnSignature signature
  T.putStrLn $ I.endMathML
  putStrLn $ I.interimOf I.HTML ""
  T.putStrLn $ I.startMathML
  T.putStrLn $ I.toMathML $ fmap DTTwN.fromDeBruijnJudgment $ head typeCheckResults
  T.putStrLn $ I.endMathML

-- | lightblue demo
-- |
processCorpus :: CP.ParseSetting -> [T.Text] -> IO()
processCorpus ps@CP.ParseSetting{..} contents = do
    start <- Time.getCurrentTime
    --let parseSetting = CP.ParseSetting langOptions beamW 1 1 1 True Nothing Nothing False False
    (i,j,k,total) <- L.foldl' (parseSentence ps) (return (0,0,0,0)) $ filter isSentence contents
    stop <- Time.getCurrentTime
    let totaltime = Time.diffUTCTime stop start
    mapM_ (S.hPutStr S.stdout) [
      "Results: Full:Partial:Error = ",
      show i,
      ":",
      show j,
      ":",
      show k,
      ", Full/Total = ",
      show i,
      "/",
      show total,
      " (",
      show ((fromRational ((toEnum i % toEnum total)*100))::F.Fixed F.E3),
      "%)\n",
      "Execution Time: ",
      show totaltime,
      " (average: ",
      show ((fromRational ((toEnum (fromEnum totaltime)) % toEnum (total*1000000000000)))::F.Fixed F.E3),
      "s/sentence)\n"
      ]
    where isSentence t = not (T.null t || "（" `T.isSuffixOf` t)

parseSentence :: CP.ParseSetting
                 -> IO(Int,Int,Int,Int) -- ^ (The number of fully succeeded, partially succeeded, failed, and total parses)
                 -> T.Text              -- ^ A next sentence to parse
                 -> IO(Int,Int,Int,Int)
parseSentence ps@CP.ParseSetting{..} score sentence = do
  (i,j,k,total) <- score
  S.putStr $ "[" ++ show (total+1) ++ "] "
  T.putStrLn sentence
  chart <- CP.parse ps sentence
  case CP.extractParseResult beamWidth chart of
    CP.Full nodes -> 
       do
       T.putStrLn $ T.toText $ head $ nodes
       T.putStr $ T.concat ["Fully parsed, Full:Partial:Failed = ", T.pack (show $ i+1), ":", T.pack (show j), ":", T.pack (show k), ", Full/Total = ", T.pack (show $ i+1), "/", T.pack (show $ total+1), " ("] 
       S.putStrLn $ percent (i+1,total+1) ++ "%)\n"
       return (i+1,j,k,total+1)
    CP.Partial nodes -> 
       do
       T.putStrLn $ T.toText $ head $ nodes
       T.putStr $ T.concat ["Partially parsed, Full:Partial:Failed = ", T.pack (show i), ":", T.pack (show $ j+1), ":", T.pack (show k), ", Full/Total = ", T.pack (show $ i+1), "/", T.pack (show $ total+1), " ("]
       S.putStrLn $ percent (i,total+1) ++ "%)\n"
       return (i,j+1,k,total+1)
    CP.Failed ->
       do
       T.putStr $ T.concat ["Failed, Full:Partial:Failed = ", T.pack (show i), ":", T.pack (show $ j), ":", T.pack (show $ k+1), ", Full/Total = ", T.pack (show $ i+1), "/", T.pack (show $ total+1), " ("]
       S.putStrLn $ percent (i,total+1) ++ "%)\n"
       return (i,j,k+1,total+1)

percent :: (Int,Int) -> String
percent (i,j) = if j == 0
                   then show (0::F.Fixed F.E2)
                   else show ((fromRational (toEnum i % toEnum j)::F.Fixed F.E2) * 100)
