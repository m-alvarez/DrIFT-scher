-- Based on DrIFT 1.0 by Noel Winstanley
--  hacked for Haskell 98 by Malcolm Wallace, University of York, Feb 1999.
--  modified by various people, now maintained by John Meacham
module Main(main) where

import ChaseImports
import DataP
import GenUtil
import GetOpt
import Data.List (partition,isSuffixOf,sort, groupBy, sortBy)
import Control.Monad(unless)
import PreludData(preludeData)
import Pretty
import RuleUtils (commentLine,texts)
import RuleUtils(Rule,Tag)
import Version
import qualified Rules(rules)
import System.IO
import System.Environment
import Data.Char

data Op = OpList | OpDerive | OpVersion

data Env = Env {
    envVerbose :: Bool,
    envOutput :: (Maybe String),
    envOperation :: Op,
    envNoline :: Bool,
    envArgs :: [(String,String)],
    envResultsOnly :: Bool,
    envGlobalRules :: [Tag],
    envIgnoreDirectives :: Bool
    }


env :: Env
env = Env {
    envVerbose = False,
    envOutput = Nothing,
    envOperation = OpDerive,
    envNoline = False,
    envArgs = [],
    envResultsOnly = False,
    envIgnoreDirectives = False,
    envGlobalRules = []
    }


getOutput :: Env -> IO Handle
getOutput e = maybe (return stdout) (\fn -> openFile fn WriteMode) (envOutput e)

options :: [OptDescr (Env -> Env)]
options =
    [ Option ['v'] ["verbose"] (NoArg (\e->e{envVerbose = True}))       "chatty output on stderr"
    , Option ['V'] ["version"] (NoArg (\e->e{envOperation = OpVersion}))       "show version number"
    , Option ['l'] ["list"] (NoArg (\e->e{envOperation = OpList}))       "list available derivations"
    , Option ['L'] ["noline"] (NoArg (\e->e{envNoline = True}))    "omit line pragmas from output"
    , Option ['o'] ["output"]  (ReqArg (\x e->e{envOutput = (Just x)}) "FILE")  "output FILE"
    , Option ['s'] ["set"]    (ReqArg setArg "name:value")  "set argument to value"
    , Option ['r'] ["resultsonly"] (NoArg (\e->e{envResultsOnly = True}))  "output only results, do not include source file"
    , Option ['g'] ["global"]  (ReqArg addGlobalRule "rule") "addition rules to apply globally"
    , Option ['i'] ["ignore"]  (NoArg (\e->e{envIgnoreDirectives = True})) "ignore directives in file. useful with -g"
    ]

setArg :: String -> Env -> Env
setArg x e = e {envArgs = (n, tail rest):(envArgs e)} where
    (n,rest) = span (/= ':') x
addGlobalRule :: Tag -> Env -> Env
addGlobalRule x e = e {envGlobalRules = x:(envGlobalRules e)}


categorize :: Ord c => [(c,a)] -> [(c,[a])]
categorize xs = map f $ groupBy fstEq $ sortBy fstOrd xs where
    f ys = (fst (head ys),snds ys)
    fstEq (a,_) (b,_) = a == b
    fstOrd (a,_) (b,_) = compare a b

doList :: IO ()
doList = do
    let rn = categorize [(c,(n,h)) | (n,_,c,h,_) <- Rules.rules]
    putStrLn $ unlines $ buildTableLL $ concat [ (c ++ ":","") : (map (\(a,b) -> ("   " ++ a, b)) $ sort xs)| (c,xs)<- rn]


header :: String
header = "Usage: DrIFT [OPTION...] file"
main :: IO ()
main = do
    argv <- getArgs
    (env,n) <- case (getOpt Permute options argv) of
	(as,n,[]) -> return (foldr ($) env as ,n)
	(_,_,errs) -> putErrDie (concat errs ++ usageInfo header options)
    case env of
	Env { envOperation = OpList } -> doList
	Env { envOperation = OpVersion} -> putStr ("Version " ++ fullName ++ "\n")
	_ -> case n of
	    [n] -> derive env n
	    _ -> putErrDie ("single input file must be specified.\n" ++ usageInfo header options)



derive :: Env -> FilePath -> IO ()
derive env fname = do
    let findent xs = f (lines xs) where
            f (x:xs) = let (w,n) = span isSpace x in case n of
                (c:_) | isAlpha c -> length w
                _ -> f xs
            f [] = 0
    file <- readFile fname
    let (body,_) = userCode file
        b = ".lhs" `isSuffixOf` fname
        zz = fromLit b body
        ss = if b then replicate (findent zz) ' ' else ""
    handle <- getOutput env
    hPutStr handle $ ss ++ "{- Generated by " ++ package ++ " (Automatic class derivations for Haskell) -}\n"
    unless (envNoline env) $ hPutStr handle $ ss ++ "{-# LINE 1 \""  ++ fname ++ "\" #-}\n"
    let (docs,dats,todo) = process . addGlobals env  . parser $ zz
    moreDocs <- fmap ((\(x,_,_) -> x) . process) (chaseImports body todo)
    let result = (\r -> codeSeperator ++ '\n':r) .  render . vsep $ (docs ++ sepDoc:moreDocs)
    if (envResultsOnly env) then hPutStr handle result else do
        hPutStr handle zz
        hPutStr handle $ unlines . map (ss ++) . lines $ result

    hFlush handle


addGlobals :: Env -> [([Tag], Data)] -> [([Tag], Data)]
addGlobals env tds    =  (envGlobalRules env,Directive):concatMap f tds where
    f x | not (envIgnoreDirectives env) = [x]
    f (_,Directive)  = []
    f (_,TypeName _)  = []
    f (_,d) = [([],d)]


rules :: [(String, Data -> Doc)]
rules = map (\(a,b,_,_,_) -> (a,b)) Rules.rules
-- codeRender doc = fullRender PageMode 80 1 doc "" -- now obsolete
vsep :: [Doc] -> Doc
vsep = vcat . map ($$ (text ""))
sepDoc :: Doc
sepDoc = commentLine . text $ " Imported from other files :-"

backup :: FilePath -> FilePath
backup f = (reverse . dropWhile (/= '.') . reverse ) f ++ "bak"

newfile :: FilePath -> FilePath
newfile f = (reverse . dropWhile (/= '.') . reverse ) f ++ "DrIFT"

-- Main Pass - Takes parsed data and rules and combines to create instances...
-- Returns all parsed data, ande commands calling for files to be imported if
-- datatypes aren't located in this module.

process :: ToDo -> ([Doc],[Data],ToDo)
process i = (concatMap g dats ++ concatMap h moreDats,parsedData,imports)
       where
	g (tags,d) = [(find t rules) d | t <- (tags ++ directives)]
	h (tags,d) = [(find t rules) d | t <- tags]
	directives = concatMap fst globals
	(dats,commands) = partition (isData . snd) i
	(globals,fors) = partition (\(_,d) -> d == Directive) commands
	(moreDats,imports) = resolve parsedData fors ([],[])
	parsedData = map snd dats ++ preludeData

find :: Tag -> [Rule] -> (Data -> Doc)
find t r = case filter ((==t) . fst) $ r of
               [] -> const (commentLine warning)
               (x:_) -> snd x
   where
   warning = hsep . texts $ ["Warning : Rule",t,"not found."]

