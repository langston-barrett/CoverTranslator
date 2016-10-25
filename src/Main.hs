import System
import System.Cmd
import System.Console.GetOpt
import System.Posix.Files
import Data.Maybe ( fromMaybe )
import qualified Text.PrettyPrint.HughesPJ as Pretty(Doc, render)
import Control.Monad
import Prelude hiding    (catch)
import Control.Exception (catch)
import IO                (writeFile, hPutStr, stderr)
import Char

import ExternalCore      (Module)
import ParserExternalCore(parseCore, ParseResult(OkP,FailP))
--import PprExternalCore()
import LambdaLifting     (lambdaLift)
import CaseAbstraction   (caseAbstract, KeepKind(AllTopLevel, VarTopLevel))

import BNFC_Show_Doc     ()
import Cl.Abs as Cl      (Module)
import Core2Cl           (core2cl)
import qualified Cl.Print(printTree, prt)
import Cl2Fol            (cl2fol)

import Fol               (ProofObl, Id(Qname), Library, Def, Prop)
import FolPP             (otterPrinter, tptpPrinter, debugPrinter)
import FoFrontEnd        (splitAndSlice)

import Core2Agda         (core2agda)
import AgdaProp2Goal     (agdaProp2Goal)
import AbsAlfa as Agda   (Module)
import PrintAlfa         (printTree)

import UnObfusc(unObfusc)

dump :: Show a => String -> a -> IO ()
dump label x = 
    writeFile (label++".debug_CoverTranslator") (show x) `catch` \err->
              hPutStr stderr ("Ignoring this problem: "++show err)

data Options = Options { 
  optVerbosity  :: Int,
  optPrintOtter :: Bool,                                 
  optPrintTptp  :: Bool,                                 
  optPrintAgda  :: Bool,                                 
  optLoadFiles  :: [String],
  optIncFiles   :: [String]
}

defaultOptions :: Options
defaultOptions = Options { 
  optVerbosity  = 0,     
  optPrintOtter = False,                           
  optPrintTptp  = False,                         
  optPrintAgda  = False,                         
  optLoadFiles  = [],
  optIncFiles   = []
}

options :: [ OptDescr (Options -> IO Options) ]
options =
    [ Option "v" ["verbose"] 
        (ReqArg (\d -> \opt -> return opt { optVerbosity = read d })
         "VERBOSITY")
        "set VERBOSITY level"
    , Option "l" ["load"] 
        (ReqArg (\f -> \opt -> 
                 return opt { optLoadFiles = f:(optLoadFiles opt) })
         "FILE")
        "load FILE as library"
    , Option "i" ["include"] 
        (ReqArg (\f -> \opt -> 
                 return opt { optIncFiles = f:(optIncFiles opt) })
         "FILE")
        "include FILE as library"
    , Option "o" ["otter"]
        (NoArg (\opt -> return opt { optPrintOtter = True }))
        "output Otter code"
    , Option "t" ["tptp"]
        (NoArg (\opt -> return opt { optPrintTptp  = True }))
        "output tptp code"
    , Option "a" ["agda"]
        (NoArg (\opt -> return opt { optPrintAgda  = True })) 
        "output Agda code"
    ]    


-- | Parse input flags, do main job (using loadFile), 
--   splitAndSlice, write output files
main :: IO ()
main = do 
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt RequireOrder options args
  filename <- case nonOptions of
    [x] -> return x
    []  -> do putStrLn (usageInfo "cfop [options] file" options)
              error "No input file specified"
    _   -> do putStrLn (usageInfo "cfop [options] file" options)
              error "Only one input file allowed"
  opts <- foldl (>>=) (return defaultOptions) actions
  let prAgda = optPrintAgda opts
  if prAgda then agda_main opts filename
            else fol_main  opts filename
  
agda_main opts filename = do
  (name, agda) <- loadFile2Agda opts filename
  when (optPrintAgda opts) (writeFile (name++".agda") (printTree agda))
  -- shoule catch IO errors

fol_main  opts filename = do
  let Options { optPrintOtter   = prOtter,
                optPrintTptp    = prTptp,
                optLoadFiles    = files2load,
		optIncFiles     = files2inc
              } = opts
  (name, b, fCode, fProp) <- loadFile opts True filename 
  loadLibraries            <- mapM (loadFile opts False) files2load 
  incLibraries             <- mapM (loadFile opts True) files2inc
  
  let libraries = loadLibraries ++ incLibraries
      mName     = toUpper (head name) : tail name
      lProofOb  = splitAndSlice libraries (mName, b, fCode, fProp)

  when prOtter (outputProofObligations otterPrinter name lProofOb)
  when prTptp  (outputProofObligations tptpPrinter  name lProofOb)

outputProofObligations :: (ProofObl -> Pretty.Doc) -> 
                          String -> [ProofObl] -> IO ()
outputProofObligations printer baseName lProofOb = mapM_ outputOne lProofOb
    where filename v = baseName ++ "_" ++ (unObfusc v) ++ ".otter"
          outputOne proofOb@(Qname _m v, _code, _prop) =
            writeFile (filename v) (Pretty.render (printer proofOb))

-- | parseCore, caseAbstract, lambdaLift, core2cl, cl2fol
loadFile :: Options -> Bool -> String -> IO Fol.Library
loadFile opts useDef filename = 
    do (name, lifted) <- loadFile_ opts filename
       let cl :: Cl.Module
           cl             = core2cl lifted

       let verbose :: Int
           verbose        = optVerbosity opts
       when (verbose>3) (dump (name++".cl") (Cl.Print.prt 0 cl))

       let fCode :: [Fol.Def]
           fProp :: [Fol.Prop]
           fol@(fCode, fProp) = cl2fol cl
--       when (verbose>0) (dump (name++".fol") (fol))

       return (name, useDef, fCode, fProp)

-- | parseCore, caseAbstract, lambdaLift
loadFile_ :: Options -> String -> IO (String, ExternalCore.Module)
loadFile_ opts filename = 
    do s <- readFile filename
       let (name, _ext)   = splitName filename                   
       let core   :: ExternalCore.Module
           core           = case parseCore s 1 of
                              OkP m   -> m
                              FailP s -> error ("Parse error: " ++ s)
           caseA  :: ExternalCore.Module
--           caseA          = caseAbstract AllTopLevel core
           caseA          = caseAbstract VarTopLevel core

       let verbose :: Int
           verbose        = optVerbosity opts
       when (verbose>0) (dump (name++".caseA.hcr") caseA)

       let lifted :: ExternalCore.Module
           lifted         = lambdaLift caseA
       when (verbose>0) (dump (name++".lifted.hcr") lifted)

       return (name, lifted)

loadFile2Agda :: Options -> String -> IO (String, Agda.Module)
loadFile2Agda opts filename =
    do (name, lifted) <- loadFile_ opts filename
       let agda = agdaProp2Goal $ 
                  core2agda lifted
       return (name, agda)

splitName :: String -> (String, String)
splitName filename = splitN filename
    where splitN s = searchDot ([],[]) (reverse filename)
          searchDot (f,e) []     = (e, [])
          searchDot (f,e) (x:xs)
            | x == '.'           = (reverse xs, e)
            | x == '/'           = (reverse (x:xs) ++ e, [])
            | otherwise          = searchDot (f, x:e) xs
