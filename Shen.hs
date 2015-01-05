{-# LANGUAGE OverloadedStrings #-}

import Control.Monad.Except
import Data.Attoparsec.Text
import qualified Data.Text as T
import Environment
import Interpreter
import Parser
import Primitives
import System.Environment.FindBin
import Types

loadFile :: String -> KLContext Env ()
loadFile file = do
  progPath <- liftIO getProgPath
  contents <- liftIO $ readFile (progPath ++ "/" ++ file)
  case parseOnly parseTopLevels (T.pack contents) of
    Left err -> liftIO $ putStrLn err
    Right tl -> mapM_ evalTopLevel tl
             
loadFiles :: KLContext Env ()
loadFiles = do
  loadFile "K Lambda/toplevel.kl"
  loadFile "K Lambda/core.kl"
  loadFile "K Lambda/sys.kl"
  loadFile "K Lambda/sequent.kl"
  loadFile "K Lambda/yacc.kl"
  loadFile "K Lambda/reader.kl"
  loadFile "K Lambda/prolog.kl"
  loadFile "K Lambda/track.kl"
  loadFile "K Lambda/load.kl"
  loadFile "K Lambda/writer.kl"
  loadFile "K Lambda/macros.kl"  
  loadFile "K Lambda/declarations.kl"
  loadFile "K Lambda/types.kl"
  loadFile "K Lambda/t-star.kl"
  loadFile "K Lambda/port-info.kl"
  loadFile "K Lambda/load-shen.kl"

main :: IO ()
main = do
  env <- initEnv
  runKLC loadFiles
       (\_ _ -> return ())
       (\_ _ -> return ())
       env       
