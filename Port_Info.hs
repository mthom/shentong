{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Port_Info where

import Control.Monad.Except
import Control.Parallel
import Environment
import Primitives
import SourceUtils
import Types
import Utils
import Wrap
import Toplevel
import Core
import Sys
import Sequent
import Yacc
import Reader
import Prolog
import Track
import Load
import Writer
import Macros
import Declarations
import ShenTypes
import T_Star

expr14 :: Types.KLContext Types.Env Types.KLValue
expr14 = do (do klSet (Types.Atom (Types.UnboundSym "*os*")) (Types.Atom (Types.Str "Linux 3.2.0.4-amd64"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*language*")) (Types.Atom (Types.Str "Haskell 2010"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*version*")) (Types.Atom (Types.Str "version 17.3"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*port*")) (Types.Atom (Types.Str "0.2.0"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*porters*")) (Types.Atom (Types.Str "Mark Thom"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*implementation*")) (Types.Atom (Types.Str "GHC 7.8.3"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*release*")) (Types.Atom (Types.Str "0.2.0"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
