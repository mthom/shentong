{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Shentong.Backend.PortInfo where

import Control.Monad.Except
import Control.Parallel
import Shentong.Environment
import Shentong.Primitives as Primitives
import Shentong.Backend.Utils
import Shentong.Types as Types
import Shentong.Utils
import Shentong.Wrap
import Shentong.Backend.Toplevel
import Shentong.Backend.Core
import Shentong.Backend.Sys
import Shentong.Backend.Sequent
import Shentong.Backend.Yacc
import Shentong.Backend.Reader
import Shentong.Backend.Prolog
import Shentong.Backend.Track
import Shentong.Backend.Load
import Shentong.Backend.Writer
import Shentong.Backend.Macros
import Shentong.Backend.Declarations
import Shentong.Backend.Types
import Shentong.Backend.TStar

expr14 :: Types.KLContext Types.Env Types.KLValue
expr14 = do (do klSet (Types.Atom (Types.UnboundSym "*os*")) (Types.Atom (Types.Str "Linux 3.2.0.4-amd64"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*language*")) (Types.Atom (Types.Str "Haskell 2010"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*version*")) (Types.Atom (Types.Str "version 17.3"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*port*")) (Types.Atom (Types.Str "0.2.0"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*porters*")) (Types.Atom (Types.Str "Mark Thom"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*implementation*")) (Types.Atom (Types.Str "GHC 7.8.3"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*release*")) (Types.Atom (Types.Str "0.2.0"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
