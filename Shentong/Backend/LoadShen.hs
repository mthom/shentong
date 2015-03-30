{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Shentong.Backend.LoadShen where

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
import Shentong.Backend.PortInfo

expr15 :: Types.KLContext Types.Env Types.KLValue
expr15 = do (do kl_shen_shen) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
