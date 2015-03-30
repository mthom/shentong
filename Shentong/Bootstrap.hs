{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Shentong.Bootstrap where

import Shentong.Environment
import Shentong.Primitives
import Shentong.Backend.Utils
import Shentong.Types
import Shentong.Utils
import Shentong.Wrap
import Shentong.Backend.FunctionTable
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
import Shentong.Backend.LoadShen

bootstrap = do functions
               expr0
               expr1
               expr2
               expr3
               expr4
               expr5
               expr6
               expr7
               expr8
               expr9
               expr10
               expr11
               expr12
               expr13
               expr14
               expr15
