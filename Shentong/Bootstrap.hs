{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Bootstrap where

import Environment
import Core.Primitives
import Backend.Utils
import Core.Types
import Core.Utils
import Wrap
import Backend.FunctionTable
import Backend.Toplevel
import Backend.Core
import Backend.Sys
import Backend.Sequent
import Backend.Yacc
import Backend.Reader
import Backend.Prolog
import Backend.Track
import Backend.Load
import Backend.Writer
import Backend.Macros
import Backend.Declarations
import Backend.Types
import Backend.TStar
import Backend.PortInfo
import Backend.LoadShen

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
