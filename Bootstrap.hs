{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Bootstrap where

import Control.Monad.Except
import Control.Parallel
import Environment
import Primitives
import SourceUtils
import Types
import Utils
import Wrap
import FunctionTable
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
import Port_Info
import Load_Shen

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
