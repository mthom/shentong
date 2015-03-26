{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Load_Shen where

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
import Port_Info

expr15 :: Types.KLContext Types.Env Types.KLValue
expr15 = do (do kl_shen_shen) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
