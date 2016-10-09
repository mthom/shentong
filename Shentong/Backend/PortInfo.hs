{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

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

{-
Copyright (c) 2015, Mark Tarver
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. The name of Mark Tarver may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY
EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}

expr14 :: Types.KLContext Types.Env Types.KLValue
expr14 = do (do klSet (Types.Atom (Types.UnboundSym "*os*")) (Types.Atom (Types.Str "Windows 7"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*language*")) (Types.Atom (Types.Str "Haskell 2010"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*version*")) (Types.Atom (Types.Str "version 19.1"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*port*")) (Types.Atom (Types.Str "0.3.1"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*porters*")) (Types.Atom (Types.Str "Mark Thom"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*implementation*")) (Types.Atom (Types.Str "GHC 8.0.1"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*release*")) (Types.Atom (Types.Str "0.1"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
