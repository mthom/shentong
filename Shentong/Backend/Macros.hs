{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Backend.Macros where

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

kl_macroexpand :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_macroexpand (!kl_V1527) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do !kl_if_1 <- kl_V1527 `pseq` (kl_Y `pseq` eq kl_V1527 kl_Y)
                                                                                            case kl_if_1 of
                                                                                                Atom (B (True)) -> do return kl_V1527
                                                                                                Atom (B (False)) -> do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_macroexpand kl_Z)))
                                                                                                                          appl_2 `pseq` (kl_Y `pseq` kl_shen_walk appl_2 kl_Y)
                                                                                                _ -> throwError "if: expected boolean")))
                                !appl_3 <- value (Types.Atom (Types.UnboundSym "*macros*"))
                                !appl_4 <- appl_3 `pseq` (kl_V1527 `pseq` kl_shen_compose appl_3 kl_V1527)
                                appl_4 `pseq` applyWrapper appl_0 [appl_4]

kl_shen_error_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_error_macro (!kl_V1529) = do let pat_cond_0 kl_V1529 kl_V1529t kl_V1529th kl_V1529tt = do !appl_1 <- kl_V1529th `pseq` (kl_V1529tt `pseq` kl_shen_mkstr kl_V1529th kl_V1529tt)
                                                                                                  !appl_2 <- appl_1 `pseq` klCons appl_1 (Types.Atom Types.Nil)
                                                                                                  appl_2 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_2
                                         pat_cond_3 = do do return kl_V1529
                                      in case kl_V1529 of
                                             !(kl_V1529@(Cons (Atom (UnboundSym "error"))
                                                              (!(kl_V1529t@(Cons (!kl_V1529th)
                                                                                 (!kl_V1529tt)))))) -> pat_cond_0 kl_V1529 kl_V1529t kl_V1529th kl_V1529tt
                                             !(kl_V1529@(Cons (ApplC (PL "error" _))
                                                              (!(kl_V1529t@(Cons (!kl_V1529th)
                                                                                 (!kl_V1529tt)))))) -> pat_cond_0 kl_V1529 kl_V1529t kl_V1529th kl_V1529tt
                                             !(kl_V1529@(Cons (ApplC (Func "error" _))
                                                              (!(kl_V1529t@(Cons (!kl_V1529th)
                                                                                 (!kl_V1529tt)))))) -> pat_cond_0 kl_V1529 kl_V1529t kl_V1529th kl_V1529tt
                                             _ -> pat_cond_3

kl_shen_output_macro :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_output_macro (!kl_V1531) = do let pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt = do !appl_1 <- kl_V1531th `pseq` (kl_V1531tt `pseq` kl_shen_mkstr kl_V1531th kl_V1531tt)
                                                                                                   !appl_2 <- klCons (ApplC (PL "stoutput" kl_stoutput)) (Types.Atom Types.Nil)
                                                                                                   !appl_3 <- appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil)
                                                                                                   !appl_4 <- appl_1 `pseq` (appl_3 `pseq` klCons appl_1 appl_3)
                                                                                                   appl_4 `pseq` klCons (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_4
                                          pat_cond_5 kl_V1531 kl_V1531t kl_V1531th = do !appl_6 <- klCons (ApplC (PL "stoutput" kl_stoutput)) (Types.Atom Types.Nil)
                                                                                        !appl_7 <- appl_6 `pseq` klCons appl_6 (Types.Atom Types.Nil)
                                                                                        !appl_8 <- kl_V1531th `pseq` (appl_7 `pseq` klCons kl_V1531th appl_7)
                                                                                        appl_8 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_8
                                          pat_cond_9 = do do return kl_V1531
                                       in case kl_V1531 of
                                              !(kl_V1531@(Cons (Atom (UnboundSym "output"))
                                                               (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                  (!kl_V1531tt)))))) -> pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt
                                              !(kl_V1531@(Cons (ApplC (PL "output" _))
                                                               (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                  (!kl_V1531tt)))))) -> pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt
                                              !(kl_V1531@(Cons (ApplC (Func "output" _))
                                                               (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                  (!kl_V1531tt)))))) -> pat_cond_0 kl_V1531 kl_V1531t kl_V1531th kl_V1531tt
                                              !(kl_V1531@(Cons (Atom (UnboundSym "pr"))
                                                               (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                  (Atom (Nil))))))) -> pat_cond_5 kl_V1531 kl_V1531t kl_V1531th
                                              !(kl_V1531@(Cons (ApplC (PL "pr" _))
                                                               (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                  (Atom (Nil))))))) -> pat_cond_5 kl_V1531 kl_V1531t kl_V1531th
                                              !(kl_V1531@(Cons (ApplC (Func "pr" _))
                                                               (!(kl_V1531t@(Cons (!kl_V1531th)
                                                                                  (Atom (Nil))))))) -> pat_cond_5 kl_V1531 kl_V1531t kl_V1531th
                                              _ -> pat_cond_9

kl_shen_make_string_macro :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_make_string_macro (!kl_V1533) = do let pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt = do kl_V1533th `pseq` (kl_V1533tt `pseq` kl_shen_mkstr kl_V1533th kl_V1533tt)
                                               pat_cond_1 = do do return kl_V1533
                                            in case kl_V1533 of
                                                   !(kl_V1533@(Cons (Atom (UnboundSym "make-string"))
                                                                    (!(kl_V1533t@(Cons (!kl_V1533th)
                                                                                       (!kl_V1533tt)))))) -> pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt
                                                   !(kl_V1533@(Cons (ApplC (PL "make-string" _))
                                                                    (!(kl_V1533t@(Cons (!kl_V1533th)
                                                                                       (!kl_V1533tt)))))) -> pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt
                                                   !(kl_V1533@(Cons (ApplC (Func "make-string" _))
                                                                    (!(kl_V1533t@(Cons (!kl_V1533th)
                                                                                       (!kl_V1533tt)))))) -> pat_cond_0 kl_V1533 kl_V1533t kl_V1533th kl_V1533tt
                                                   _ -> pat_cond_1

kl_shen_input_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_input_macro (!kl_V1535) = do let pat_cond_0 kl_V1535 = do !appl_1 <- klCons (ApplC (PL "stinput" kl_stinput)) (Types.Atom Types.Nil)
                                                                  !appl_2 <- appl_1 `pseq` klCons appl_1 (Types.Atom Types.Nil)
                                                                  appl_2 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_2
                                         pat_cond_3 kl_V1535 = do !appl_4 <- klCons (ApplC (PL "stinput" kl_stinput)) (Types.Atom Types.Nil)
                                                                  !appl_5 <- appl_4 `pseq` klCons appl_4 (Types.Atom Types.Nil)
                                                                  appl_5 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_5
                                         pat_cond_6 kl_V1535 = do !appl_7 <- klCons (ApplC (PL "stinput" kl_stinput)) (Types.Atom Types.Nil)
                                                                  !appl_8 <- appl_7 `pseq` klCons appl_7 (Types.Atom Types.Nil)
                                                                  appl_8 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_8
                                         pat_cond_9 kl_V1535 kl_V1535t kl_V1535th = do !appl_10 <- klCons (ApplC (PL "stinput" kl_stinput)) (Types.Atom Types.Nil)
                                                                                       !appl_11 <- appl_10 `pseq` klCons appl_10 (Types.Atom Types.Nil)
                                                                                       !appl_12 <- kl_V1535th `pseq` (appl_11 `pseq` klCons kl_V1535th appl_11)
                                                                                       appl_12 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_12
                                         pat_cond_13 kl_V1535 = do !appl_14 <- klCons (ApplC (PL "stinput" kl_stinput)) (Types.Atom Types.Nil)
                                                                   !appl_15 <- appl_14 `pseq` klCons appl_14 (Types.Atom Types.Nil)
                                                                   appl_15 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_15
                                         pat_cond_16 = do do return kl_V1535
                                      in case kl_V1535 of
                                             !(kl_V1535@(Cons (Atom (UnboundSym "lineread"))
                                                              (Atom (Nil)))) -> pat_cond_0 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (PL "lineread" _))
                                                              (Atom (Nil)))) -> pat_cond_0 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (Func "lineread" _))
                                                              (Atom (Nil)))) -> pat_cond_0 kl_V1535
                                             !(kl_V1535@(Cons (Atom (UnboundSym "input"))
                                                              (Atom (Nil)))) -> pat_cond_3 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (PL "input" _))
                                                              (Atom (Nil)))) -> pat_cond_3 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (Func "input" _))
                                                              (Atom (Nil)))) -> pat_cond_3 kl_V1535
                                             !(kl_V1535@(Cons (Atom (UnboundSym "read"))
                                                              (Atom (Nil)))) -> pat_cond_6 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (PL "read" _))
                                                              (Atom (Nil)))) -> pat_cond_6 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (Func "read" _))
                                                              (Atom (Nil)))) -> pat_cond_6 kl_V1535
                                             !(kl_V1535@(Cons (Atom (UnboundSym "input+"))
                                                              (!(kl_V1535t@(Cons (!kl_V1535th)
                                                                                 (Atom (Nil))))))) -> pat_cond_9 kl_V1535 kl_V1535t kl_V1535th
                                             !(kl_V1535@(Cons (ApplC (PL "input+" _))
                                                              (!(kl_V1535t@(Cons (!kl_V1535th)
                                                                                 (Atom (Nil))))))) -> pat_cond_9 kl_V1535 kl_V1535t kl_V1535th
                                             !(kl_V1535@(Cons (ApplC (Func "input+" _))
                                                              (!(kl_V1535t@(Cons (!kl_V1535th)
                                                                                 (Atom (Nil))))))) -> pat_cond_9 kl_V1535 kl_V1535t kl_V1535th
                                             !(kl_V1535@(Cons (Atom (UnboundSym "read-byte"))
                                                              (Atom (Nil)))) -> pat_cond_13 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (PL "read-byte" _))
                                                              (Atom (Nil)))) -> pat_cond_13 kl_V1535
                                             !(kl_V1535@(Cons (ApplC (Func "read-byte" _))
                                                              (Atom (Nil)))) -> pat_cond_13 kl_V1535
                                             _ -> pat_cond_16

kl_shen_compose :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_compose (!kl_V1538) (!kl_V1539) = do let pat_cond_0 = do return kl_V1539
                                                 pat_cond_1 kl_V1538 kl_V1538h kl_V1538t = do !appl_2 <- kl_V1539 `pseq` applyWrapper kl_V1538h [kl_V1539]
                                                                                              kl_V1538t `pseq` (appl_2 `pseq` kl_shen_compose kl_V1538t appl_2)
                                                 pat_cond_3 = do do kl_shen_f_error (ApplC (wrapNamed "shen.compose" kl_shen_compose))
                                              in case kl_V1538 of
                                                     kl_V1538@(Atom (Nil)) -> pat_cond_0
                                                     !(kl_V1538@(Cons (!kl_V1538h)
                                                                      (!kl_V1538t))) -> pat_cond_1 kl_V1538 kl_V1538h kl_V1538t
                                                     _ -> pat_cond_3

kl_shen_compile_macro :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_compile_macro (!kl_V1541) = do let pat_cond_0 kl_V1541 kl_V1541t kl_V1541th kl_V1541tt kl_V1541tth = do !appl_1 <- klCons (Types.Atom (Types.UnboundSym "E")) (Types.Atom Types.Nil)
                                                                                                                !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_1
                                                                                                                !appl_3 <- klCons (Types.Atom (Types.UnboundSym "E")) (Types.Atom Types.Nil)
                                                                                                                !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str "parse error here: ~S~%")) appl_3
                                                                                                                !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "error")) appl_4
                                                                                                                !appl_6 <- klCons (Types.Atom (Types.Str "parse error~%")) (Types.Atom Types.Nil)
                                                                                                                !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "error")) appl_6
                                                                                                                !appl_8 <- appl_7 `pseq` klCons appl_7 (Types.Atom Types.Nil)
                                                                                                                !appl_9 <- appl_5 `pseq` (appl_8 `pseq` klCons appl_5 appl_8)
                                                                                                                !appl_10 <- appl_2 `pseq` (appl_9 `pseq` klCons appl_2 appl_9)
                                                                                                                !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_10
                                                                                                                !appl_12 <- appl_11 `pseq` klCons appl_11 (Types.Atom Types.Nil)
                                                                                                                !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_12
                                                                                                                !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_13
                                                                                                                !appl_15 <- appl_14 `pseq` klCons appl_14 (Types.Atom Types.Nil)
                                                                                                                !appl_16 <- kl_V1541tth `pseq` (appl_15 `pseq` klCons kl_V1541tth appl_15)
                                                                                                                !appl_17 <- kl_V1541th `pseq` (appl_16 `pseq` klCons kl_V1541th appl_16)
                                                                                                                appl_17 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_17
                                           pat_cond_18 = do do return kl_V1541
                                        in case kl_V1541 of
                                               !(kl_V1541@(Cons (Atom (UnboundSym "compile"))
                                                                (!(kl_V1541t@(Cons (!kl_V1541th)
                                                                                   (!(kl_V1541tt@(Cons (!kl_V1541tth)
                                                                                                       (Atom (Nil)))))))))) -> pat_cond_0 kl_V1541 kl_V1541t kl_V1541th kl_V1541tt kl_V1541tth
                                               !(kl_V1541@(Cons (ApplC (PL "compile" _))
                                                                (!(kl_V1541t@(Cons (!kl_V1541th)
                                                                                   (!(kl_V1541tt@(Cons (!kl_V1541tth)
                                                                                                       (Atom (Nil)))))))))) -> pat_cond_0 kl_V1541 kl_V1541t kl_V1541th kl_V1541tt kl_V1541tth
                                               !(kl_V1541@(Cons (ApplC (Func "compile" _))
                                                                (!(kl_V1541t@(Cons (!kl_V1541th)
                                                                                   (!(kl_V1541tt@(Cons (!kl_V1541tth)
                                                                                                       (Atom (Nil)))))))))) -> pat_cond_0 kl_V1541 kl_V1541t kl_V1541th kl_V1541tt kl_V1541tth
                                               _ -> pat_cond_18

kl_shen_prolog_macro :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_prolog_macro (!kl_V1543) = do let pat_cond_0 kl_V1543 kl_V1543t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_F) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Receive) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_PrologDef) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Query) -> do return kl_Query)))
                                                                                                                                                                                                                                                                               !appl_5 <- klCons (ApplC (PL "shen.start-new-prolog-process" kl_shen_start_new_prolog_process)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                               !appl_6 <- klCons (Atom (B True)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                               !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "freeze")) appl_6
                                                                                                                                                                                                                                                                               !appl_8 <- appl_7 `pseq` klCons appl_7 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                               !appl_9 <- appl_5 `pseq` (appl_8 `pseq` klCons appl_5 appl_8)
                                                                                                                                                                                                                                                                               !appl_10 <- kl_Receive `pseq` (appl_9 `pseq` kl_append kl_Receive appl_9)
                                                                                                                                                                                                                                                                               !appl_11 <- kl_F `pseq` (appl_10 `pseq` klCons kl_F appl_10)
                                                                                                                                                                                                                                                                               appl_11 `pseq` applyWrapper appl_4 [appl_11])))
                                                                                                                                                                                                           !appl_12 <- kl_F `pseq` klCons kl_F (Types.Atom Types.Nil)
                                                                                                                                                                                                           !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.UnboundSym "defprolog")) appl_12
                                                                                                                                                                                                           !appl_14 <- klCons (Types.Atom (Types.UnboundSym "<--")) (Types.Atom Types.Nil)
                                                                                                                                                                                                           !appl_15 <- kl_V1543t `pseq` kl_shen_pass_literals kl_V1543t
                                                                                                                                                                                                           !appl_16 <- klCons (Types.Atom (Types.UnboundSym ";")) (Types.Atom Types.Nil)
                                                                                                                                                                                                           !appl_17 <- appl_15 `pseq` (appl_16 `pseq` kl_append appl_15 appl_16)
                                                                                                                                                                                                           !appl_18 <- appl_14 `pseq` (appl_17 `pseq` kl_append appl_14 appl_17)
                                                                                                                                                                                                           !appl_19 <- kl_Receive `pseq` (appl_18 `pseq` kl_append kl_Receive appl_18)
                                                                                                                                                                                                           !appl_20 <- appl_13 `pseq` (appl_19 `pseq` kl_append appl_13 appl_19)
                                                                                                                                                                                                           !appl_21 <- appl_20 `pseq` kl_eval appl_20
                                                                                                                                                                                                           appl_21 `pseq` applyWrapper appl_3 [appl_21])))
                                                                                                                                         !appl_22 <- kl_V1543t `pseq` kl_shen_receive_terms kl_V1543t
                                                                                                                                         appl_22 `pseq` applyWrapper appl_2 [appl_22])))
                                                                             !appl_23 <- kl_gensym (Types.Atom (Types.UnboundSym "shen.f"))
                                                                             appl_23 `pseq` applyWrapper appl_1 [appl_23]
                                          pat_cond_24 = do do return kl_V1543
                                       in case kl_V1543 of
                                              !(kl_V1543@(Cons (Atom (UnboundSym "prolog?"))
                                                               (!kl_V1543t))) -> pat_cond_0 kl_V1543 kl_V1543t
                                              !(kl_V1543@(Cons (ApplC (PL "prolog?" _))
                                                               (!kl_V1543t))) -> pat_cond_0 kl_V1543 kl_V1543t
                                              !(kl_V1543@(Cons (ApplC (Func "prolog?" _))
                                                               (!kl_V1543t))) -> pat_cond_0 kl_V1543 kl_V1543t
                                              _ -> pat_cond_24

kl_shen_receive_terms :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_receive_terms (!kl_V1549) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                           pat_cond_1 kl_V1549 kl_V1549h kl_V1549ht kl_V1549hth kl_V1549t = do !appl_2 <- kl_V1549t `pseq` kl_shen_receive_terms kl_V1549t
                                                                                                               kl_V1549hth `pseq` (appl_2 `pseq` klCons kl_V1549hth appl_2)
                                           pat_cond_3 kl_V1549 kl_V1549h kl_V1549t = do kl_V1549t `pseq` kl_shen_receive_terms kl_V1549t
                                           pat_cond_4 = do do kl_shen_f_error (ApplC (wrapNamed "shen.receive-terms" kl_shen_receive_terms))
                                        in case kl_V1549 of
                                               kl_V1549@(Atom (Nil)) -> pat_cond_0
                                               !(kl_V1549@(Cons (!(kl_V1549h@(Cons (Atom (UnboundSym "shen.receive"))
                                                                                   (!(kl_V1549ht@(Cons (!kl_V1549hth)
                                                                                                       (Atom (Nil))))))))
                                                                (!kl_V1549t))) -> pat_cond_1 kl_V1549 kl_V1549h kl_V1549ht kl_V1549hth kl_V1549t
                                               !(kl_V1549@(Cons (!(kl_V1549h@(Cons (ApplC (PL "shen.receive"
                                                                                              _))
                                                                                   (!(kl_V1549ht@(Cons (!kl_V1549hth)
                                                                                                       (Atom (Nil))))))))
                                                                (!kl_V1549t))) -> pat_cond_1 kl_V1549 kl_V1549h kl_V1549ht kl_V1549hth kl_V1549t
                                               !(kl_V1549@(Cons (!(kl_V1549h@(Cons (ApplC (Func "shen.receive"
                                                                                                _))
                                                                                   (!(kl_V1549ht@(Cons (!kl_V1549hth)
                                                                                                       (Atom (Nil))))))))
                                                                (!kl_V1549t))) -> pat_cond_1 kl_V1549 kl_V1549h kl_V1549ht kl_V1549hth kl_V1549t
                                               !(kl_V1549@(Cons (!kl_V1549h)
                                                                (!kl_V1549t))) -> pat_cond_3 kl_V1549 kl_V1549h kl_V1549t
                                               _ -> pat_cond_4

kl_shen_pass_literals :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_pass_literals (!kl_V1553) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                           pat_cond_1 kl_V1553 kl_V1553h kl_V1553ht kl_V1553hth kl_V1553t = do kl_V1553t `pseq` kl_shen_pass_literals kl_V1553t
                                           pat_cond_2 kl_V1553 kl_V1553h kl_V1553t = do !appl_3 <- kl_V1553t `pseq` kl_shen_pass_literals kl_V1553t
                                                                                        kl_V1553h `pseq` (appl_3 `pseq` klCons kl_V1553h appl_3)
                                           pat_cond_4 = do do kl_shen_f_error (ApplC (wrapNamed "shen.pass-literals" kl_shen_pass_literals))
                                        in case kl_V1553 of
                                               kl_V1553@(Atom (Nil)) -> pat_cond_0
                                               !(kl_V1553@(Cons (!(kl_V1553h@(Cons (Atom (UnboundSym "shen.receive"))
                                                                                   (!(kl_V1553ht@(Cons (!kl_V1553hth)
                                                                                                       (Atom (Nil))))))))
                                                                (!kl_V1553t))) -> pat_cond_1 kl_V1553 kl_V1553h kl_V1553ht kl_V1553hth kl_V1553t
                                               !(kl_V1553@(Cons (!(kl_V1553h@(Cons (ApplC (PL "shen.receive"
                                                                                              _))
                                                                                   (!(kl_V1553ht@(Cons (!kl_V1553hth)
                                                                                                       (Atom (Nil))))))))
                                                                (!kl_V1553t))) -> pat_cond_1 kl_V1553 kl_V1553h kl_V1553ht kl_V1553hth kl_V1553t
                                               !(kl_V1553@(Cons (!(kl_V1553h@(Cons (ApplC (Func "shen.receive"
                                                                                                _))
                                                                                   (!(kl_V1553ht@(Cons (!kl_V1553hth)
                                                                                                       (Atom (Nil))))))))
                                                                (!kl_V1553t))) -> pat_cond_1 kl_V1553 kl_V1553h kl_V1553ht kl_V1553hth kl_V1553t
                                               !(kl_V1553@(Cons (!kl_V1553h)
                                                                (!kl_V1553t))) -> pat_cond_2 kl_V1553 kl_V1553h kl_V1553t
                                               _ -> pat_cond_4

kl_shen_defprolog_macro :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_defprolog_macro (!kl_V1555) = do let pat_cond_0 kl_V1555 kl_V1555t kl_V1555th kl_V1555tt = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do kl_Y `pseq` kl_shen_LBdefprologRB kl_Y)))
                                                                                                      let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do kl_V1555th `pseq` (kl_Y `pseq` kl_shen_prolog_error kl_V1555th kl_Y))))
                                                                                                      appl_1 `pseq` (kl_V1555t `pseq` (appl_2 `pseq` kl_compile appl_1 kl_V1555t appl_2))
                                             pat_cond_3 = do do return kl_V1555
                                          in case kl_V1555 of
                                                 !(kl_V1555@(Cons (Atom (UnboundSym "defprolog"))
                                                                  (!(kl_V1555t@(Cons (!kl_V1555th)
                                                                                     (!kl_V1555tt)))))) -> pat_cond_0 kl_V1555 kl_V1555t kl_V1555th kl_V1555tt
                                                 !(kl_V1555@(Cons (ApplC (PL "defprolog" _))
                                                                  (!(kl_V1555t@(Cons (!kl_V1555th)
                                                                                     (!kl_V1555tt)))))) -> pat_cond_0 kl_V1555 kl_V1555t kl_V1555th kl_V1555tt
                                                 !(kl_V1555@(Cons (ApplC (Func "defprolog" _))
                                                                  (!(kl_V1555t@(Cons (!kl_V1555th)
                                                                                     (!kl_V1555tt)))))) -> pat_cond_0 kl_V1555 kl_V1555t kl_V1555th kl_V1555tt
                                                 _ -> pat_cond_3

kl_shen_datatype_macro :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_datatype_macro (!kl_V1557) = do let pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt = do !appl_1 <- kl_V1557th `pseq` kl_shen_intern_type kl_V1557th
                                                                                                     !appl_2 <- klCons (Types.Atom (Types.UnboundSym "X")) (Types.Atom Types.Nil)
                                                                                                     !appl_3 <- appl_2 `pseq` klCons (ApplC (wrapNamed "shen.<datatype-rules>" kl_shen_LBdatatype_rulesRB)) appl_2
                                                                                                     !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                                     !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_4
                                                                                                     !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_5
                                                                                                     !appl_7 <- kl_V1557tt `pseq` kl_shen_rcons_form kl_V1557tt
                                                                                                     !appl_8 <- klCons (ApplC (wrapNamed "shen.datatype-error" kl_shen_datatype_error)) (Types.Atom Types.Nil)
                                                                                                     !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "function" kl_function)) appl_8
                                                                                                     !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                     !appl_11 <- appl_7 `pseq` (appl_10 `pseq` klCons appl_7 appl_10)
                                                                                                     !appl_12 <- appl_6 `pseq` (appl_11 `pseq` klCons appl_6 appl_11)
                                                                                                     !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_12
                                                                                                     !appl_14 <- appl_13 `pseq` klCons appl_13 (Types.Atom Types.Nil)
                                                                                                     !appl_15 <- appl_1 `pseq` (appl_14 `pseq` klCons appl_1 appl_14)
                                                                                                     appl_15 `pseq` klCons (ApplC (wrapNamed "shen.process-datatype" kl_shen_process_datatype)) appl_15
                                            pat_cond_16 = do do return kl_V1557
                                         in case kl_V1557 of
                                                !(kl_V1557@(Cons (Atom (UnboundSym "datatype"))
                                                                 (!(kl_V1557t@(Cons (!kl_V1557th)
                                                                                    (!kl_V1557tt)))))) -> pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt
                                                !(kl_V1557@(Cons (ApplC (PL "datatype" _))
                                                                 (!(kl_V1557t@(Cons (!kl_V1557th)
                                                                                    (!kl_V1557tt)))))) -> pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt
                                                !(kl_V1557@(Cons (ApplC (Func "datatype" _))
                                                                 (!(kl_V1557t@(Cons (!kl_V1557th)
                                                                                    (!kl_V1557tt)))))) -> pat_cond_0 kl_V1557 kl_V1557t kl_V1557th kl_V1557tt
                                                _ -> pat_cond_16

kl_shen_intern_type :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_intern_type (!kl_V1559) = do !appl_0 <- kl_V1559 `pseq` str kl_V1559
                                     !appl_1 <- appl_0 `pseq` cn (Types.Atom (Types.Str "type#")) appl_0
                                     appl_1 `pseq` intern appl_1

kl_shen_Ats_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_Ats_macro (!kl_V1561) = do let pat_cond_0 kl_V1561 kl_V1561t kl_V1561th kl_V1561tt kl_V1561tth kl_V1561ttt kl_V1561ttth kl_V1561tttt = do !appl_1 <- kl_V1561tt `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) kl_V1561tt
                                                                                                                                                  !appl_2 <- appl_1 `pseq` kl_shen_Ats_macro appl_1
                                                                                                                                                  !appl_3 <- appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil)
                                                                                                                                                  !appl_4 <- kl_V1561th `pseq` (appl_3 `pseq` klCons kl_V1561th appl_3)
                                                                                                                                                  appl_4 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_4
                                       pat_cond_5 = do !kl_if_6 <- let pat_cond_7 kl_V1561 kl_V1561h kl_V1561t = do !kl_if_8 <- let pat_cond_9 = do !kl_if_10 <- let pat_cond_11 kl_V1561t kl_V1561th kl_V1561tt = do !kl_if_12 <- let pat_cond_13 kl_V1561tt kl_V1561tth kl_V1561ttt = do !kl_if_14 <- let pat_cond_15 = do !kl_if_16 <- kl_V1561th `pseq` stringP kl_V1561th
                                                                                                                                                                                                                                                                                                                             case kl_if_16 of
                                                                                                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                            pat_cond_17 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                         in case kl_V1561ttt of
                                                                                                                                                                                                                                                                                                                kl_V1561ttt@(Atom (Nil)) -> pat_cond_15
                                                                                                                                                                                                                                                                                                                _ -> pat_cond_17
                                                                                                                                                                                                                                                                                           case kl_if_14 of
                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                       pat_cond_18 = do do return (Atom (B False))
                                                                                                                                                                                                                                    in case kl_V1561tt of
                                                                                                                                                                                                                                           !(kl_V1561tt@(Cons (!kl_V1561tth)
                                                                                                                                                                                                                                                              (!kl_V1561ttt))) -> pat_cond_13 kl_V1561tt kl_V1561tth kl_V1561ttt
                                                                                                                                                                                                                                           _ -> pat_cond_18
                                                                                                                                                                                                                      case kl_if_12 of
                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                     pat_cond_19 = do do return (Atom (B False))
                                                                                                                                                                  in case kl_V1561t of
                                                                                                                                                                         !(kl_V1561t@(Cons (!kl_V1561th)
                                                                                                                                                                                           (!kl_V1561tt))) -> pat_cond_11 kl_V1561t kl_V1561th kl_V1561tt
                                                                                                                                                                         _ -> pat_cond_19
                                                                                                                                                    case kl_if_10 of
                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                    pat_cond_20 = do do return (Atom (B False))
                                                                                                                                 in case kl_V1561h of
                                                                                                                                        kl_V1561h@(Atom (UnboundSym "@s")) -> pat_cond_9
                                                                                                                                        kl_V1561h@(ApplC (PL "@s"
                                                                                                                                                             _)) -> pat_cond_9
                                                                                                                                        kl_V1561h@(ApplC (Func "@s"
                                                                                                                                                               _)) -> pat_cond_9
                                                                                                                                        _ -> pat_cond_20
                                                                                                                    case kl_if_8 of
                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                        _ -> throwError "if: expected boolean"
                                                                       pat_cond_21 = do do return (Atom (B False))
                                                                    in case kl_V1561 of
                                                                           !(kl_V1561@(Cons (!kl_V1561h)
                                                                                            (!kl_V1561t))) -> pat_cond_7 kl_V1561 kl_V1561h kl_V1561t
                                                                           _ -> pat_cond_21
                                                       case kl_if_6 of
                                                           Atom (B (True)) -> do let !appl_22 = ApplC (Func "lambda" (Context (\(!kl_E) -> do !appl_23 <- kl_E `pseq` kl_length kl_E
                                                                                                                                              !kl_if_24 <- appl_23 `pseq` greaterThan appl_23 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                              case kl_if_24 of
                                                                                                                                                  Atom (B (True)) -> do !appl_25 <- kl_V1561 `pseq` tl kl_V1561
                                                                                                                                                                        !appl_26 <- appl_25 `pseq` tl appl_25
                                                                                                                                                                        !appl_27 <- kl_E `pseq` (appl_26 `pseq` kl_append kl_E appl_26)
                                                                                                                                                                        !appl_28 <- appl_27 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_27
                                                                                                                                                                        appl_28 `pseq` kl_shen_Ats_macro appl_28
                                                                                                                                                  Atom (B (False)) -> do do return kl_V1561
                                                                                                                                                  _ -> throwError "if: expected boolean")))
                                                                                 !appl_29 <- kl_V1561 `pseq` tl kl_V1561
                                                                                 !appl_30 <- appl_29 `pseq` hd appl_29
                                                                                 !appl_31 <- appl_30 `pseq` kl_explode appl_30
                                                                                 appl_31 `pseq` applyWrapper appl_22 [appl_31]
                                                           Atom (B (False)) -> do do return kl_V1561
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V1561 of
                                           !(kl_V1561@(Cons (Atom (UnboundSym "@s"))
                                                            (!(kl_V1561t@(Cons (!kl_V1561th)
                                                                               (!(kl_V1561tt@(Cons (!kl_V1561tth)
                                                                                                   (!(kl_V1561ttt@(Cons (!kl_V1561ttth)
                                                                                                                        (!kl_V1561tttt)))))))))))) -> pat_cond_0 kl_V1561 kl_V1561t kl_V1561th kl_V1561tt kl_V1561tth kl_V1561ttt kl_V1561ttth kl_V1561tttt
                                           !(kl_V1561@(Cons (ApplC (PL "@s" _))
                                                            (!(kl_V1561t@(Cons (!kl_V1561th)
                                                                               (!(kl_V1561tt@(Cons (!kl_V1561tth)
                                                                                                   (!(kl_V1561ttt@(Cons (!kl_V1561ttth)
                                                                                                                        (!kl_V1561tttt)))))))))))) -> pat_cond_0 kl_V1561 kl_V1561t kl_V1561th kl_V1561tt kl_V1561tth kl_V1561ttt kl_V1561ttth kl_V1561tttt
                                           !(kl_V1561@(Cons (ApplC (Func "@s" _))
                                                            (!(kl_V1561t@(Cons (!kl_V1561th)
                                                                               (!(kl_V1561tt@(Cons (!kl_V1561tth)
                                                                                                   (!(kl_V1561ttt@(Cons (!kl_V1561ttth)
                                                                                                                        (!kl_V1561tttt)))))))))))) -> pat_cond_0 kl_V1561 kl_V1561t kl_V1561th kl_V1561tt kl_V1561tth kl_V1561ttt kl_V1561ttth kl_V1561tttt
                                           _ -> pat_cond_5

kl_shen_synonyms_macro :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_synonyms_macro (!kl_V1563) = do let pat_cond_0 kl_V1563 kl_V1563t = do !appl_1 <- kl_V1563t `pseq` kl_shen_curry_synonyms kl_V1563t
                                                                               !appl_2 <- appl_1 `pseq` kl_shen_rcons_form appl_1
                                                                               !appl_3 <- appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil)
                                                                               appl_3 `pseq` klCons (ApplC (wrapNamed "shen.synonyms-help" kl_shen_synonyms_help)) appl_3
                                            pat_cond_4 = do do return kl_V1563
                                         in case kl_V1563 of
                                                !(kl_V1563@(Cons (Atom (UnboundSym "synonyms"))
                                                                 (!kl_V1563t))) -> pat_cond_0 kl_V1563 kl_V1563t
                                                !(kl_V1563@(Cons (ApplC (PL "synonyms" _))
                                                                 (!kl_V1563t))) -> pat_cond_0 kl_V1563 kl_V1563t
                                                !(kl_V1563@(Cons (ApplC (Func "synonyms" _))
                                                                 (!kl_V1563t))) -> pat_cond_0 kl_V1563 kl_V1563t
                                                _ -> pat_cond_4

kl_shen_curry_synonyms :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_curry_synonyms (!kl_V1565) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_curry_type kl_X)))
                                        appl_0 `pseq` (kl_V1565 `pseq` kl_map appl_0 kl_V1565)

kl_shen_nl_macro :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_nl_macro (!kl_V1567) = do let pat_cond_0 kl_V1567 = do !appl_1 <- klCons (Types.Atom (Types.N (Types.KI 1))) (Types.Atom Types.Nil)
                                                               appl_1 `pseq` klCons (ApplC (wrapNamed "nl" kl_nl)) appl_1
                                      pat_cond_2 = do do return kl_V1567
                                   in case kl_V1567 of
                                          !(kl_V1567@(Cons (Atom (UnboundSym "nl"))
                                                           (Atom (Nil)))) -> pat_cond_0 kl_V1567
                                          !(kl_V1567@(Cons (ApplC (PL "nl" _))
                                                           (Atom (Nil)))) -> pat_cond_0 kl_V1567
                                          !(kl_V1567@(Cons (ApplC (Func "nl" _))
                                                           (Atom (Nil)))) -> pat_cond_0 kl_V1567
                                          _ -> pat_cond_2

kl_shen_assoc_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_assoc_macro (!kl_V1569) = do !kl_if_0 <- let pat_cond_1 kl_V1569 kl_V1569h kl_V1569t = do !kl_if_2 <- let pat_cond_3 kl_V1569t kl_V1569th kl_V1569tt = do !kl_if_4 <- let pat_cond_5 kl_V1569tt kl_V1569tth kl_V1569ttt = do !kl_if_6 <- let pat_cond_7 kl_V1569ttt kl_V1569ttth kl_V1569tttt = do !appl_8 <- klCons (ApplC (wrapNamed "do" kl_do)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                           !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_8
                                                                                                                                                                                                                                                                                                           !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_9
                                                                                                                                                                                                                                                                                                           !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.UnboundSym "or")) appl_10
                                                                                                                                                                                                                                                                                                           !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_11
                                                                                                                                                                                                                                                                                                           !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_12
                                                                                                                                                                                                                                                                                                           !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_13
                                                                                                                                                                                                                                                                                                           !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_14
                                                                                                                                                                                                                                                                                                           !kl_if_16 <- kl_V1569h `pseq` (appl_15 `pseq` kl_elementP kl_V1569h appl_15)
                                                                                                                                                                                                                                                                                                           case kl_if_16 of
                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                     pat_cond_17 = do do return (Atom (B False))
                                                                                                                                                                                                                                                  in case kl_V1569ttt of
                                                                                                                                                                                                                                                         !(kl_V1569ttt@(Cons (!kl_V1569ttth)
                                                                                                                                                                                                                                                                             (!kl_V1569tttt))) -> pat_cond_7 kl_V1569ttt kl_V1569ttth kl_V1569tttt
                                                                                                                                                                                                                                                         _ -> pat_cond_17
                                                                                                                                                                                                                                     case kl_if_6 of
                                                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                                                  pat_cond_18 = do do return (Atom (B False))
                                                                                                                                                                               in case kl_V1569tt of
                                                                                                                                                                                      !(kl_V1569tt@(Cons (!kl_V1569tth)
                                                                                                                                                                                                         (!kl_V1569ttt))) -> pat_cond_5 kl_V1569tt kl_V1569tth kl_V1569ttt
                                                                                                                                                                                      _ -> pat_cond_18
                                                                                                                                                                  case kl_if_4 of
                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                  pat_cond_19 = do do return (Atom (B False))
                                                                                                               in case kl_V1569t of
                                                                                                                      !(kl_V1569t@(Cons (!kl_V1569th)
                                                                                                                                        (!kl_V1569tt))) -> pat_cond_3 kl_V1569t kl_V1569th kl_V1569tt
                                                                                                                      _ -> pat_cond_19
                                                                                                  case kl_if_2 of
                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                      _ -> throwError "if: expected boolean"
                                                     pat_cond_20 = do do return (Atom (B False))
                                                  in case kl_V1569 of
                                                         !(kl_V1569@(Cons (!kl_V1569h)
                                                                          (!kl_V1569t))) -> pat_cond_1 kl_V1569 kl_V1569h kl_V1569t
                                                         _ -> pat_cond_20
                                     case kl_if_0 of
                                         Atom (B (True)) -> do !appl_21 <- kl_V1569 `pseq` hd kl_V1569
                                                               !appl_22 <- kl_V1569 `pseq` tl kl_V1569
                                                               !appl_23 <- appl_22 `pseq` hd appl_22
                                                               !appl_24 <- kl_V1569 `pseq` hd kl_V1569
                                                               !appl_25 <- kl_V1569 `pseq` tl kl_V1569
                                                               !appl_26 <- appl_25 `pseq` tl appl_25
                                                               !appl_27 <- appl_24 `pseq` (appl_26 `pseq` klCons appl_24 appl_26)
                                                               !appl_28 <- appl_27 `pseq` kl_shen_assoc_macro appl_27
                                                               !appl_29 <- appl_28 `pseq` klCons appl_28 (Types.Atom Types.Nil)
                                                               !appl_30 <- appl_23 `pseq` (appl_29 `pseq` klCons appl_23 appl_29)
                                                               appl_21 `pseq` (appl_30 `pseq` klCons appl_21 appl_30)
                                         Atom (B (False)) -> do do return kl_V1569
                                         _ -> throwError "if: expected boolean"

kl_shen_let_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_let_macro (!kl_V1571) = do let pat_cond_0 kl_V1571 kl_V1571t kl_V1571th kl_V1571tt kl_V1571tth kl_V1571ttt kl_V1571ttth kl_V1571tttt kl_V1571tttth kl_V1571ttttt = do !appl_1 <- kl_V1571ttt `pseq` klCons (Types.Atom (Types.UnboundSym "let")) kl_V1571ttt
                                                                                                                                                                              !appl_2 <- appl_1 `pseq` kl_shen_let_macro appl_1
                                                                                                                                                                              !appl_3 <- appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil)
                                                                                                                                                                              !appl_4 <- kl_V1571tth `pseq` (appl_3 `pseq` klCons kl_V1571tth appl_3)
                                                                                                                                                                              !appl_5 <- kl_V1571th `pseq` (appl_4 `pseq` klCons kl_V1571th appl_4)
                                                                                                                                                                              appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_5
                                       pat_cond_6 = do do return kl_V1571
                                    in case kl_V1571 of
                                           !(kl_V1571@(Cons (Atom (UnboundSym "let"))
                                                            (!(kl_V1571t@(Cons (!kl_V1571th)
                                                                               (!(kl_V1571tt@(Cons (!kl_V1571tth)
                                                                                                   (!(kl_V1571ttt@(Cons (!kl_V1571ttth)
                                                                                                                        (!(kl_V1571tttt@(Cons (!kl_V1571tttth)
                                                                                                                                              (!kl_V1571ttttt))))))))))))))) -> pat_cond_0 kl_V1571 kl_V1571t kl_V1571th kl_V1571tt kl_V1571tth kl_V1571ttt kl_V1571ttth kl_V1571tttt kl_V1571tttth kl_V1571ttttt
                                           !(kl_V1571@(Cons (ApplC (PL "let" _))
                                                            (!(kl_V1571t@(Cons (!kl_V1571th)
                                                                               (!(kl_V1571tt@(Cons (!kl_V1571tth)
                                                                                                   (!(kl_V1571ttt@(Cons (!kl_V1571ttth)
                                                                                                                        (!(kl_V1571tttt@(Cons (!kl_V1571tttth)
                                                                                                                                              (!kl_V1571ttttt))))))))))))))) -> pat_cond_0 kl_V1571 kl_V1571t kl_V1571th kl_V1571tt kl_V1571tth kl_V1571ttt kl_V1571ttth kl_V1571tttt kl_V1571tttth kl_V1571ttttt
                                           !(kl_V1571@(Cons (ApplC (Func "let" _))
                                                            (!(kl_V1571t@(Cons (!kl_V1571th)
                                                                               (!(kl_V1571tt@(Cons (!kl_V1571tth)
                                                                                                   (!(kl_V1571ttt@(Cons (!kl_V1571ttth)
                                                                                                                        (!(kl_V1571tttt@(Cons (!kl_V1571tttth)
                                                                                                                                              (!kl_V1571ttttt))))))))))))))) -> pat_cond_0 kl_V1571 kl_V1571t kl_V1571th kl_V1571tt kl_V1571tth kl_V1571ttt kl_V1571ttth kl_V1571tttt kl_V1571tttth kl_V1571ttttt
                                           _ -> pat_cond_6

kl_shen_abs_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_abs_macro (!kl_V1573) = do let pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt = do !appl_1 <- kl_V1573tt `pseq` klCons (Types.Atom (Types.UnboundSym "/.")) kl_V1573tt
                                                                                                                                                  !appl_2 <- appl_1 `pseq` kl_shen_abs_macro appl_1
                                                                                                                                                  !appl_3 <- appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil)
                                                                                                                                                  !appl_4 <- kl_V1573th `pseq` (appl_3 `pseq` klCons kl_V1573th appl_3)
                                                                                                                                                  appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_4
                                       pat_cond_5 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth = do kl_V1573t `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) kl_V1573t
                                       pat_cond_6 = do do return kl_V1573
                                    in case kl_V1573 of
                                           !(kl_V1573@(Cons (Atom (UnboundSym "/."))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (!(kl_V1573ttt@(Cons (!kl_V1573ttth)
                                                                                                                        (!kl_V1573tttt)))))))))))) -> pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt
                                           !(kl_V1573@(Cons (ApplC (PL "/." _))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (!(kl_V1573ttt@(Cons (!kl_V1573ttth)
                                                                                                                        (!kl_V1573tttt)))))))))))) -> pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt
                                           !(kl_V1573@(Cons (ApplC (Func "/." _))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (!(kl_V1573ttt@(Cons (!kl_V1573ttth)
                                                                                                                        (!kl_V1573tttt)))))))))))) -> pat_cond_0 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth kl_V1573ttt kl_V1573ttth kl_V1573tttt
                                           !(kl_V1573@(Cons (Atom (UnboundSym "/."))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (Atom (Nil)))))))))) -> pat_cond_5 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth
                                           !(kl_V1573@(Cons (ApplC (PL "/." _))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (Atom (Nil)))))))))) -> pat_cond_5 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth
                                           !(kl_V1573@(Cons (ApplC (Func "/." _))
                                                            (!(kl_V1573t@(Cons (!kl_V1573th)
                                                                               (!(kl_V1573tt@(Cons (!kl_V1573tth)
                                                                                                   (Atom (Nil)))))))))) -> pat_cond_5 kl_V1573 kl_V1573t kl_V1573th kl_V1573tt kl_V1573tth
                                           _ -> pat_cond_6

kl_shen_cases_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_cases_macro (!kl_V1577) = do let pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt = do return kl_V1577tth
                                         pat_cond_1 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth = do !appl_2 <- klCons (Types.Atom (Types.Str "error: cases exhausted")) (Types.Atom Types.Nil)
                                                                                                              !appl_3 <- appl_2 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_2
                                                                                                              !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                                              !appl_5 <- kl_V1577tth `pseq` (appl_4 `pseq` klCons kl_V1577tth appl_4)
                                                                                                              !appl_6 <- kl_V1577th `pseq` (appl_5 `pseq` klCons kl_V1577th appl_5)
                                                                                                              appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_6
                                         pat_cond_7 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth kl_V1577ttt = do !appl_8 <- kl_V1577ttt `pseq` klCons (Types.Atom (Types.UnboundSym "cases")) kl_V1577ttt
                                                                                                                          !appl_9 <- appl_8 `pseq` kl_shen_cases_macro appl_8
                                                                                                                          !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                                          !appl_11 <- kl_V1577tth `pseq` (appl_10 `pseq` klCons kl_V1577tth appl_10)
                                                                                                                          !appl_12 <- kl_V1577th `pseq` (appl_11 `pseq` klCons kl_V1577th appl_11)
                                                                                                                          appl_12 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_12
                                         pat_cond_13 kl_V1577 kl_V1577t kl_V1577th = do simpleError (Types.Atom (Types.Str "error: odd number of case elements\n"))
                                         pat_cond_14 = do do return kl_V1577
                                      in case kl_V1577 of
                                             !(kl_V1577@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1577t@(Cons (Atom (UnboundSym "true"))
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1577t@(Cons (Atom (B (True)))
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1577t@(Cons (Atom (UnboundSym "true"))
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1577t@(Cons (Atom (B (True)))
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1577t@(Cons (Atom (UnboundSym "true"))
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1577t@(Cons (Atom (B (True)))
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_0 kl_V1577 kl_V1577t kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (Atom (Nil)))))))))) -> pat_cond_1 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth
                                             !(kl_V1577@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (Atom (Nil)))))))))) -> pat_cond_1 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth
                                             !(kl_V1577@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (Atom (Nil)))))))))) -> pat_cond_1 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth
                                             !(kl_V1577@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_7 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_7 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (!(kl_V1577tt@(Cons (!kl_V1577tth)
                                                                                                     (!kl_V1577ttt))))))))) -> pat_cond_7 kl_V1577 kl_V1577t kl_V1577th kl_V1577tt kl_V1577tth kl_V1577ttt
                                             !(kl_V1577@(Cons (Atom (UnboundSym "cases"))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (Atom (Nil))))))) -> pat_cond_13 kl_V1577 kl_V1577t kl_V1577th
                                             !(kl_V1577@(Cons (ApplC (PL "cases" _))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (Atom (Nil))))))) -> pat_cond_13 kl_V1577 kl_V1577t kl_V1577th
                                             !(kl_V1577@(Cons (ApplC (Func "cases" _))
                                                              (!(kl_V1577t@(Cons (!kl_V1577th)
                                                                                 (Atom (Nil))))))) -> pat_cond_13 kl_V1577 kl_V1577t kl_V1577th
                                             _ -> pat_cond_14

kl_shen_timer_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_timer_macro (!kl_V1579) = do let pat_cond_0 kl_V1579 kl_V1579t kl_V1579th = do !appl_1 <- klCons (Types.Atom (Types.UnboundSym "run")) (Types.Atom Types.Nil)
                                                                                       !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_1
                                                                                       !appl_3 <- klCons (Types.Atom (Types.UnboundSym "run")) (Types.Atom Types.Nil)
                                                                                       !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_3
                                                                                       !appl_5 <- klCons (Types.Atom (Types.UnboundSym "Start")) (Types.Atom Types.Nil)
                                                                                       !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_5
                                                                                       !appl_7 <- appl_6 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_6
                                                                                       !appl_8 <- klCons (Types.Atom (Types.UnboundSym "Time")) (Types.Atom Types.Nil)
                                                                                       !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "str" str)) appl_8
                                                                                       !appl_10 <- klCons (Types.Atom (Types.Str " secs\n")) (Types.Atom Types.Nil)
                                                                                       !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                                                       !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_11
                                                                                       !appl_13 <- appl_12 `pseq` klCons appl_12 (Types.Atom Types.Nil)
                                                                                       !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.Str "\nrun time: ")) appl_13
                                                                                       !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_14
                                                                                       !appl_16 <- klCons (ApplC (PL "stoutput" kl_stoutput)) (Types.Atom Types.Nil)
                                                                                       !appl_17 <- appl_16 `pseq` klCons appl_16 (Types.Atom Types.Nil)
                                                                                       !appl_18 <- appl_15 `pseq` (appl_17 `pseq` klCons appl_15 appl_17)
                                                                                       !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_18
                                                                                       !appl_20 <- klCons (Types.Atom (Types.UnboundSym "Result")) (Types.Atom Types.Nil)
                                                                                       !appl_21 <- appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)
                                                                                       !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.UnboundSym "Message")) appl_21
                                                                                       !appl_23 <- appl_7 `pseq` (appl_22 `pseq` klCons appl_7 appl_22)
                                                                                       !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "Time")) appl_23
                                                                                       !appl_25 <- appl_4 `pseq` (appl_24 `pseq` klCons appl_4 appl_24)
                                                                                       !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_25
                                                                                       !appl_27 <- kl_V1579th `pseq` (appl_26 `pseq` klCons kl_V1579th appl_26)
                                                                                       !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_27
                                                                                       !appl_29 <- appl_2 `pseq` (appl_28 `pseq` klCons appl_2 appl_28)
                                                                                       !appl_30 <- appl_29 `pseq` klCons (Types.Atom (Types.UnboundSym "Start")) appl_29
                                                                                       !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_30
                                                                                       appl_31 `pseq` kl_shen_let_macro appl_31
                                         pat_cond_32 = do do return kl_V1579
                                      in case kl_V1579 of
                                             !(kl_V1579@(Cons (Atom (UnboundSym "time"))
                                                              (!(kl_V1579t@(Cons (!kl_V1579th)
                                                                                 (Atom (Nil))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579th
                                             !(kl_V1579@(Cons (ApplC (PL "time" _))
                                                              (!(kl_V1579t@(Cons (!kl_V1579th)
                                                                                 (Atom (Nil))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579th
                                             !(kl_V1579@(Cons (ApplC (Func "time" _))
                                                              (!(kl_V1579t@(Cons (!kl_V1579th)
                                                                                 (Atom (Nil))))))) -> pat_cond_0 kl_V1579 kl_V1579t kl_V1579th
                                             _ -> pat_cond_32

kl_shen_tuple_up :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_tuple_up (!kl_V1581) = do let pat_cond_0 kl_V1581 kl_V1581h kl_V1581t = do !appl_1 <- kl_V1581t `pseq` kl_shen_tuple_up kl_V1581t
                                                                                   !appl_2 <- appl_1 `pseq` klCons appl_1 (Types.Atom Types.Nil)
                                                                                   !appl_3 <- kl_V1581h `pseq` (appl_2 `pseq` klCons kl_V1581h appl_2)
                                                                                   appl_3 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_3
                                      pat_cond_4 = do do return kl_V1581
                                   in case kl_V1581 of
                                          !(kl_V1581@(Cons (!kl_V1581h)
                                                           (!kl_V1581t))) -> pat_cond_0 kl_V1581 kl_V1581h kl_V1581t
                                          _ -> pat_cond_4

kl_shen_putDivget_macro :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_putDivget_macro (!kl_V1583) = do let pat_cond_0 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth kl_V1583ttt kl_V1583ttth = do !appl_1 <- klCons (Types.Atom (Types.UnboundSym "*property-vector*")) (Types.Atom Types.Nil)
                                                                                                                                           !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_1
                                                                                                                                           !appl_3 <- appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil)
                                                                                                                                           !appl_4 <- kl_V1583ttth `pseq` (appl_3 `pseq` klCons kl_V1583ttth appl_3)
                                                                                                                                           !appl_5 <- kl_V1583tth `pseq` (appl_4 `pseq` klCons kl_V1583tth appl_4)
                                                                                                                                           !appl_6 <- kl_V1583th `pseq` (appl_5 `pseq` klCons kl_V1583th appl_5)
                                                                                                                                           appl_6 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_6
                                             pat_cond_7 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth = do !appl_8 <- klCons (Types.Atom (Types.UnboundSym "*property-vector*")) (Types.Atom Types.Nil)
                                                                                                                  !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_8
                                                                                                                  !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                                  !appl_11 <- kl_V1583tth `pseq` (appl_10 `pseq` klCons kl_V1583tth appl_10)
                                                                                                                  !appl_12 <- kl_V1583th `pseq` (appl_11 `pseq` klCons kl_V1583th appl_11)
                                                                                                                  appl_12 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_12
                                             pat_cond_13 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth = do !appl_14 <- klCons (Types.Atom (Types.UnboundSym "*property-vector*")) (Types.Atom Types.Nil)
                                                                                                                   !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_14
                                                                                                                   !appl_16 <- appl_15 `pseq` klCons appl_15 (Types.Atom Types.Nil)
                                                                                                                   !appl_17 <- kl_V1583tth `pseq` (appl_16 `pseq` klCons kl_V1583tth appl_16)
                                                                                                                   !appl_18 <- kl_V1583th `pseq` (appl_17 `pseq` klCons kl_V1583th appl_17)
                                                                                                                   appl_18 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_18
                                             pat_cond_19 = do do return kl_V1583
                                          in case kl_V1583 of
                                                 !(kl_V1583@(Cons (Atom (UnboundSym "put"))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (!(kl_V1583ttt@(Cons (!kl_V1583ttth)
                                                                                                                              (Atom (Nil))))))))))))) -> pat_cond_0 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth kl_V1583ttt kl_V1583ttth
                                                 !(kl_V1583@(Cons (ApplC (PL "put" _))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (!(kl_V1583ttt@(Cons (!kl_V1583ttth)
                                                                                                                              (Atom (Nil))))))))))))) -> pat_cond_0 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth kl_V1583ttt kl_V1583ttth
                                                 !(kl_V1583@(Cons (ApplC (Func "put" _))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (!(kl_V1583ttt@(Cons (!kl_V1583ttth)
                                                                                                                              (Atom (Nil))))))))))))) -> pat_cond_0 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth kl_V1583ttt kl_V1583ttth
                                                 !(kl_V1583@(Cons (Atom (UnboundSym "get"))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (Atom (Nil)))))))))) -> pat_cond_7 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth
                                                 !(kl_V1583@(Cons (ApplC (PL "get" _))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (Atom (Nil)))))))))) -> pat_cond_7 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth
                                                 !(kl_V1583@(Cons (ApplC (Func "get" _))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (Atom (Nil)))))))))) -> pat_cond_7 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth
                                                 !(kl_V1583@(Cons (Atom (UnboundSym "unput"))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (Atom (Nil)))))))))) -> pat_cond_13 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth
                                                 !(kl_V1583@(Cons (ApplC (PL "unput" _))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (Atom (Nil)))))))))) -> pat_cond_13 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth
                                                 !(kl_V1583@(Cons (ApplC (Func "unput" _))
                                                                  (!(kl_V1583t@(Cons (!kl_V1583th)
                                                                                     (!(kl_V1583tt@(Cons (!kl_V1583tth)
                                                                                                         (Atom (Nil)))))))))) -> pat_cond_13 kl_V1583 kl_V1583t kl_V1583th kl_V1583tt kl_V1583tth
                                                 _ -> pat_cond_19

kl_shen_function_macro :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_function_macro (!kl_V1585) = do let pat_cond_0 kl_V1585 kl_V1585t kl_V1585th = do let !aw_1 = Types.Atom (Types.UnboundSym "arity")
                                                                                          !appl_2 <- kl_V1585th `pseq` applyWrapper aw_1 [kl_V1585th]
                                                                                          kl_V1585th `pseq` (appl_2 `pseq` kl_shen_function_abstraction kl_V1585th appl_2)
                                            pat_cond_3 = do do return kl_V1585
                                         in case kl_V1585 of
                                                !(kl_V1585@(Cons (Atom (UnboundSym "function"))
                                                                 (!(kl_V1585t@(Cons (!kl_V1585th)
                                                                                    (Atom (Nil))))))) -> pat_cond_0 kl_V1585 kl_V1585t kl_V1585th
                                                !(kl_V1585@(Cons (ApplC (PL "function" _))
                                                                 (!(kl_V1585t@(Cons (!kl_V1585th)
                                                                                    (Atom (Nil))))))) -> pat_cond_0 kl_V1585 kl_V1585t kl_V1585th
                                                !(kl_V1585@(Cons (ApplC (Func "function" _))
                                                                 (!(kl_V1585t@(Cons (!kl_V1585th)
                                                                                    (Atom (Nil))))))) -> pat_cond_0 kl_V1585 kl_V1585t kl_V1585th
                                                _ -> pat_cond_3

kl_shen_function_abstraction :: Types.KLValue ->
                                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_function_abstraction (!kl_V1588) (!kl_V1589) = do let pat_cond_0 = do !appl_1 <- kl_V1588 `pseq` kl_shen_app kl_V1588 (Types.Atom (Types.Str " has no lambda form\n")) (Types.Atom (Types.UnboundSym "shen.a"))
                                                                              appl_1 `pseq` simpleError appl_1
                                                              pat_cond_2 = do !appl_3 <- kl_V1588 `pseq` klCons kl_V1588 (Types.Atom Types.Nil)
                                                                              appl_3 `pseq` klCons (ApplC (wrapNamed "function" kl_function)) appl_3
                                                              pat_cond_4 = do do kl_V1588 `pseq` (kl_V1589 `pseq` kl_shen_function_abstraction_help kl_V1588 kl_V1589 (Types.Atom Types.Nil))
                                                           in case kl_V1589 of
                                                                  kl_V1589@(Atom (N (KI 0))) -> pat_cond_0
                                                                  kl_V1589@(Atom (N (KI (-1)))) -> pat_cond_2
                                                                  _ -> pat_cond_4

kl_shen_function_abstraction_help :: Types.KLValue ->
                                     Types.KLValue ->
                                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_function_abstraction_help (!kl_V1593) (!kl_V1594) (!kl_V1595) = do let pat_cond_0 = do kl_V1593 `pseq` (kl_V1595 `pseq` klCons kl_V1593 kl_V1595)
                                                                               pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_3 <- kl_V1594 `pseq` Primitives.subtract kl_V1594 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                              !appl_4 <- kl_X `pseq` klCons kl_X (Types.Atom Types.Nil)
                                                                                                                                                              !appl_5 <- kl_V1595 `pseq` (appl_4 `pseq` kl_append kl_V1595 appl_4)
                                                                                                                                                              !appl_6 <- kl_V1593 `pseq` (appl_3 `pseq` (appl_5 `pseq` kl_shen_function_abstraction_help kl_V1593 appl_3 appl_5))
                                                                                                                                                              !appl_7 <- appl_6 `pseq` klCons appl_6 (Types.Atom Types.Nil)
                                                                                                                                                              !appl_8 <- kl_X `pseq` (appl_7 `pseq` klCons kl_X appl_7)
                                                                                                                                                              appl_8 `pseq` klCons (Types.Atom (Types.UnboundSym "/.")) appl_8)))
                                                                                                  !appl_9 <- kl_gensym (Types.Atom (Types.UnboundSym "V"))
                                                                                                  appl_9 `pseq` applyWrapper appl_2 [appl_9]
                                                                            in case kl_V1594 of
                                                                                   kl_V1594@(Atom (N (KI 0))) -> pat_cond_0
                                                                                   _ -> pat_cond_1

kl_undefmacro :: Types.KLValue ->
                 Types.KLContext Types.Env Types.KLValue
kl_undefmacro (!kl_V1597) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_MacroReg) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Pos) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Remove1) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Remove2) -> do return kl_V1597)))
                                                                                                                                                                                                                                  !appl_4 <- value (Types.Atom (Types.UnboundSym "*macros*"))
                                                                                                                                                                                                                                  !appl_5 <- kl_Pos `pseq` (appl_4 `pseq` kl_shen_remove_nth kl_Pos appl_4)
                                                                                                                                                                                                                                  !appl_6 <- appl_5 `pseq` klSet (Types.Atom (Types.UnboundSym "*macros*")) appl_5
                                                                                                                                                                                                                                  appl_6 `pseq` applyWrapper appl_3 [appl_6])))
                                                                                                                                                                !appl_7 <- kl_V1597 `pseq` (kl_MacroReg `pseq` kl_remove kl_V1597 kl_MacroReg)
                                                                                                                                                                !appl_8 <- appl_7 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*macroreg*")) appl_7
                                                                                                                                                                appl_8 `pseq` applyWrapper appl_2 [appl_8])))
                                                                                                  !appl_9 <- kl_V1597 `pseq` (kl_MacroReg `pseq` kl_shen_findpos kl_V1597 kl_MacroReg)
                                                                                                  appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                               !appl_10 <- value (Types.Atom (Types.UnboundSym "shen.*macroreg*"))
                               appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_findpos :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_findpos (!kl_V1607) (!kl_V1608) = do let pat_cond_0 = do !appl_1 <- kl_V1607 `pseq` kl_shen_app kl_V1607 (Types.Atom (Types.Str " is not a macro\n")) (Types.Atom (Types.UnboundSym "shen.a"))
                                                                 appl_1 `pseq` simpleError appl_1
                                                 pat_cond_2 kl_V1608 kl_V1608h kl_V1608t = do return (Types.Atom (Types.N (Types.KI 1)))
                                                 pat_cond_3 kl_V1608 kl_V1608h kl_V1608t = do !appl_4 <- kl_V1607 `pseq` (kl_V1608t `pseq` kl_shen_findpos kl_V1607 kl_V1608t)
                                                                                              appl_4 `pseq` add (Types.Atom (Types.N (Types.KI 1))) appl_4
                                                 pat_cond_5 = do do kl_shen_f_error (ApplC (wrapNamed "shen.findpos" kl_shen_findpos))
                                              in case kl_V1608 of
                                                     kl_V1608@(Atom (Nil)) -> pat_cond_0
                                                     !(kl_V1608@(Cons (!kl_V1608h)
                                                                      (!kl_V1608t))) | eqCore kl_V1608h kl_V1607 -> pat_cond_2 kl_V1608 kl_V1608h kl_V1608t
                                                     !(kl_V1608@(Cons (!kl_V1608h)
                                                                      (!kl_V1608t))) -> pat_cond_3 kl_V1608 kl_V1608h kl_V1608t
                                                     _ -> pat_cond_5

kl_shen_remove_nth :: Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_remove_nth (!kl_V1613) (!kl_V1614) = do !kl_if_0 <- let pat_cond_1 = do let pat_cond_2 kl_V1614 kl_V1614h kl_V1614t = do return (Atom (B True))
                                                                                    pat_cond_3 = do do return (Atom (B False))
                                                                                 in case kl_V1614 of
                                                                                        !(kl_V1614@(Cons (!kl_V1614h)
                                                                                                         (!kl_V1614t))) -> pat_cond_2 kl_V1614 kl_V1614h kl_V1614t
                                                                                        _ -> pat_cond_3
                                                                pat_cond_4 = do do return (Atom (B False))
                                                             in case kl_V1613 of
                                                                    kl_V1613@(Atom (N (KI 1))) -> pat_cond_1
                                                                    _ -> pat_cond_4
                                                case kl_if_0 of
                                                    Atom (B (True)) -> do kl_V1614 `pseq` tl kl_V1614
                                                    Atom (B (False)) -> do let pat_cond_5 kl_V1614 kl_V1614h kl_V1614t = do !appl_6 <- kl_V1613 `pseq` Primitives.subtract kl_V1613 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                            !appl_7 <- appl_6 `pseq` (kl_V1614t `pseq` kl_shen_remove_nth appl_6 kl_V1614t)
                                                                                                                            kl_V1614h `pseq` (appl_7 `pseq` klCons kl_V1614h appl_7)
                                                                               pat_cond_8 = do do kl_shen_f_error (ApplC (wrapNamed "shen.remove-nth" kl_shen_remove_nth))
                                                                            in case kl_V1614 of
                                                                                   !(kl_V1614@(Cons (!kl_V1614h)
                                                                                                    (!kl_V1614t))) -> pat_cond_5 kl_V1614 kl_V1614h kl_V1614t
                                                                                   _ -> pat_cond_8
                                                    _ -> throwError "if: expected boolean"

expr10 :: Types.KLContext Types.Env Types.KLValue
expr10 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
