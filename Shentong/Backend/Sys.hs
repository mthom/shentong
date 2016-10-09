{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Backend.Sys where

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

kl_thaw :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_thaw (!kl_V2614) = do applyWrapper kl_V2614 []

kl_eval :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_eval (!kl_V2616) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Macroexpand) -> do !kl_if_1 <- kl_Macroexpand `pseq` kl_shen_packagedP kl_Macroexpand
                                                                                               case kl_if_1 of
                                                                                                   Atom (B (True)) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_eval_without_macros kl_Z)))
                                                                                                                         !appl_3 <- kl_Macroexpand `pseq` kl_shen_package_contents kl_Macroexpand
                                                                                                                         appl_2 `pseq` (appl_3 `pseq` kl_map appl_2 appl_3)
                                                                                                   Atom (B (False)) -> do do kl_Macroexpand `pseq` kl_shen_eval_without_macros kl_Macroexpand
                                                                                                   _ -> throwError "if: expected boolean")))
                         let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do let !aw_5 = Types.Atom (Types.UnboundSym "macroexpand")
                                                                                     kl_Y `pseq` applyWrapper aw_5 [kl_Y])))
                         !appl_6 <- appl_4 `pseq` (kl_V2616 `pseq` kl_shen_walk appl_4 kl_V2616)
                         appl_6 `pseq` applyWrapper appl_0 [appl_6]

kl_shen_eval_without_macros :: Types.KLValue ->
                               Types.KLContext Types.Env Types.KLValue
kl_shen_eval_without_macros (!kl_V2618) = do !appl_0 <- kl_V2618 `pseq` kl_shen_proc_inputPlus kl_V2618
                                             !appl_1 <- appl_0 `pseq` kl_shen_elim_def appl_0
                                             appl_1 `pseq` evalKL appl_1

kl_shen_proc_inputPlus :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_proc_inputPlus (!kl_V2620) = do let pat_cond_0 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth = do let !aw_1 = Types.Atom (Types.UnboundSym "shen.rcons_form")
                                                                                                                 !appl_2 <- kl_V2620th `pseq` applyWrapper aw_1 [kl_V2620th]
                                                                                                                 !appl_3 <- appl_2 `pseq` (kl_V2620tt `pseq` klCons appl_2 kl_V2620tt)
                                                                                                                 appl_3 `pseq` klCons (Types.Atom (Types.UnboundSym "input+")) appl_3
                                            pat_cond_4 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth = do let !aw_5 = Types.Atom (Types.UnboundSym "shen.rcons_form")
                                                                                                                 !appl_6 <- kl_V2620th `pseq` applyWrapper aw_5 [kl_V2620th]
                                                                                                                 !appl_7 <- appl_6 `pseq` (kl_V2620tt `pseq` klCons appl_6 kl_V2620tt)
                                                                                                                 appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.read+")) appl_7
                                            pat_cond_8 kl_V2620 kl_V2620h kl_V2620t = do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_proc_inputPlus kl_Z)))
                                                                                         appl_9 `pseq` (kl_V2620 `pseq` kl_map appl_9 kl_V2620)
                                            pat_cond_10 = do do return kl_V2620
                                         in case kl_V2620 of
                                                !(kl_V2620@(Cons (Atom (UnboundSym "input+"))
                                                                 (!(kl_V2620t@(Cons (!kl_V2620th)
                                                                                    (!(kl_V2620tt@(Cons (!kl_V2620tth)
                                                                                                        (Atom (Nil)))))))))) -> pat_cond_0 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth
                                                !(kl_V2620@(Cons (ApplC (PL "input+" _))
                                                                 (!(kl_V2620t@(Cons (!kl_V2620th)
                                                                                    (!(kl_V2620tt@(Cons (!kl_V2620tth)
                                                                                                        (Atom (Nil)))))))))) -> pat_cond_0 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth
                                                !(kl_V2620@(Cons (ApplC (Func "input+" _))
                                                                 (!(kl_V2620t@(Cons (!kl_V2620th)
                                                                                    (!(kl_V2620tt@(Cons (!kl_V2620tth)
                                                                                                        (Atom (Nil)))))))))) -> pat_cond_0 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth
                                                !(kl_V2620@(Cons (Atom (UnboundSym "shen.read+"))
                                                                 (!(kl_V2620t@(Cons (!kl_V2620th)
                                                                                    (!(kl_V2620tt@(Cons (!kl_V2620tth)
                                                                                                        (Atom (Nil)))))))))) -> pat_cond_4 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth
                                                !(kl_V2620@(Cons (ApplC (PL "shen.read+" _))
                                                                 (!(kl_V2620t@(Cons (!kl_V2620th)
                                                                                    (!(kl_V2620tt@(Cons (!kl_V2620tth)
                                                                                                        (Atom (Nil)))))))))) -> pat_cond_4 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth
                                                !(kl_V2620@(Cons (ApplC (Func "shen.read+" _))
                                                                 (!(kl_V2620t@(Cons (!kl_V2620th)
                                                                                    (!(kl_V2620tt@(Cons (!kl_V2620tth)
                                                                                                        (Atom (Nil)))))))))) -> pat_cond_4 kl_V2620 kl_V2620t kl_V2620th kl_V2620tt kl_V2620tth
                                                !(kl_V2620@(Cons (!kl_V2620h)
                                                                 (!kl_V2620t))) -> pat_cond_8 kl_V2620 kl_V2620h kl_V2620t
                                                _ -> pat_cond_10

kl_shen_elim_def :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_elim_def (!kl_V2622) = do let pat_cond_0 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt = do kl_V2622th `pseq` (kl_V2622tt `pseq` kl_shen_shen_RBkl kl_V2622th kl_V2622tt)
                                      pat_cond_1 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt = do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Default) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Def) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_MacroAdd) -> do return kl_Def)))
                                                                                                                                                                                                                               !appl_5 <- kl_V2622th `pseq` kl_shen_add_macro kl_V2622th
                                                                                                                                                                                                                               appl_5 `pseq` applyWrapper appl_4 [appl_5])))
                                                                                                                                                                 !appl_6 <- kl_V2622tt `pseq` (kl_Default `pseq` kl_append kl_V2622tt kl_Default)
                                                                                                                                                                 !appl_7 <- kl_V2622th `pseq` (appl_6 `pseq` klCons kl_V2622th appl_6)
                                                                                                                                                                 !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_7
                                                                                                                                                                 !appl_9 <- appl_8 `pseq` kl_shen_elim_def appl_8
                                                                                                                                                                 appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                               !appl_10 <- klCons (Types.Atom (Types.UnboundSym "X")) (Types.Atom Types.Nil)
                                                                                               !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_10
                                                                                               !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_11
                                                                                               appl_12 `pseq` applyWrapper appl_2 [appl_12]
                                      pat_cond_13 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt = do let !aw_14 = Types.Atom (Types.UnboundSym "shen.yacc")
                                                                                                !appl_15 <- kl_V2622 `pseq` applyWrapper aw_14 [kl_V2622]
                                                                                                appl_15 `pseq` kl_shen_elim_def appl_15
                                      pat_cond_16 kl_V2622 kl_V2622h kl_V2622t = do let !appl_17 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_elim_def kl_Z)))
                                                                                    appl_17 `pseq` (kl_V2622 `pseq` kl_map appl_17 kl_V2622)
                                      pat_cond_18 = do do return kl_V2622
                                   in case kl_V2622 of
                                          !(kl_V2622@(Cons (Atom (UnboundSym "define"))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_0 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (ApplC (PL "define" _))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_0 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (ApplC (Func "define" _))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_0 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (Atom (UnboundSym "defmacro"))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_1 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (ApplC (PL "defmacro" _))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_1 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (ApplC (Func "defmacro" _))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_1 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (Atom (UnboundSym "defcc"))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_13 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (ApplC (PL "defcc" _))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_13 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (ApplC (Func "defcc" _))
                                                           (!(kl_V2622t@(Cons (!kl_V2622th)
                                                                              (!kl_V2622tt)))))) -> pat_cond_13 kl_V2622 kl_V2622t kl_V2622th kl_V2622tt
                                          !(kl_V2622@(Cons (!kl_V2622h)
                                                           (!kl_V2622t))) -> pat_cond_16 kl_V2622 kl_V2622h kl_V2622t
                                          _ -> pat_cond_18

kl_shen_add_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_add_macro (!kl_V2624) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_MacroReg) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_NewMacroReg) -> do !kl_if_2 <- kl_MacroReg `pseq` (kl_NewMacroReg `pseq` eq kl_MacroReg kl_NewMacroReg)
                                                                                                                                                                            case kl_if_2 of
                                                                                                                                                                                Atom (B (True)) -> do return (Types.Atom (Types.UnboundSym "shen.skip"))
                                                                                                                                                                                Atom (B (False)) -> do do !appl_3 <- kl_V2624 `pseq` kl_function kl_V2624
                                                                                                                                                                                                          !appl_4 <- value (Types.Atom (Types.UnboundSym "*macros*"))
                                                                                                                                                                                                          !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                                                                                                                          appl_5 `pseq` klSet (Types.Atom (Types.UnboundSym "*macros*")) appl_5
                                                                                                                                                                                _ -> throwError "if: expected boolean")))
                                                                                                      !appl_6 <- value (Types.Atom (Types.UnboundSym "shen.*macroreg*"))
                                                                                                      let !aw_7 = Types.Atom (Types.UnboundSym "adjoin")
                                                                                                      !appl_8 <- kl_V2624 `pseq` (appl_6 `pseq` applyWrapper aw_7 [kl_V2624,
                                                                                                                                                                   appl_6])
                                                                                                      !appl_9 <- appl_8 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*macroreg*")) appl_8
                                                                                                      appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                                   !appl_10 <- value (Types.Atom (Types.UnboundSym "shen.*macroreg*"))
                                   appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_packagedP :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_packagedP (!kl_V2632) = do let pat_cond_0 kl_V2632 kl_V2632t kl_V2632th kl_V2632tt kl_V2632tth kl_V2632ttt = do return (Atom (B True))
                                       pat_cond_1 = do do return (Atom (B False))
                                    in case kl_V2632 of
                                           !(kl_V2632@(Cons (Atom (UnboundSym "package"))
                                                            (!(kl_V2632t@(Cons (!kl_V2632th)
                                                                               (!(kl_V2632tt@(Cons (!kl_V2632tth)
                                                                                                   (!kl_V2632ttt))))))))) -> pat_cond_0 kl_V2632 kl_V2632t kl_V2632th kl_V2632tt kl_V2632tth kl_V2632ttt
                                           !(kl_V2632@(Cons (ApplC (PL "package" _))
                                                            (!(kl_V2632t@(Cons (!kl_V2632th)
                                                                               (!(kl_V2632tt@(Cons (!kl_V2632tth)
                                                                                                   (!kl_V2632ttt))))))))) -> pat_cond_0 kl_V2632 kl_V2632t kl_V2632th kl_V2632tt kl_V2632tth kl_V2632ttt
                                           !(kl_V2632@(Cons (ApplC (Func "package" _))
                                                            (!(kl_V2632t@(Cons (!kl_V2632th)
                                                                               (!(kl_V2632tt@(Cons (!kl_V2632tth)
                                                                                                   (!kl_V2632ttt))))))))) -> pat_cond_0 kl_V2632 kl_V2632t kl_V2632th kl_V2632tt kl_V2632tth kl_V2632ttt
                                           _ -> pat_cond_1

kl_external :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_external (!kl_V2634) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                 kl_V2634 `pseq` (appl_0 `pseq` kl_get kl_V2634 (Types.Atom (Types.UnboundSym "shen.external-symbols")) appl_0)) `catchError` (\(!kl_E) -> do let !aw_1 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                              !appl_2 <- kl_V2634 `pseq` applyWrapper aw_1 [kl_V2634,
                                                                                                                                                                                                                            Types.Atom (Types.Str " has not been used.\n"),
                                                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                                              !appl_3 <- appl_2 `pseq` cn (Types.Atom (Types.Str "package ")) appl_2
                                                                                                                                                                              appl_3 `pseq` simpleError appl_3)

kl_internal :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_internal (!kl_V2636) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                 kl_V2636 `pseq` (appl_0 `pseq` kl_get kl_V2636 (Types.Atom (Types.UnboundSym "shen.internal-symbols")) appl_0)) `catchError` (\(!kl_E) -> do let !aw_1 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                              !appl_2 <- kl_V2636 `pseq` applyWrapper aw_1 [kl_V2636,
                                                                                                                                                                                                                            Types.Atom (Types.Str " has not been used.\n"),
                                                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                                              !appl_3 <- appl_2 `pseq` cn (Types.Atom (Types.Str "package ")) appl_2
                                                                                                                                                                              appl_3 `pseq` simpleError appl_3)

kl_shen_package_contents :: Types.KLValue ->
                            Types.KLContext Types.Env Types.KLValue
kl_shen_package_contents (!kl_V2640) = do let pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt = do return kl_V2640ttt
                                              pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt kl_V2640tth kl_V2640ttt = do let !aw_2 = Types.Atom (Types.UnboundSym "shen.packageh")
                                                                                                                               kl_V2640th `pseq` (kl_V2640tth `pseq` (kl_V2640ttt `pseq` applyWrapper aw_2 [kl_V2640th,
                                                                                                                                                                                                            kl_V2640tth,
                                                                                                                                                                                                            kl_V2640ttt]))
                                              pat_cond_3 = do do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                 applyWrapper aw_4 [ApplC (wrapNamed "shen.package-contents" kl_shen_package_contents)]
                                           in case kl_V2640 of
                                                  !(kl_V2640@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2640t@(Cons (Atom (UnboundSym "null"))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2640t@(Cons (ApplC (PL "null"
                                                                                                 _))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2640t@(Cons (ApplC (Func "null"
                                                                                                   _))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2640t@(Cons (Atom (UnboundSym "null"))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2640t@(Cons (ApplC (PL "null"
                                                                                                 _))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2640t@(Cons (ApplC (Func "null"
                                                                                                   _))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2640t@(Cons (Atom (UnboundSym "null"))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2640t@(Cons (ApplC (PL "null"
                                                                                                 _))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2640t@(Cons (ApplC (Func "null"
                                                                                                   _))
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_0 kl_V2640 kl_V2640t kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (Atom (UnboundSym "package"))
                                                                   (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (PL "package" _))
                                                                   (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  !(kl_V2640@(Cons (ApplC (Func "package" _))
                                                                   (!(kl_V2640t@(Cons (!kl_V2640th)
                                                                                      (!(kl_V2640tt@(Cons (!kl_V2640tth)
                                                                                                          (!kl_V2640ttt))))))))) -> pat_cond_1 kl_V2640 kl_V2640t kl_V2640th kl_V2640tt kl_V2640tth kl_V2640ttt
                                                  _ -> pat_cond_3

kl_shen_walk :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_walk (!kl_V2643) (!kl_V2644) = do let pat_cond_0 kl_V2644 kl_V2644h kl_V2644t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_V2643 `pseq` (kl_Z `pseq` kl_shen_walk kl_V2643 kl_Z))))
                                                                                           !appl_2 <- appl_1 `pseq` (kl_V2644 `pseq` kl_map appl_1 kl_V2644)
                                                                                           appl_2 `pseq` applyWrapper kl_V2643 [appl_2]
                                              pat_cond_3 = do do kl_V2644 `pseq` applyWrapper kl_V2643 [kl_V2644]
                                           in case kl_V2644 of
                                                  !(kl_V2644@(Cons (!kl_V2644h)
                                                                   (!kl_V2644t))) -> pat_cond_0 kl_V2644 kl_V2644h kl_V2644t
                                                  _ -> pat_cond_3

kl_compile :: Types.KLValue ->
              Types.KLValue ->
              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_compile (!kl_V2648) (!kl_V2649) (!kl_V2650) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_O) -> do let !aw_1 = Types.Atom (Types.UnboundSym "fail")
                                                                                                                !appl_2 <- applyWrapper aw_1 []
                                                                                                                !kl_if_3 <- appl_2 `pseq` (kl_O `pseq` eq appl_2 kl_O)
                                                                                                                !kl_if_4 <- case kl_if_3 of
                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                Atom (B (False)) -> do do !appl_5 <- kl_O `pseq` hd kl_O
                                                                                                                                                          !appl_6 <- appl_5 `pseq` kl_emptyP appl_5
                                                                                                                                                          !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                                                                                                                                          case kl_if_7 of
                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                case kl_if_4 of
                                                                                                                    Atom (B (True)) -> do kl_O `pseq` applyWrapper kl_V2650 [kl_O]
                                                                                                                    Atom (B (False)) -> do do let !aw_8 = Types.Atom (Types.UnboundSym "shen.hdtl")
                                                                                                                                              kl_O `pseq` applyWrapper aw_8 [kl_O]
                                                                                                                    _ -> throwError "if: expected boolean")))
                                                    !appl_9 <- klCons (Types.Atom Types.Nil) (Types.Atom Types.Nil)
                                                    !appl_10 <- kl_V2649 `pseq` (appl_9 `pseq` klCons kl_V2649 appl_9)
                                                    !appl_11 <- appl_10 `pseq` applyWrapper kl_V2648 [appl_10]
                                                    appl_11 `pseq` applyWrapper appl_0 [appl_11]

kl_fail_if :: Types.KLValue ->
              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_fail_if (!kl_V2653) (!kl_V2654) = do !kl_if_0 <- kl_V2654 `pseq` applyWrapper kl_V2653 [kl_V2654]
                                        case kl_if_0 of
                                            Atom (B (True)) -> do let !aw_1 = Types.Atom (Types.UnboundSym "fail")
                                                                  applyWrapper aw_1 []
                                            Atom (B (False)) -> do do return kl_V2654
                                            _ -> throwError "if: expected boolean"

kl_Ats :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_Ats (!kl_V2657) (!kl_V2658) = do kl_V2657 `pseq` (kl_V2658 `pseq` cn kl_V2657 kl_V2658)

kl_tcP :: Types.KLContext Types.Env Types.KLValue
kl_tcP = do value (Types.Atom (Types.UnboundSym "shen.*tc*"))

kl_ps :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_ps (!kl_V2660) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                           kl_V2660 `pseq` (appl_0 `pseq` kl_get kl_V2660 (Types.Atom (Types.UnboundSym "shen.source")) appl_0)) `catchError` (\(!kl_E) -> do let !aw_1 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                              !appl_2 <- kl_V2660 `pseq` applyWrapper aw_1 [kl_V2660,
                                                                                                                                                                                                            Types.Atom (Types.Str " not found.\n"),
                                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                              appl_2 `pseq` simpleError appl_2)

kl_stinput :: Types.KLContext Types.Env Types.KLValue
kl_stinput = do value (Types.Atom (Types.UnboundSym "*stinput*"))

kl_shen_PlusvectorP :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_PlusvectorP (!kl_V2662) = do !kl_if_0 <- kl_V2662 `pseq` absvectorP kl_V2662
                                     case kl_if_0 of
                                         Atom (B (True)) -> do !appl_1 <- kl_V2662 `pseq` addressFrom kl_V2662 (Types.Atom (Types.N (Types.KI 0)))
                                                               !kl_if_2 <- appl_1 `pseq` greaterThan appl_1 (Types.Atom (Types.N (Types.KI 0)))
                                                               case kl_if_2 of
                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                   _ -> throwError "if: expected boolean"
                                         Atom (B (False)) -> do do return (Atom (B False))
                                         _ -> throwError "if: expected boolean"

kl_vector :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_vector (!kl_V2664) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Vector) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_ZeroStamp) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Standard) -> do return kl_Standard)))
                                                                                                                                                                !appl_3 <- let pat_cond_4 = do return kl_ZeroStamp
                                                                                                                                                                               pat_cond_5 = do do let !aw_6 = Types.Atom (Types.UnboundSym "fail")
                                                                                                                                                                                                  !appl_7 <- applyWrapper aw_6 []
                                                                                                                                                                                                  kl_ZeroStamp `pseq` (kl_V2664 `pseq` (appl_7 `pseq` kl_shen_fillvector kl_ZeroStamp (Types.Atom (Types.N (Types.KI 1))) kl_V2664 appl_7))
                                                                                                                                                                            in case kl_V2664 of
                                                                                                                                                                                   kl_V2664@(Atom (N (KI 0))) -> pat_cond_4
                                                                                                                                                                                   _ -> pat_cond_5
                                                                                                                                                                appl_3 `pseq` applyWrapper appl_2 [appl_3])))
                                                                                            !appl_8 <- kl_Vector `pseq` (kl_V2664 `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 0))) kl_V2664)
                                                                                            appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                           !appl_9 <- kl_V2664 `pseq` add kl_V2664 (Types.Atom (Types.N (Types.KI 1)))
                           !appl_10 <- appl_9 `pseq` absvector appl_9
                           appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_fillvector :: Types.KLValue ->
                      Types.KLValue ->
                      Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_fillvector (!kl_V2670) (!kl_V2671) (!kl_V2672) (!kl_V2673) = do !kl_if_0 <- kl_V2672 `pseq` (kl_V2671 `pseq` eq kl_V2672 kl_V2671)
                                                                        case kl_if_0 of
                                                                            Atom (B (True)) -> do kl_V2670 `pseq` (kl_V2672 `pseq` (kl_V2673 `pseq` addressTo kl_V2670 kl_V2672 kl_V2673))
                                                                            Atom (B (False)) -> do do !appl_1 <- kl_V2670 `pseq` (kl_V2671 `pseq` (kl_V2673 `pseq` addressTo kl_V2670 kl_V2671 kl_V2673))
                                                                                                      !appl_2 <- kl_V2671 `pseq` add (Types.Atom (Types.N (Types.KI 1))) kl_V2671
                                                                                                      appl_1 `pseq` (appl_2 `pseq` (kl_V2672 `pseq` (kl_V2673 `pseq` kl_shen_fillvector appl_1 appl_2 kl_V2672 kl_V2673)))
                                                                            _ -> throwError "if: expected boolean"

kl_vectorP :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_vectorP (!kl_V2675) = do !kl_if_0 <- kl_V2675 `pseq` absvectorP kl_V2675
                            case kl_if_0 of
                                Atom (B (True)) -> do !kl_if_1 <- (do !appl_2 <- kl_V2675 `pseq` addressFrom kl_V2675 (Types.Atom (Types.N (Types.KI 0)))
                                                                      appl_2 `pseq` greaterThanOrEqualTo appl_2 (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Atom (B False)))
                                                      case kl_if_1 of
                                                          Atom (B (True)) -> do return (Atom (B True))
                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                          _ -> throwError "if: expected boolean"
                                Atom (B (False)) -> do do return (Atom (B False))
                                _ -> throwError "if: expected boolean"

kl_vector_RB :: Types.KLValue ->
                Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_vector_RB (!kl_V2679) (!kl_V2680) (!kl_V2681) = do let pat_cond_0 = do simpleError (Types.Atom (Types.Str "cannot access 0th element of a vector\n"))
                                                          pat_cond_1 = do do kl_V2679 `pseq` (kl_V2680 `pseq` (kl_V2681 `pseq` addressTo kl_V2679 kl_V2680 kl_V2681))
                                                       in case kl_V2680 of
                                                              kl_V2680@(Atom (N (KI 0))) -> pat_cond_0
                                                              _ -> pat_cond_1

kl_LB_vector :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_LB_vector (!kl_V2684) (!kl_V2685) = do let pat_cond_0 = do simpleError (Types.Atom (Types.Str "cannot access 0th element of a vector\n"))
                                              pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_VectorElement) -> do let !aw_3 = Types.Atom (Types.UnboundSym "fail")
                                                                                                                                         !appl_4 <- applyWrapper aw_3 []
                                                                                                                                         !kl_if_5 <- kl_VectorElement `pseq` (appl_4 `pseq` eq kl_VectorElement appl_4)
                                                                                                                                         case kl_if_5 of
                                                                                                                                             Atom (B (True)) -> do simpleError (Types.Atom (Types.Str "vector element not found\n"))
                                                                                                                                             Atom (B (False)) -> do do return kl_VectorElement
                                                                                                                                             _ -> throwError "if: expected boolean")))
                                                                 !appl_6 <- kl_V2684 `pseq` (kl_V2685 `pseq` addressFrom kl_V2684 kl_V2685)
                                                                 appl_6 `pseq` applyWrapper appl_2 [appl_6]
                                           in case kl_V2685 of
                                                  kl_V2685@(Atom (N (KI 0))) -> pat_cond_0
                                                  _ -> pat_cond_1

kl_shen_posintP :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_posintP (!kl_V2687) = do !kl_if_0 <- kl_V2687 `pseq` kl_integerP kl_V2687
                                 case kl_if_0 of
                                     Atom (B (True)) -> do !kl_if_1 <- kl_V2687 `pseq` greaterThanOrEqualTo kl_V2687 (Types.Atom (Types.N (Types.KI 0)))
                                                           case kl_if_1 of
                                                               Atom (B (True)) -> do return (Atom (B True))
                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                               _ -> throwError "if: expected boolean"
                                     Atom (B (False)) -> do do return (Atom (B False))
                                     _ -> throwError "if: expected boolean"

kl_limit :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_limit (!kl_V2689) = do kl_V2689 `pseq` addressFrom kl_V2689 (Types.Atom (Types.N (Types.KI 0)))

kl_symbolP :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_symbolP (!kl_V2691) = do !kl_if_0 <- kl_V2691 `pseq` kl_booleanP kl_V2691
                            !kl_if_1 <- case kl_if_0 of
                                            Atom (B (True)) -> do return (Atom (B True))
                                            Atom (B (False)) -> do do !kl_if_2 <- kl_V2691 `pseq` numberP kl_V2691
                                                                      !kl_if_3 <- case kl_if_2 of
                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                      Atom (B (False)) -> do do !kl_if_4 <- kl_V2691 `pseq` stringP kl_V2691
                                                                                                                case kl_if_4 of
                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                      _ -> throwError "if: expected boolean"
                                                                      case kl_if_3 of
                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                          _ -> throwError "if: expected boolean"
                                            _ -> throwError "if: expected boolean"
                            case kl_if_1 of
                                Atom (B (True)) -> do return (Atom (B False))
                                Atom (B (False)) -> do do (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_String) -> do kl_String `pseq` kl_shen_analyse_symbolP kl_String)))
                                                              !appl_6 <- kl_V2691 `pseq` str kl_V2691
                                                              appl_6 `pseq` applyWrapper appl_5 [appl_6]) `catchError` (\(!kl_E) -> do return (Atom (B False)))
                                _ -> throwError "if: expected boolean"

kl_shen_analyse_symbolP :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_analyse_symbolP (!kl_V2693) = do !kl_if_0 <- kl_V2693 `pseq` kl_shen_PlusstringP kl_V2693
                                         case kl_if_0 of
                                             Atom (B (True)) -> do !appl_1 <- kl_V2693 `pseq` pos kl_V2693 (Types.Atom (Types.N (Types.KI 0)))
                                                                   !kl_if_2 <- appl_1 `pseq` kl_shen_alphaP appl_1
                                                                   case kl_if_2 of
                                                                       Atom (B (True)) -> do !appl_3 <- kl_V2693 `pseq` tlstr kl_V2693
                                                                                             !kl_if_4 <- appl_3 `pseq` kl_shen_alphanumsP appl_3
                                                                                             case kl_if_4 of
                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                 _ -> throwError "if: expected boolean"
                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                       _ -> throwError "if: expected boolean"
                                             Atom (B (False)) -> do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                       applyWrapper aw_5 [ApplC (wrapNamed "shen.analyse-symbol?" kl_shen_analyse_symbolP)]
                                             _ -> throwError "if: expected boolean"

kl_shen_alphaP :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_alphaP (!kl_V2695) = do !appl_0 <- klCons (Types.Atom (Types.Str ".")) (Types.Atom Types.Nil)
                                !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.Str "'")) appl_0
                                !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.Str "#")) appl_1
                                !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.Str "`")) appl_2
                                !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str ";")) appl_3
                                !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.Str ":")) appl_4
                                !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.Str "}")) appl_5
                                !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.Str "{")) appl_6
                                !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.Str "%")) appl_7
                                !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.Str "&")) appl_8
                                !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.Str "<")) appl_9
                                !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.Str ">")) appl_10
                                !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.Str "~")) appl_11
                                !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.Str "@")) appl_12
                                !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.Str "!")) appl_13
                                !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.Str "$")) appl_14
                                !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.Str "?")) appl_15
                                !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.Str "_")) appl_16
                                !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.Str "-")) appl_17
                                !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.Str "+")) appl_18
                                !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.Str "/")) appl_19
                                !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.Str "*")) appl_20
                                !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.Str "=")) appl_21
                                !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.Str "z")) appl_22
                                !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.Str "y")) appl_23
                                !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.Str "x")) appl_24
                                !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.Str "w")) appl_25
                                !appl_27 <- appl_26 `pseq` klCons (Types.Atom (Types.Str "v")) appl_26
                                !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.Str "u")) appl_27
                                !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.Str "t")) appl_28
                                !appl_30 <- appl_29 `pseq` klCons (Types.Atom (Types.Str "s")) appl_29
                                !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.Str "r")) appl_30
                                !appl_32 <- appl_31 `pseq` klCons (Types.Atom (Types.Str "q")) appl_31
                                !appl_33 <- appl_32 `pseq` klCons (Types.Atom (Types.Str "p")) appl_32
                                !appl_34 <- appl_33 `pseq` klCons (Types.Atom (Types.Str "o")) appl_33
                                !appl_35 <- appl_34 `pseq` klCons (Types.Atom (Types.Str "n")) appl_34
                                !appl_36 <- appl_35 `pseq` klCons (Types.Atom (Types.Str "m")) appl_35
                                !appl_37 <- appl_36 `pseq` klCons (Types.Atom (Types.Str "l")) appl_36
                                !appl_38 <- appl_37 `pseq` klCons (Types.Atom (Types.Str "k")) appl_37
                                !appl_39 <- appl_38 `pseq` klCons (Types.Atom (Types.Str "j")) appl_38
                                !appl_40 <- appl_39 `pseq` klCons (Types.Atom (Types.Str "i")) appl_39
                                !appl_41 <- appl_40 `pseq` klCons (Types.Atom (Types.Str "h")) appl_40
                                !appl_42 <- appl_41 `pseq` klCons (Types.Atom (Types.Str "g")) appl_41
                                !appl_43 <- appl_42 `pseq` klCons (Types.Atom (Types.Str "f")) appl_42
                                !appl_44 <- appl_43 `pseq` klCons (Types.Atom (Types.Str "e")) appl_43
                                !appl_45 <- appl_44 `pseq` klCons (Types.Atom (Types.Str "d")) appl_44
                                !appl_46 <- appl_45 `pseq` klCons (Types.Atom (Types.Str "c")) appl_45
                                !appl_47 <- appl_46 `pseq` klCons (Types.Atom (Types.Str "b")) appl_46
                                !appl_48 <- appl_47 `pseq` klCons (Types.Atom (Types.Str "a")) appl_47
                                !appl_49 <- appl_48 `pseq` klCons (Types.Atom (Types.Str "Z")) appl_48
                                !appl_50 <- appl_49 `pseq` klCons (Types.Atom (Types.Str "Y")) appl_49
                                !appl_51 <- appl_50 `pseq` klCons (Types.Atom (Types.Str "X")) appl_50
                                !appl_52 <- appl_51 `pseq` klCons (Types.Atom (Types.Str "W")) appl_51
                                !appl_53 <- appl_52 `pseq` klCons (Types.Atom (Types.Str "V")) appl_52
                                !appl_54 <- appl_53 `pseq` klCons (Types.Atom (Types.Str "U")) appl_53
                                !appl_55 <- appl_54 `pseq` klCons (Types.Atom (Types.Str "T")) appl_54
                                !appl_56 <- appl_55 `pseq` klCons (Types.Atom (Types.Str "S")) appl_55
                                !appl_57 <- appl_56 `pseq` klCons (Types.Atom (Types.Str "R")) appl_56
                                !appl_58 <- appl_57 `pseq` klCons (Types.Atom (Types.Str "Q")) appl_57
                                !appl_59 <- appl_58 `pseq` klCons (Types.Atom (Types.Str "P")) appl_58
                                !appl_60 <- appl_59 `pseq` klCons (Types.Atom (Types.Str "O")) appl_59
                                !appl_61 <- appl_60 `pseq` klCons (Types.Atom (Types.Str "N")) appl_60
                                !appl_62 <- appl_61 `pseq` klCons (Types.Atom (Types.Str "M")) appl_61
                                !appl_63 <- appl_62 `pseq` klCons (Types.Atom (Types.Str "L")) appl_62
                                !appl_64 <- appl_63 `pseq` klCons (Types.Atom (Types.Str "K")) appl_63
                                !appl_65 <- appl_64 `pseq` klCons (Types.Atom (Types.Str "J")) appl_64
                                !appl_66 <- appl_65 `pseq` klCons (Types.Atom (Types.Str "I")) appl_65
                                !appl_67 <- appl_66 `pseq` klCons (Types.Atom (Types.Str "H")) appl_66
                                !appl_68 <- appl_67 `pseq` klCons (Types.Atom (Types.Str "G")) appl_67
                                !appl_69 <- appl_68 `pseq` klCons (Types.Atom (Types.Str "F")) appl_68
                                !appl_70 <- appl_69 `pseq` klCons (Types.Atom (Types.Str "E")) appl_69
                                !appl_71 <- appl_70 `pseq` klCons (Types.Atom (Types.Str "D")) appl_70
                                !appl_72 <- appl_71 `pseq` klCons (Types.Atom (Types.Str "C")) appl_71
                                !appl_73 <- appl_72 `pseq` klCons (Types.Atom (Types.Str "B")) appl_72
                                !appl_74 <- appl_73 `pseq` klCons (Types.Atom (Types.Str "A")) appl_73
                                kl_V2695 `pseq` (appl_74 `pseq` kl_elementP kl_V2695 appl_74)

kl_shen_alphanumsP :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_alphanumsP (!kl_V2697) = do let pat_cond_0 = do return (Atom (B True))
                                        pat_cond_1 = do !kl_if_2 <- kl_V2697 `pseq` kl_shen_PlusstringP kl_V2697
                                                        case kl_if_2 of
                                                            Atom (B (True)) -> do !appl_3 <- kl_V2697 `pseq` pos kl_V2697 (Types.Atom (Types.N (Types.KI 0)))
                                                                                  !kl_if_4 <- appl_3 `pseq` kl_shen_alphanumP appl_3
                                                                                  case kl_if_4 of
                                                                                      Atom (B (True)) -> do !appl_5 <- kl_V2697 `pseq` tlstr kl_V2697
                                                                                                            !kl_if_6 <- appl_5 `pseq` kl_shen_alphanumsP appl_5
                                                                                                            case kl_if_6 of
                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                _ -> throwError "if: expected boolean"
                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                      _ -> throwError "if: expected boolean"
                                                            Atom (B (False)) -> do do let !aw_7 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                      applyWrapper aw_7 [ApplC (wrapNamed "shen.alphanums?" kl_shen_alphanumsP)]
                                                            _ -> throwError "if: expected boolean"
                                     in case kl_V2697 of
                                            kl_V2697@(Atom (Str "")) -> pat_cond_0
                                            _ -> pat_cond_1

kl_shen_alphanumP :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_alphanumP (!kl_V2699) = do !kl_if_0 <- kl_V2699 `pseq` kl_shen_alphaP kl_V2699
                                   case kl_if_0 of
                                       Atom (B (True)) -> do return (Atom (B True))
                                       Atom (B (False)) -> do do !kl_if_1 <- kl_V2699 `pseq` kl_shen_digitP kl_V2699
                                                                 case kl_if_1 of
                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                     _ -> throwError "if: expected boolean"
                                       _ -> throwError "if: expected boolean"

kl_shen_digitP :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_digitP (!kl_V2701) = do !appl_0 <- klCons (Types.Atom (Types.Str "0")) (Types.Atom Types.Nil)
                                !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.Str "9")) appl_0
                                !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.Str "8")) appl_1
                                !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.Str "7")) appl_2
                                !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str "6")) appl_3
                                !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.Str "5")) appl_4
                                !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.Str "4")) appl_5
                                !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.Str "3")) appl_6
                                !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.Str "2")) appl_7
                                !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.Str "1")) appl_8
                                kl_V2701 `pseq` (appl_9 `pseq` kl_elementP kl_V2701 appl_9)

kl_variableP :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_variableP (!kl_V2703) = do !kl_if_0 <- kl_V2703 `pseq` kl_booleanP kl_V2703
                              !kl_if_1 <- case kl_if_0 of
                                              Atom (B (True)) -> do return (Atom (B True))
                                              Atom (B (False)) -> do do !kl_if_2 <- kl_V2703 `pseq` numberP kl_V2703
                                                                        !kl_if_3 <- case kl_if_2 of
                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                        Atom (B (False)) -> do do !kl_if_4 <- kl_V2703 `pseq` stringP kl_V2703
                                                                                                                  case kl_if_4 of
                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                        _ -> throwError "if: expected boolean"
                                                                        case kl_if_3 of
                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                            _ -> throwError "if: expected boolean"
                                              _ -> throwError "if: expected boolean"
                              case kl_if_1 of
                                  Atom (B (True)) -> do return (Atom (B False))
                                  Atom (B (False)) -> do do (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_String) -> do kl_String `pseq` kl_shen_analyse_variableP kl_String)))
                                                                !appl_6 <- kl_V2703 `pseq` str kl_V2703
                                                                appl_6 `pseq` applyWrapper appl_5 [appl_6]) `catchError` (\(!kl_E) -> do return (Atom (B False)))
                                  _ -> throwError "if: expected boolean"

kl_shen_analyse_variableP :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_analyse_variableP (!kl_V2705) = do !kl_if_0 <- kl_V2705 `pseq` kl_shen_PlusstringP kl_V2705
                                           case kl_if_0 of
                                               Atom (B (True)) -> do !appl_1 <- kl_V2705 `pseq` pos kl_V2705 (Types.Atom (Types.N (Types.KI 0)))
                                                                     !kl_if_2 <- appl_1 `pseq` kl_shen_uppercaseP appl_1
                                                                     case kl_if_2 of
                                                                         Atom (B (True)) -> do !appl_3 <- kl_V2705 `pseq` tlstr kl_V2705
                                                                                               !kl_if_4 <- appl_3 `pseq` kl_shen_alphanumsP appl_3
                                                                                               case kl_if_4 of
                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                   _ -> throwError "if: expected boolean"
                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                         _ -> throwError "if: expected boolean"
                                               Atom (B (False)) -> do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                         applyWrapper aw_5 [ApplC (wrapNamed "shen.analyse-variable?" kl_shen_analyse_variableP)]
                                               _ -> throwError "if: expected boolean"

kl_shen_uppercaseP :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_uppercaseP (!kl_V2707) = do !appl_0 <- klCons (Types.Atom (Types.Str "Z")) (Types.Atom Types.Nil)
                                    !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.Str "Y")) appl_0
                                    !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.Str "X")) appl_1
                                    !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.Str "W")) appl_2
                                    !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str "V")) appl_3
                                    !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.Str "U")) appl_4
                                    !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.Str "T")) appl_5
                                    !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.Str "S")) appl_6
                                    !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.Str "R")) appl_7
                                    !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.Str "Q")) appl_8
                                    !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.Str "P")) appl_9
                                    !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.Str "O")) appl_10
                                    !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.Str "N")) appl_11
                                    !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.Str "M")) appl_12
                                    !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.Str "L")) appl_13
                                    !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.Str "K")) appl_14
                                    !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.Str "J")) appl_15
                                    !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.Str "I")) appl_16
                                    !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.Str "H")) appl_17
                                    !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.Str "G")) appl_18
                                    !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.Str "F")) appl_19
                                    !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.Str "E")) appl_20
                                    !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.Str "D")) appl_21
                                    !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.Str "C")) appl_22
                                    !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.Str "B")) appl_23
                                    !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.Str "A")) appl_24
                                    kl_V2707 `pseq` (appl_25 `pseq` kl_elementP kl_V2707 appl_25)

kl_gensym :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_gensym (!kl_V2709) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*gensym*"))
                           !appl_1 <- appl_0 `pseq` add (Types.Atom (Types.N (Types.KI 1))) appl_0
                           !appl_2 <- appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*gensym*")) appl_1
                           kl_V2709 `pseq` (appl_2 `pseq` kl_concat kl_V2709 appl_2)

kl_concat :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_concat (!kl_V2712) (!kl_V2713) = do !appl_0 <- kl_V2712 `pseq` str kl_V2712
                                       !appl_1 <- kl_V2713 `pseq` str kl_V2713
                                       !appl_2 <- appl_0 `pseq` (appl_1 `pseq` cn appl_0 appl_1)
                                       appl_2 `pseq` intern appl_2

kl_Atp :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_Atp (!kl_V2716) (!kl_V2717) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Vector) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Tag) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Fst) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Snd) -> do return kl_Vector)))
                                                                                                                                                                                                                                 !appl_4 <- kl_Vector `pseq` (kl_V2717 `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 2))) kl_V2717)
                                                                                                                                                                                                                                 appl_4 `pseq` applyWrapper appl_3 [appl_4])))
                                                                                                                                                                   !appl_5 <- kl_Vector `pseq` (kl_V2716 `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 1))) kl_V2716)
                                                                                                                                                                   appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                                     !appl_6 <- kl_Vector `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 0))) (Types.Atom (Types.UnboundSym "shen.tuple"))
                                                                                                     appl_6 `pseq` applyWrapper appl_1 [appl_6])))
                                    !appl_7 <- absvector (Types.Atom (Types.N (Types.KI 3)))
                                    appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_fst :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_fst (!kl_V2719) = do kl_V2719 `pseq` addressFrom kl_V2719 (Types.Atom (Types.N (Types.KI 1)))

kl_snd :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_snd (!kl_V2721) = do kl_V2721 `pseq` addressFrom kl_V2721 (Types.Atom (Types.N (Types.KI 2)))

kl_tupleP :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_tupleP (!kl_V2723) = do (do !kl_if_0 <- kl_V2723 `pseq` absvectorP kl_V2723
                               case kl_if_0 of
                                   Atom (B (True)) -> do !appl_1 <- kl_V2723 `pseq` addressFrom kl_V2723 (Types.Atom (Types.N (Types.KI 0)))
                                                         !kl_if_2 <- appl_1 `pseq` eq (Types.Atom (Types.UnboundSym "shen.tuple")) appl_1
                                                         case kl_if_2 of
                                                             Atom (B (True)) -> do return (Atom (B True))
                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                             _ -> throwError "if: expected boolean"
                                   Atom (B (False)) -> do do return (Atom (B False))
                                   _ -> throwError "if: expected boolean") `catchError` (\(!kl_E) -> do return (Atom (B False)))

kl_append :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_append (!kl_V2726) (!kl_V2727) = do let pat_cond_0 = do return kl_V2727
                                           pat_cond_1 kl_V2726 kl_V2726h kl_V2726t = do !appl_2 <- kl_V2726t `pseq` (kl_V2727 `pseq` kl_append kl_V2726t kl_V2727)
                                                                                        kl_V2726h `pseq` (appl_2 `pseq` klCons kl_V2726h appl_2)
                                           pat_cond_3 = do do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                              applyWrapper aw_4 [ApplC (wrapNamed "append" kl_append)]
                                        in case kl_V2726 of
                                               kl_V2726@(Atom (Nil)) -> pat_cond_0
                                               !(kl_V2726@(Cons (!kl_V2726h)
                                                                (!kl_V2726t))) -> pat_cond_1 kl_V2726 kl_V2726h kl_V2726t
                                               _ -> pat_cond_3

kl_Atv :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_Atv (!kl_V2730) (!kl_V2731) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_NewVector) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_XPlusNewVector) -> do let pat_cond_3 = do return kl_XPlusNewVector
                                                                                                                                                                                                                                                     pat_cond_4 = do do kl_V2731 `pseq` (kl_Limit `pseq` (kl_XPlusNewVector `pseq` kl_shen_Atv_help kl_V2731 (Types.Atom (Types.N (Types.KI 1))) kl_Limit kl_XPlusNewVector))
                                                                                                                                                                                                                                                  in case kl_Limit of
                                                                                                                                                                                                                                                         kl_Limit@(Atom (N (KI 0))) -> pat_cond_3
                                                                                                                                                                                                                                                         _ -> pat_cond_4)))
                                                                                                                                                                        !appl_5 <- kl_NewVector `pseq` (kl_V2730 `pseq` kl_vector_RB kl_NewVector (Types.Atom (Types.N (Types.KI 1))) kl_V2730)
                                                                                                                                                                        appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                                    !appl_6 <- kl_Limit `pseq` add kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                    !appl_7 <- appl_6 `pseq` kl_vector appl_6
                                                                                                    appl_7 `pseq` applyWrapper appl_1 [appl_7])))
                                    !appl_8 <- kl_V2731 `pseq` kl_limit kl_V2731
                                    appl_8 `pseq` applyWrapper appl_0 [appl_8]

kl_shen_Atv_help :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_Atv_help (!kl_V2737) (!kl_V2738) (!kl_V2739) (!kl_V2740) = do !kl_if_0 <- kl_V2739 `pseq` (kl_V2738 `pseq` eq kl_V2739 kl_V2738)
                                                                      case kl_if_0 of
                                                                          Atom (B (True)) -> do !appl_1 <- kl_V2739 `pseq` add kl_V2739 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                kl_V2737 `pseq` (kl_V2740 `pseq` (kl_V2739 `pseq` (appl_1 `pseq` kl_shen_copyfromvector kl_V2737 kl_V2740 kl_V2739 appl_1)))
                                                                          Atom (B (False)) -> do do !appl_2 <- kl_V2738 `pseq` add kl_V2738 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                    !appl_3 <- kl_V2738 `pseq` add kl_V2738 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                    !appl_4 <- kl_V2737 `pseq` (kl_V2740 `pseq` (kl_V2738 `pseq` (appl_3 `pseq` kl_shen_copyfromvector kl_V2737 kl_V2740 kl_V2738 appl_3)))
                                                                                                    kl_V2737 `pseq` (appl_2 `pseq` (kl_V2739 `pseq` (appl_4 `pseq` kl_shen_Atv_help kl_V2737 appl_2 kl_V2739 appl_4)))
                                                                          _ -> throwError "if: expected boolean"

kl_shen_copyfromvector :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_copyfromvector (!kl_V2745) (!kl_V2746) (!kl_V2747) (!kl_V2748) = do (do !appl_0 <- kl_V2745 `pseq` (kl_V2747 `pseq` kl_LB_vector kl_V2745 kl_V2747)
                                                                                kl_V2746 `pseq` (kl_V2748 `pseq` (appl_0 `pseq` kl_vector_RB kl_V2746 kl_V2748 appl_0))) `catchError` (\(!kl_E) -> do return kl_V2746)

kl_hdv :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_hdv (!kl_V2750) = do (do kl_V2750 `pseq` kl_LB_vector kl_V2750 (Types.Atom (Types.N (Types.KI 1)))) `catchError` (\(!kl_E) -> do let !aw_0 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                    !appl_1 <- kl_V2750 `pseq` applyWrapper aw_0 [kl_V2750,
                                                                                                                                                                                  Types.Atom (Types.Str "\n"),
                                                                                                                                                                                  Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                    !appl_2 <- appl_1 `pseq` cn (Types.Atom (Types.Str "hdv needs a non-empty vector as an argument; not ")) appl_1
                                                                                                                                    appl_2 `pseq` simpleError appl_2)

kl_tlv :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_tlv (!kl_V2752) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do let pat_cond_1 = do simpleError (Types.Atom (Types.Str "cannot take the tail of the empty vector\n"))
                                                                                            pat_cond_2 = do do let pat_cond_3 = do kl_vector (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                   pat_cond_4 = do do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_NewVector) -> do !appl_6 <- kl_Limit `pseq` Primitives.subtract kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                          !appl_7 <- appl_6 `pseq` kl_vector appl_6
                                                                                                                                                                                                          kl_V2752 `pseq` (kl_Limit `pseq` (appl_7 `pseq` kl_shen_tlv_help kl_V2752 (Types.Atom (Types.N (Types.KI 2))) kl_Limit appl_7)))))
                                                                                                                                      !appl_8 <- kl_Limit `pseq` Primitives.subtract kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                      !appl_9 <- appl_8 `pseq` kl_vector appl_8
                                                                                                                                      appl_9 `pseq` applyWrapper appl_5 [appl_9]
                                                                                                                in case kl_Limit of
                                                                                                                       kl_Limit@(Atom (N (KI 1))) -> pat_cond_3
                                                                                                                       _ -> pat_cond_4
                                                                                         in case kl_Limit of
                                                                                                kl_Limit@(Atom (N (KI 0))) -> pat_cond_1
                                                                                                _ -> pat_cond_2)))
                        !appl_10 <- kl_V2752 `pseq` kl_limit kl_V2752
                        appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_tlv_help :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_tlv_help (!kl_V2758) (!kl_V2759) (!kl_V2760) (!kl_V2761) = do !kl_if_0 <- kl_V2760 `pseq` (kl_V2759 `pseq` eq kl_V2760 kl_V2759)
                                                                      case kl_if_0 of
                                                                          Atom (B (True)) -> do !appl_1 <- kl_V2760 `pseq` Primitives.subtract kl_V2760 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                kl_V2758 `pseq` (kl_V2761 `pseq` (kl_V2760 `pseq` (appl_1 `pseq` kl_shen_copyfromvector kl_V2758 kl_V2761 kl_V2760 appl_1)))
                                                                          Atom (B (False)) -> do do !appl_2 <- kl_V2759 `pseq` add kl_V2759 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                    !appl_3 <- kl_V2759 `pseq` Primitives.subtract kl_V2759 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                    !appl_4 <- kl_V2758 `pseq` (kl_V2761 `pseq` (kl_V2759 `pseq` (appl_3 `pseq` kl_shen_copyfromvector kl_V2758 kl_V2761 kl_V2759 appl_3)))
                                                                                                    kl_V2758 `pseq` (appl_2 `pseq` (kl_V2760 `pseq` (appl_4 `pseq` kl_shen_tlv_help kl_V2758 appl_2 kl_V2760 appl_4)))
                                                                          _ -> throwError "if: expected boolean"

kl_assoc :: Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_assoc (!kl_V2773) (!kl_V2774) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                          pat_cond_1 kl_V2774 kl_V2774h kl_V2774hh kl_V2774ht kl_V2774t = do return kl_V2774h
                                          pat_cond_2 kl_V2774 kl_V2774h kl_V2774t = do kl_V2773 `pseq` (kl_V2774t `pseq` kl_assoc kl_V2773 kl_V2774t)
                                          pat_cond_3 = do do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                             applyWrapper aw_4 [ApplC (wrapNamed "assoc" kl_assoc)]
                                       in case kl_V2774 of
                                              kl_V2774@(Atom (Nil)) -> pat_cond_0
                                              !(kl_V2774@(Cons (!(kl_V2774h@(Cons (!kl_V2774hh)
                                                                                  (!kl_V2774ht))))
                                                               (!kl_V2774t))) | eqCore kl_V2774hh kl_V2773 -> pat_cond_1 kl_V2774 kl_V2774h kl_V2774hh kl_V2774ht kl_V2774t
                                              !(kl_V2774@(Cons (!kl_V2774h)
                                                               (!kl_V2774t))) -> pat_cond_2 kl_V2774 kl_V2774h kl_V2774t
                                              _ -> pat_cond_3

kl_booleanP :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_booleanP (!kl_V2780) = do let pat_cond_0 = do return (Atom (B True))
                                 pat_cond_1 = do return (Atom (B True))
                                 pat_cond_2 = do do return (Atom (B False))
                              in case kl_V2780 of
                                     kl_V2780@(Atom (UnboundSym "true")) -> pat_cond_0
                                     kl_V2780@(Atom (B (True))) -> pat_cond_0
                                     kl_V2780@(Atom (UnboundSym "false")) -> pat_cond_1
                                     kl_V2780@(Atom (B (False))) -> pat_cond_1
                                     _ -> pat_cond_2

kl_nl :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_nl (!kl_V2782) = do let pat_cond_0 = do return (Types.Atom (Types.N (Types.KI 0)))
                           pat_cond_1 = do do !appl_2 <- kl_stoutput
                                              let !aw_3 = Types.Atom (Types.UnboundSym "shen.prhush")
                                              !appl_4 <- appl_2 `pseq` applyWrapper aw_3 [Types.Atom (Types.Str "\n"),
                                                                                          appl_2]
                                              !appl_5 <- kl_V2782 `pseq` Primitives.subtract kl_V2782 (Types.Atom (Types.N (Types.KI 1)))
                                              !appl_6 <- appl_5 `pseq` kl_nl appl_5
                                              appl_4 `pseq` (appl_6 `pseq` kl_do appl_4 appl_6)
                        in case kl_V2782 of
                               kl_V2782@(Atom (N (KI 0))) -> pat_cond_0
                               _ -> pat_cond_1

kl_difference :: Types.KLValue ->
                 Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_difference (!kl_V2787) (!kl_V2788) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                               pat_cond_1 kl_V2787 kl_V2787h kl_V2787t = do !kl_if_2 <- kl_V2787h `pseq` (kl_V2788 `pseq` kl_elementP kl_V2787h kl_V2788)
                                                                                            case kl_if_2 of
                                                                                                Atom (B (True)) -> do kl_V2787t `pseq` (kl_V2788 `pseq` kl_difference kl_V2787t kl_V2788)
                                                                                                Atom (B (False)) -> do do !appl_3 <- kl_V2787t `pseq` (kl_V2788 `pseq` kl_difference kl_V2787t kl_V2788)
                                                                                                                          kl_V2787h `pseq` (appl_3 `pseq` klCons kl_V2787h appl_3)
                                                                                                _ -> throwError "if: expected boolean"
                                               pat_cond_4 = do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                  applyWrapper aw_5 [ApplC (wrapNamed "difference" kl_difference)]
                                            in case kl_V2787 of
                                                   kl_V2787@(Atom (Nil)) -> pat_cond_0
                                                   !(kl_V2787@(Cons (!kl_V2787h)
                                                                    (!kl_V2787t))) -> pat_cond_1 kl_V2787 kl_V2787h kl_V2787t
                                                   _ -> pat_cond_4

kl_do :: Types.KLValue ->
         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_do (!kl_V2791) (!kl_V2792) = do return kl_V2792

{-
kl_elementP :: Types.KLValue ->
               Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_elementP (!kl_V1594) (!kl_V1595) = do let !appl_0 = List []
                                         !kl_if_1 <- appl_0 `pseq` (kl_V1595 `pseq` eq appl_0 kl_V1595)
                                         klIf kl_if_1 (do return (Atom (B False))) (do !kl_if_2 <- kl_V1595 `pseq` consP kl_V1595
                                                                                       !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V1595 `pseq` hd kl_V1595
                                                                                                                    appl_4 `pseq` (kl_V1594 `pseq` eq appl_4 kl_V1594)) (do return (Atom (B False)))
                                                                                       klIf kl_if_3 (do return (Atom (B True))) (do !kl_if_5 <- kl_V1595 `pseq` consP kl_V1595
                                                                                                                                    klIf kl_if_5 (do !appl_6 <- kl_V1595 `pseq` tl kl_V1595
                                                                                                                                                     kl_V1594 `pseq` (appl_6 `pseq` kl_elementP kl_V1594 appl_6)) (do klIf (Atom (B True)) (do let !aw_7 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                               applyWrapper aw_7 [ApplC (wrapNamed "element?" kl_elementP)]) (do return (List [])))))
-}

kl_elementP :: Types.KLValue ->
               Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_elementP !v (Atom Nil) = return (Atom (B False))
kl_elementP !v (Cons h hs) = do
  case eqCore h v of
   True  -> return (Atom (B True))
   False -> kl_elementP v hs
kl_elementP _ _ = applyWrapper (Atom (UnboundSym "shen.f_error")) [ApplC (wrapNamed "element?" kl_elementP)]

kl_emptyP :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_emptyP (!kl_V2811) = do let pat_cond_0 = do return (Atom (B True))
                               pat_cond_1 = do do return (Atom (B False))
                            in case kl_V2811 of
                                   kl_V2811@(Atom (Nil)) -> pat_cond_0
                                   _ -> pat_cond_1

kl_fix :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_fix (!kl_V2814) (!kl_V2815) = do !appl_0 <- kl_V2815 `pseq` applyWrapper kl_V2814 [kl_V2815]
                                    kl_V2814 `pseq` (kl_V2815 `pseq` (appl_0 `pseq` kl_shen_fix_help kl_V2814 kl_V2815 appl_0))

kl_shen_fix_help :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_fix_help (!kl_V2826) (!kl_V2827) (!kl_V2828) = do !kl_if_0 <- kl_V2828 `pseq` (kl_V2827 `pseq` eq kl_V2828 kl_V2827)
                                                          case kl_if_0 of
                                                              Atom (B (True)) -> do return kl_V2828
                                                              Atom (B (False)) -> do do !appl_1 <- kl_V2828 `pseq` applyWrapper kl_V2826 [kl_V2828]
                                                                                        kl_V2826 `pseq` (kl_V2828 `pseq` (appl_1 `pseq` kl_shen_fix_help kl_V2826 kl_V2828 appl_1))
                                                              _ -> throwError "if: expected boolean"

kl_put :: Types.KLValue ->
          Types.KLValue ->
          Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_put (!kl_V2833) (!kl_V2834) (!kl_V2835) (!kl_V2836) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Change) -> do return kl_V2835)))
                                                                                                                                                                                        !appl_3 <- kl_V2833 `pseq` (kl_V2834 `pseq` (kl_V2835 `pseq` (kl_Entry `pseq` kl_shen_change_pointer_value kl_V2833 kl_V2834 kl_V2835 kl_Entry)))
                                                                                                                                                                                        !appl_4 <- kl_V2836 `pseq` (kl_N `pseq` (appl_3 `pseq` kl_vector_RB kl_V2836 kl_N appl_3))
                                                                                                                                                                                        appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                                        !appl_5 <- (do kl_V2836 `pseq` (kl_N `pseq` kl_LB_vector kl_V2836 kl_N)) `catchError` (\(!kl_E) -> do return (Types.Atom Types.Nil))
                                                                                                                        appl_5 `pseq` applyWrapper appl_1 [appl_5])))
                                                            !appl_6 <- kl_V2836 `pseq` kl_limit kl_V2836
                                                            !appl_7 <- kl_V2833 `pseq` (appl_6 `pseq` kl_hash kl_V2833 appl_6)
                                                            appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_unput :: Types.KLValue ->
            Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_unput (!kl_V2840) (!kl_V2841) (!kl_V2842) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Change) -> do return kl_V2840)))
                                                                                                                                                                              !appl_3 <- kl_V2840 `pseq` (kl_V2841 `pseq` (kl_Entry `pseq` kl_shen_remove_pointer kl_V2840 kl_V2841 kl_Entry))
                                                                                                                                                                              !appl_4 <- kl_V2842 `pseq` (kl_N `pseq` (appl_3 `pseq` kl_vector_RB kl_V2842 kl_N appl_3))
                                                                                                                                                                              appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                              !appl_5 <- (do kl_V2842 `pseq` (kl_N `pseq` kl_LB_vector kl_V2842 kl_N)) `catchError` (\(!kl_E) -> do return (Types.Atom Types.Nil))
                                                                                                              appl_5 `pseq` applyWrapper appl_1 [appl_5])))
                                                  !appl_6 <- kl_V2842 `pseq` kl_limit kl_V2842
                                                  !appl_7 <- kl_V2840 `pseq` (appl_6 `pseq` kl_hash kl_V2840 appl_6)
                                                  appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_shen_remove_pointer :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_remove_pointer (!kl_V2850) (!kl_V2851) (!kl_V2852) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                                                    pat_cond_1 kl_V2852 kl_V2852h kl_V2852hh kl_V2852hhh kl_V2852hht kl_V2852hhth kl_V2852ht kl_V2852t = do return kl_V2852t
                                                                    pat_cond_2 kl_V2852 kl_V2852h kl_V2852t = do !appl_3 <- kl_V2850 `pseq` (kl_V2851 `pseq` (kl_V2852t `pseq` kl_shen_remove_pointer kl_V2850 kl_V2851 kl_V2852t))
                                                                                                                 kl_V2852h `pseq` (appl_3 `pseq` klCons kl_V2852h appl_3)
                                                                    pat_cond_4 = do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                       applyWrapper aw_5 [ApplC (wrapNamed "shen.remove-pointer" kl_shen_remove_pointer)]
                                                                 in case kl_V2852 of
                                                                        kl_V2852@(Atom (Nil)) -> pat_cond_0
                                                                        !(kl_V2852@(Cons (!(kl_V2852h@(Cons (!(kl_V2852hh@(Cons (!kl_V2852hhh)
                                                                                                                                (!(kl_V2852hht@(Cons (!kl_V2852hhth)
                                                                                                                                                     (Atom (Nil))))))))
                                                                                                            (!kl_V2852ht))))
                                                                                         (!kl_V2852t))) | eqCore kl_V2852hhth kl_V2851 && eqCore kl_V2852hhh kl_V2850 -> pat_cond_1 kl_V2852 kl_V2852h kl_V2852hh kl_V2852hhh kl_V2852hht kl_V2852hhth kl_V2852ht kl_V2852t
                                                                        !(kl_V2852@(Cons (!kl_V2852h)
                                                                                         (!kl_V2852t))) -> pat_cond_2 kl_V2852 kl_V2852h kl_V2852t
                                                                        _ -> pat_cond_4

kl_shen_change_pointer_value :: Types.KLValue ->
                                Types.KLValue ->
                                Types.KLValue ->
                                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_change_pointer_value (!kl_V2861) (!kl_V2862) (!kl_V2863) (!kl_V2864) = do let pat_cond_0 = do !appl_1 <- kl_V2862 `pseq` klCons kl_V2862 (Types.Atom Types.Nil)
                                                                                                      !appl_2 <- kl_V2861 `pseq` (appl_1 `pseq` klCons kl_V2861 appl_1)
                                                                                                      !appl_3 <- appl_2 `pseq` (kl_V2863 `pseq` klCons appl_2 kl_V2863)
                                                                                                      appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                      pat_cond_4 kl_V2864 kl_V2864h kl_V2864hh kl_V2864hhh kl_V2864hht kl_V2864hhth kl_V2864ht kl_V2864t = do !appl_5 <- kl_V2864hh `pseq` (kl_V2863 `pseq` klCons kl_V2864hh kl_V2863)
                                                                                                                                                                                              appl_5 `pseq` (kl_V2864t `pseq` klCons appl_5 kl_V2864t)
                                                                                      pat_cond_6 kl_V2864 kl_V2864h kl_V2864t = do !appl_7 <- kl_V2861 `pseq` (kl_V2862 `pseq` (kl_V2863 `pseq` (kl_V2864t `pseq` kl_shen_change_pointer_value kl_V2861 kl_V2862 kl_V2863 kl_V2864t)))
                                                                                                                                   kl_V2864h `pseq` (appl_7 `pseq` klCons kl_V2864h appl_7)
                                                                                      pat_cond_8 = do do let !aw_9 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                         applyWrapper aw_9 [ApplC (wrapNamed "shen.change-pointer-value" kl_shen_change_pointer_value)]
                                                                                   in case kl_V2864 of
                                                                                          kl_V2864@(Atom (Nil)) -> pat_cond_0
                                                                                          !(kl_V2864@(Cons (!(kl_V2864h@(Cons (!(kl_V2864hh@(Cons (!kl_V2864hhh)
                                                                                                                                                  (!(kl_V2864hht@(Cons (!kl_V2864hhth)
                                                                                                                                                                       (Atom (Nil))))))))
                                                                                                                              (!kl_V2864ht))))
                                                                                                           (!kl_V2864t))) | eqCore kl_V2864hhth kl_V2862 && eqCore kl_V2864hhh kl_V2861 -> pat_cond_4 kl_V2864 kl_V2864h kl_V2864hh kl_V2864hhh kl_V2864hht kl_V2864hhth kl_V2864ht kl_V2864t
                                                                                          !(kl_V2864@(Cons (!kl_V2864h)
                                                                                                           (!kl_V2864t))) -> pat_cond_6 kl_V2864 kl_V2864h kl_V2864t
                                                                                          _ -> pat_cond_8

kl_get :: Types.KLValue ->
          Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_get (!kl_V2868) (!kl_V2869) (!kl_V2870) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Result) -> do !kl_if_3 <- kl_Result `pseq` kl_emptyP kl_Result
                                                                                                                                                                                                                                             case kl_if_3 of
                                                                                                                                                                                                                                                 Atom (B (True)) -> do simpleError (Types.Atom (Types.Str "value not found\n"))
                                                                                                                                                                                                                                                 Atom (B (False)) -> do do kl_Result `pseq` tl kl_Result
                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean")))
                                                                                                                                                                            !appl_4 <- kl_V2869 `pseq` klCons kl_V2869 (Types.Atom Types.Nil)
                                                                                                                                                                            !appl_5 <- kl_V2868 `pseq` (appl_4 `pseq` klCons kl_V2868 appl_4)
                                                                                                                                                                            !appl_6 <- appl_5 `pseq` (kl_Entry `pseq` kl_assoc appl_5 kl_Entry)
                                                                                                                                                                            appl_6 `pseq` applyWrapper appl_2 [appl_6])))
                                                                                                            !appl_7 <- (do kl_V2870 `pseq` (kl_N `pseq` kl_LB_vector kl_V2870 kl_N)) `catchError` (\(!kl_E) -> do simpleError (Types.Atom (Types.Str "pointer not found\n")))
                                                                                                            appl_7 `pseq` applyWrapper appl_1 [appl_7])))
                                                !appl_8 <- kl_V2870 `pseq` kl_limit kl_V2870
                                                !appl_9 <- kl_V2868 `pseq` (appl_8 `pseq` kl_hash kl_V2868 appl_8)
                                                appl_9 `pseq` applyWrapper appl_0 [appl_9]

kl_hash :: Types.KLValue ->
           Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_hash (!kl_V2873) (!kl_V2874) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Hash) -> do let pat_cond_1 = do return (Types.Atom (Types.N (Types.KI 1)))
                                                                                                        pat_cond_2 = do do return kl_Hash
                                                                                                     in case kl_Hash of
                                                                                                            kl_Hash@(Atom (N (KI 0))) -> pat_cond_1
                                                                                                            _ -> pat_cond_2)))
                                     let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` stringToN kl_X)))
                                     !appl_4 <- kl_V2873 `pseq` kl_explode kl_V2873
                                     !appl_5 <- appl_3 `pseq` (appl_4 `pseq` kl_map appl_3 appl_4)
                                     !appl_6 <- appl_5 `pseq` kl_sum appl_5
                                     !appl_7 <- appl_6 `pseq` (kl_V2874 `pseq` kl_shen_mod appl_6 kl_V2874)
                                     appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_shen_mod :: Types.KLValue ->
               Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mod (!kl_V2877) (!kl_V2878) = do !appl_0 <- kl_V2878 `pseq` klCons kl_V2878 (Types.Atom Types.Nil)
                                         !appl_1 <- kl_V2877 `pseq` (appl_0 `pseq` kl_shen_multiples kl_V2877 appl_0)
                                         kl_V2877 `pseq` (appl_1 `pseq` kl_shen_modh kl_V2877 appl_1)

kl_shen_multiples :: Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_multiples (!kl_V2881) (!kl_V2882) = do !kl_if_0 <- let pat_cond_1 kl_V2882 kl_V2882h kl_V2882t = do !kl_if_2 <- kl_V2882h `pseq` (kl_V2881 `pseq` greaterThan kl_V2882h kl_V2881)
                                                                                                            case kl_if_2 of
                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                _ -> throwError "if: expected boolean"
                                                               pat_cond_3 = do do return (Atom (B False))
                                                            in case kl_V2882 of
                                                                   !(kl_V2882@(Cons (!kl_V2882h)
                                                                                    (!kl_V2882t))) -> pat_cond_1 kl_V2882 kl_V2882h kl_V2882t
                                                                   _ -> pat_cond_3
                                               case kl_if_0 of
                                                   Atom (B (True)) -> do kl_V2882 `pseq` tl kl_V2882
                                                   Atom (B (False)) -> do let pat_cond_4 kl_V2882 kl_V2882h kl_V2882t = do !appl_5 <- kl_V2882h `pseq` multiply (Types.Atom (Types.N (Types.KI 2))) kl_V2882h
                                                                                                                           !appl_6 <- appl_5 `pseq` (kl_V2882 `pseq` klCons appl_5 kl_V2882)
                                                                                                                           kl_V2881 `pseq` (appl_6 `pseq` kl_shen_multiples kl_V2881 appl_6)
                                                                              pat_cond_7 = do do let !aw_8 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                 applyWrapper aw_8 [ApplC (wrapNamed "shen.multiples" kl_shen_multiples)]
                                                                           in case kl_V2882 of
                                                                                  !(kl_V2882@(Cons (!kl_V2882h)
                                                                                                   (!kl_V2882t))) -> pat_cond_4 kl_V2882 kl_V2882h kl_V2882t
                                                                                  _ -> pat_cond_7
                                                   _ -> throwError "if: expected boolean"

kl_shen_modh :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_modh (!kl_V2887) (!kl_V2888) = do let pat_cond_0 = do return (Types.Atom (Types.N (Types.KI 0)))
                                              pat_cond_1 = do let pat_cond_2 = do return kl_V2887
                                                                  pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V2888 kl_V2888h kl_V2888t = do !kl_if_6 <- kl_V2888h `pseq` (kl_V2887 `pseq` greaterThan kl_V2888h kl_V2887)
                                                                                                                                               case kl_if_6 of
                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                  pat_cond_7 = do do return (Atom (B False))
                                                                                               in case kl_V2888 of
                                                                                                      !(kl_V2888@(Cons (!kl_V2888h)
                                                                                                                       (!kl_V2888t))) -> pat_cond_5 kl_V2888 kl_V2888h kl_V2888t
                                                                                                      _ -> pat_cond_7
                                                                                  case kl_if_4 of
                                                                                      Atom (B (True)) -> do !appl_8 <- kl_V2888 `pseq` tl kl_V2888
                                                                                                            !kl_if_9 <- appl_8 `pseq` kl_emptyP appl_8
                                                                                                            case kl_if_9 of
                                                                                                                Atom (B (True)) -> do return kl_V2887
                                                                                                                Atom (B (False)) -> do do !appl_10 <- kl_V2888 `pseq` tl kl_V2888
                                                                                                                                          kl_V2887 `pseq` (appl_10 `pseq` kl_shen_modh kl_V2887 appl_10)
                                                                                                                _ -> throwError "if: expected boolean"
                                                                                      Atom (B (False)) -> do let pat_cond_11 kl_V2888 kl_V2888h kl_V2888t = do !appl_12 <- kl_V2887 `pseq` (kl_V2888h `pseq` Primitives.subtract kl_V2887 kl_V2888h)
                                                                                                                                                               appl_12 `pseq` (kl_V2888 `pseq` kl_shen_modh appl_12 kl_V2888)
                                                                                                                 pat_cond_13 = do do let !aw_14 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                     applyWrapper aw_14 [ApplC (wrapNamed "shen.modh" kl_shen_modh)]
                                                                                                              in case kl_V2888 of
                                                                                                                     !(kl_V2888@(Cons (!kl_V2888h)
                                                                                                                                      (!kl_V2888t))) -> pat_cond_11 kl_V2888 kl_V2888h kl_V2888t
                                                                                                                     _ -> pat_cond_13
                                                                                      _ -> throwError "if: expected boolean"
                                                               in case kl_V2888 of
                                                                      kl_V2888@(Atom (Nil)) -> pat_cond_2
                                                                      _ -> pat_cond_3
                                           in case kl_V2887 of
                                                  kl_V2887@(Atom (N (KI 0))) -> pat_cond_0
                                                  _ -> pat_cond_1

kl_sum :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_sum (!kl_V2890) = do let pat_cond_0 = do return (Types.Atom (Types.N (Types.KI 0)))
                            pat_cond_1 kl_V2890 kl_V2890h kl_V2890t = do !appl_2 <- kl_V2890t `pseq` kl_sum kl_V2890t
                                                                         kl_V2890h `pseq` (appl_2 `pseq` add kl_V2890h appl_2)
                            pat_cond_3 = do do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                               applyWrapper aw_4 [ApplC (wrapNamed "sum" kl_sum)]
                         in case kl_V2890 of
                                kl_V2890@(Atom (Nil)) -> pat_cond_0
                                !(kl_V2890@(Cons (!kl_V2890h)
                                                 (!kl_V2890t))) -> pat_cond_1 kl_V2890 kl_V2890h kl_V2890t
                                _ -> pat_cond_3

kl_head :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_head (!kl_V2898) = do let pat_cond_0 kl_V2898 kl_V2898h kl_V2898t = do return kl_V2898h
                             pat_cond_1 = do do simpleError (Types.Atom (Types.Str "head expects a non-empty list"))
                          in case kl_V2898 of
                                 !(kl_V2898@(Cons (!kl_V2898h)
                                                  (!kl_V2898t))) -> pat_cond_0 kl_V2898 kl_V2898h kl_V2898t
                                 _ -> pat_cond_1

kl_tail :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_tail (!kl_V2906) = do let pat_cond_0 kl_V2906 kl_V2906h kl_V2906t = do return kl_V2906t
                             pat_cond_1 = do do simpleError (Types.Atom (Types.Str "tail expects a non-empty list"))
                          in case kl_V2906 of
                                 !(kl_V2906@(Cons (!kl_V2906h)
                                                  (!kl_V2906t))) -> pat_cond_0 kl_V2906 kl_V2906h kl_V2906t
                                 _ -> pat_cond_1

kl_hdstr :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_hdstr (!kl_V2908) = do kl_V2908 `pseq` pos kl_V2908 (Types.Atom (Types.N (Types.KI 0)))

kl_intersection :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_intersection (!kl_V2913) (!kl_V2914) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                                 pat_cond_1 kl_V2913 kl_V2913h kl_V2913t = do !kl_if_2 <- kl_V2913h `pseq` (kl_V2914 `pseq` kl_elementP kl_V2913h kl_V2914)
                                                                                              case kl_if_2 of
                                                                                                  Atom (B (True)) -> do !appl_3 <- kl_V2913t `pseq` (kl_V2914 `pseq` kl_intersection kl_V2913t kl_V2914)
                                                                                                                        kl_V2913h `pseq` (appl_3 `pseq` klCons kl_V2913h appl_3)
                                                                                                  Atom (B (False)) -> do do kl_V2913t `pseq` (kl_V2914 `pseq` kl_intersection kl_V2913t kl_V2914)
                                                                                                  _ -> throwError "if: expected boolean"
                                                 pat_cond_4 = do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                    applyWrapper aw_5 [ApplC (wrapNamed "intersection" kl_intersection)]
                                              in case kl_V2913 of
                                                     kl_V2913@(Atom (Nil)) -> pat_cond_0
                                                     !(kl_V2913@(Cons (!kl_V2913h)
                                                                      (!kl_V2913t))) -> pat_cond_1 kl_V2913 kl_V2913h kl_V2913t
                                                     _ -> pat_cond_4

kl_reverse :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_reverse (!kl_V2916) = do kl_V2916 `pseq` kl_shen_reverse_help kl_V2916 (Types.Atom Types.Nil)

kl_shen_reverse_help :: Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_reverse_help (!kl_V2919) (!kl_V2920) = do let pat_cond_0 = do return kl_V2920
                                                      pat_cond_1 kl_V2919 kl_V2919h kl_V2919t = do !appl_2 <- kl_V2919h `pseq` (kl_V2920 `pseq` klCons kl_V2919h kl_V2920)
                                                                                                   kl_V2919t `pseq` (appl_2 `pseq` kl_shen_reverse_help kl_V2919t appl_2)
                                                      pat_cond_3 = do do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                         applyWrapper aw_4 [ApplC (wrapNamed "shen.reverse_help" kl_shen_reverse_help)]
                                                   in case kl_V2919 of
                                                          kl_V2919@(Atom (Nil)) -> pat_cond_0
                                                          !(kl_V2919@(Cons (!kl_V2919h)
                                                                           (!kl_V2919t))) -> pat_cond_1 kl_V2919 kl_V2919h kl_V2919t
                                                          _ -> pat_cond_3

kl_union :: Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_union (!kl_V2923) (!kl_V2924) = do let pat_cond_0 = do return kl_V2924
                                          pat_cond_1 kl_V2923 kl_V2923h kl_V2923t = do !kl_if_2 <- kl_V2923h `pseq` (kl_V2924 `pseq` kl_elementP kl_V2923h kl_V2924)
                                                                                       case kl_if_2 of
                                                                                           Atom (B (True)) -> do kl_V2923t `pseq` (kl_V2924 `pseq` kl_union kl_V2923t kl_V2924)
                                                                                           Atom (B (False)) -> do do !appl_3 <- kl_V2923t `pseq` (kl_V2924 `pseq` kl_union kl_V2923t kl_V2924)
                                                                                                                     kl_V2923h `pseq` (appl_3 `pseq` klCons kl_V2923h appl_3)
                                                                                           _ -> throwError "if: expected boolean"
                                          pat_cond_4 = do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                             applyWrapper aw_5 [ApplC (wrapNamed "union" kl_union)]
                                       in case kl_V2923 of
                                              kl_V2923@(Atom (Nil)) -> pat_cond_0
                                              !(kl_V2923@(Cons (!kl_V2923h)
                                                               (!kl_V2923t))) -> pat_cond_1 kl_V2923 kl_V2923h kl_V2923t
                                              _ -> pat_cond_4

kl_y_or_nP :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_y_or_nP (!kl_V2926) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Message) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Y_or_N) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Input) -> do let pat_cond_3 = do return (Atom (B True))
                                                                                                                                                                                                                                   pat_cond_4 = do do let pat_cond_5 = do return (Atom (B False))
                                                                                                                                                                                                                                                          pat_cond_6 = do do !appl_7 <- kl_stoutput
                                                                                                                                                                                                                                                                             let !aw_8 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                             !appl_9 <- appl_7 `pseq` applyWrapper aw_8 [Types.Atom (Types.Str "please answer y or n\n"),
                                                                                                                                                                                                                                                                                                                         appl_7]
                                                                                                                                                                                                                                                                             !appl_10 <- kl_V2926 `pseq` kl_y_or_nP kl_V2926
                                                                                                                                                                                                                                                                             appl_9 `pseq` (appl_10 `pseq` kl_do appl_9 appl_10)
                                                                                                                                                                                                                                                       in case kl_Input of
                                                                                                                                                                                                                                                              kl_Input@(Atom (Str "n")) -> pat_cond_5
                                                                                                                                                                                                                                                              _ -> pat_cond_6
                                                                                                                                                                                                                                in case kl_Input of
                                                                                                                                                                                                                                       kl_Input@(Atom (Str "y")) -> pat_cond_3
                                                                                                                                                                                                                                       _ -> pat_cond_4)))
                                                                                                                                                               !appl_11 <- kl_stinput
                                                                                                                                                               let !aw_12 = Types.Atom (Types.UnboundSym "read")
                                                                                                                                                               !appl_13 <- appl_11 `pseq` applyWrapper aw_12 [appl_11]
                                                                                                                                                               let !aw_14 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                               !appl_15 <- appl_13 `pseq` applyWrapper aw_14 [appl_13,
                                                                                                                                                                                                              Types.Atom (Types.Str ""),
                                                                                                                                                                                                              Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                                               appl_15 `pseq` applyWrapper appl_2 [appl_15])))
                                                                                              !appl_16 <- kl_stoutput
                                                                                              let !aw_17 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                              !appl_18 <- appl_16 `pseq` applyWrapper aw_17 [Types.Atom (Types.Str " (y/n) "),
                                                                                                                                             appl_16]
                                                                                              appl_18 `pseq` applyWrapper appl_1 [appl_18])))
                            let !aw_19 = Types.Atom (Types.UnboundSym "shen.proc-nl")
                            !appl_20 <- kl_V2926 `pseq` applyWrapper aw_19 [kl_V2926]
                            !appl_21 <- kl_stoutput
                            let !aw_22 = Types.Atom (Types.UnboundSym "shen.prhush")
                            !appl_23 <- appl_20 `pseq` (appl_21 `pseq` applyWrapper aw_22 [appl_20,
                                                                                           appl_21])
                            appl_23 `pseq` applyWrapper appl_0 [appl_23]

kl_not :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_not (!kl_V2928) = do case kl_V2928 of
                            Atom (B (True)) -> do return (Atom (B False))
                            Atom (B (False)) -> do do return (Atom (B True))
                            _ -> throwError "if: expected boolean"

kl_subst :: Types.KLValue ->
            Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_subst (!kl_V2941) (!kl_V2942) (!kl_V2943) = do !kl_if_0 <- kl_V2943 `pseq` (kl_V2942 `pseq` eq kl_V2943 kl_V2942)
                                                  case kl_if_0 of
                                                      Atom (B (True)) -> do return kl_V2941
                                                      Atom (B (False)) -> do let pat_cond_1 kl_V2943 kl_V2943h kl_V2943t = do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_W) -> do kl_V2941 `pseq` (kl_V2942 `pseq` (kl_W `pseq` kl_subst kl_V2941 kl_V2942 kl_W)))))
                                                                                                                              appl_2 `pseq` (kl_V2943 `pseq` kl_map appl_2 kl_V2943)
                                                                                 pat_cond_3 = do do return kl_V2943
                                                                              in case kl_V2943 of
                                                                                     !(kl_V2943@(Cons (!kl_V2943h)
                                                                                                      (!kl_V2943t))) -> pat_cond_1 kl_V2943 kl_V2943h kl_V2943t
                                                                                     _ -> pat_cond_3
                                                      _ -> throwError "if: expected boolean"

kl_explode :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_explode (!kl_V2945) = do let !aw_0 = Types.Atom (Types.UnboundSym "shen.app")
                            !appl_1 <- kl_V2945 `pseq` applyWrapper aw_0 [kl_V2945,
                                                                          Types.Atom (Types.Str ""),
                                                                          Types.Atom (Types.UnboundSym "shen.a")]
                            appl_1 `pseq` kl_shen_explode_h appl_1

kl_shen_explode_h :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_explode_h (!kl_V2947) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                       pat_cond_1 = do !kl_if_2 <- kl_V2947 `pseq` kl_shen_PlusstringP kl_V2947
                                                       case kl_if_2 of
                                                           Atom (B (True)) -> do !appl_3 <- kl_V2947 `pseq` pos kl_V2947 (Types.Atom (Types.N (Types.KI 0)))
                                                                                 !appl_4 <- kl_V2947 `pseq` tlstr kl_V2947
                                                                                 !appl_5 <- appl_4 `pseq` kl_shen_explode_h appl_4
                                                                                 appl_3 `pseq` (appl_5 `pseq` klCons appl_3 appl_5)
                                                           Atom (B (False)) -> do do let !aw_6 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                     applyWrapper aw_6 [ApplC (wrapNamed "shen.explode-h" kl_shen_explode_h)]
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V2947 of
                                           kl_V2947@(Atom (Str "")) -> pat_cond_0
                                           _ -> pat_cond_1

kl_cd :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_cd (!kl_V2949) = do !appl_0 <- let pat_cond_1 = do return (Types.Atom (Types.Str ""))
                                      pat_cond_2 = do do let !aw_3 = Types.Atom (Types.UnboundSym "shen.app")
                                                         kl_V2949 `pseq` applyWrapper aw_3 [kl_V2949,
                                                                                            Types.Atom (Types.Str "/"),
                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                   in case kl_V2949 of
                                          kl_V2949@(Atom (Str "")) -> pat_cond_1
                                          _ -> pat_cond_2
                       appl_0 `pseq` klSet (Types.Atom (Types.UnboundSym "*home-directory*")) appl_0

kl_map :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_map (!kl_V2952) (!kl_V2953) = do kl_V2952 `pseq` (kl_V2953 `pseq` kl_shen_map_h kl_V2952 kl_V2953 (Types.Atom Types.Nil))

kl_shen_map_h :: Types.KLValue ->
                 Types.KLValue ->
                 Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_map_h (!kl_V2959) (!kl_V2960) (!kl_V2961) = do let pat_cond_0 = do kl_V2961 `pseq` kl_reverse kl_V2961
                                                           pat_cond_1 kl_V2960 kl_V2960h kl_V2960t = do !appl_2 <- kl_V2960h `pseq` applyWrapper kl_V2959 [kl_V2960h]
                                                                                                        !appl_3 <- appl_2 `pseq` (kl_V2961 `pseq` klCons appl_2 kl_V2961)
                                                                                                        kl_V2959 `pseq` (kl_V2960t `pseq` (appl_3 `pseq` kl_shen_map_h kl_V2959 kl_V2960t appl_3))
                                                           pat_cond_4 = do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                              applyWrapper aw_5 [ApplC (wrapNamed "shen.map-h" kl_shen_map_h)]
                                                        in case kl_V2960 of
                                                               kl_V2960@(Atom (Nil)) -> pat_cond_0
                                                               !(kl_V2960@(Cons (!kl_V2960h)
                                                                                (!kl_V2960t))) -> pat_cond_1 kl_V2960 kl_V2960h kl_V2960t
                                                               _ -> pat_cond_4

kl_length :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_length (!kl_V2963) = do kl_V2963 `pseq` kl_shen_length_h kl_V2963 (Types.Atom (Types.N (Types.KI 0)))

kl_shen_length_h :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_length_h (!kl_V2966) (!kl_V2967) = do let pat_cond_0 = do return kl_V2967
                                                  pat_cond_1 = do do !appl_2 <- kl_V2966 `pseq` tl kl_V2966
                                                                     !appl_3 <- kl_V2967 `pseq` add kl_V2967 (Types.Atom (Types.N (Types.KI 1)))
                                                                     appl_2 `pseq` (appl_3 `pseq` kl_shen_length_h appl_2 appl_3)
                                               in case kl_V2966 of
                                                      kl_V2966@(Atom (Nil)) -> pat_cond_0
                                                      _ -> pat_cond_1

kl_occurrences :: Types.KLValue ->
                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_occurrences (!kl_V2979) (!kl_V2980) = do !kl_if_0 <- kl_V2980 `pseq` (kl_V2979 `pseq` eq kl_V2980 kl_V2979)
                                            case kl_if_0 of
                                                Atom (B (True)) -> do return (Types.Atom (Types.N (Types.KI 1)))
                                                Atom (B (False)) -> do let pat_cond_1 kl_V2980 kl_V2980h kl_V2980t = do !appl_2 <- kl_V2979 `pseq` (kl_V2980h `pseq` kl_occurrences kl_V2979 kl_V2980h)
                                                                                                                        !appl_3 <- kl_V2979 `pseq` (kl_V2980t `pseq` kl_occurrences kl_V2979 kl_V2980t)
                                                                                                                        appl_2 `pseq` (appl_3 `pseq` add appl_2 appl_3)
                                                                           pat_cond_4 = do do return (Types.Atom (Types.N (Types.KI 0)))
                                                                        in case kl_V2980 of
                                                                               !(kl_V2980@(Cons (!kl_V2980h)
                                                                                                (!kl_V2980t))) -> pat_cond_1 kl_V2980 kl_V2980h kl_V2980t
                                                                               _ -> pat_cond_4
                                                _ -> throwError "if: expected boolean"

kl_nth :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_nth (!kl_V2989) (!kl_V2990) = do !kl_if_0 <- let pat_cond_1 = do let pat_cond_2 kl_V2990 kl_V2990h kl_V2990t = do return (Atom (B True))
                                                                        pat_cond_3 = do do return (Atom (B False))
                                                                     in case kl_V2990 of
                                                                            !(kl_V2990@(Cons (!kl_V2990h)
                                                                                             (!kl_V2990t))) -> pat_cond_2 kl_V2990 kl_V2990h kl_V2990t
                                                                            _ -> pat_cond_3
                                                    pat_cond_4 = do do return (Atom (B False))
                                                 in case kl_V2989 of
                                                        kl_V2989@(Atom (N (KI 1))) -> pat_cond_1
                                                        _ -> pat_cond_4
                                    case kl_if_0 of
                                        Atom (B (True)) -> do kl_V2990 `pseq` hd kl_V2990
                                        Atom (B (False)) -> do let pat_cond_5 kl_V2990 kl_V2990h kl_V2990t = do !appl_6 <- kl_V2989 `pseq` Primitives.subtract kl_V2989 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                appl_6 `pseq` (kl_V2990t `pseq` kl_nth appl_6 kl_V2990t)
                                                                   pat_cond_7 = do do let !aw_8 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                      applyWrapper aw_8 [ApplC (wrapNamed "nth" kl_nth)]
                                                                in case kl_V2990 of
                                                                       !(kl_V2990@(Cons (!kl_V2990h)
                                                                                        (!kl_V2990t))) -> pat_cond_5 kl_V2990 kl_V2990h kl_V2990t
                                                                       _ -> pat_cond_7
                                        _ -> throwError "if: expected boolean"

{-
kl_integerP :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_integerP (!kl_V2992) = do !kl_if_0 <- kl_V2992 `pseq` numberP kl_V2992
                             case kl_if_0 of
                                 Atom (B (True)) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Abs) -> do !appl_2 <- kl_Abs `pseq` kl_shen_magless kl_Abs (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                     kl_Abs `pseq` (appl_2 `pseq` kl_shen_integer_testP kl_Abs appl_2))))
                                                       !appl_3 <- kl_V2992 `pseq` kl_shen_abs kl_V2992
                                                       !kl_if_4 <- appl_3 `pseq` applyWrapper appl_1 [appl_3]
                                                       case kl_if_4 of
                                                           Atom (B (True)) -> do return (Atom (B True))
                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                           _ -> throwError "if: expected boolean"
                                 Atom (B (False)) -> do do return (Atom (B False))
                                 _ -> throwError "if: expected boolean"
-}

kl_integerP :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_integerP (Atom (N (KI _))) = return (Atom (B True))
kl_integerP (Atom (N (KD d))) = return (Atom (B (fromInteger (round d) == d)))
kl_integerP !v = return (Atom (B False))

kl_shen_abs :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_shen_abs (!kl_V2994) = do !kl_if_0 <- kl_V2994 `pseq` greaterThan kl_V2994 (Types.Atom (Types.N (Types.KI 0)))
                             case kl_if_0 of
                                 Atom (B (True)) -> do return kl_V2994
                                 Atom (B (False)) -> do do kl_V2994 `pseq` Primitives.subtract (Types.Atom (Types.N (Types.KI 0))) kl_V2994
                                 _ -> throwError "if: expected boolean"

kl_shen_magless :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_magless (!kl_V2997) (!kl_V2998) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Nx2) -> do !kl_if_1 <- kl_Nx2 `pseq` (kl_V2997 `pseq` greaterThan kl_Nx2 kl_V2997)
                                                                                                           case kl_if_1 of
                                                                                                               Atom (B (True)) -> do return kl_V2998
                                                                                                               Atom (B (False)) -> do do kl_V2997 `pseq` (kl_Nx2 `pseq` kl_shen_magless kl_V2997 kl_Nx2)
                                                                                                               _ -> throwError "if: expected boolean")))
                                             !appl_2 <- kl_V2998 `pseq` multiply kl_V2998 (Types.Atom (Types.N (Types.KI 2)))
                                             appl_2 `pseq` applyWrapper appl_0 [appl_2]

kl_shen_integer_testP :: Types.KLValue ->
                         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_integer_testP (!kl_V3004) (!kl_V3005) = do let pat_cond_0 = do return (Atom (B True))
                                                       pat_cond_1 = do !kl_if_2 <- kl_V3004 `pseq` greaterThan (Types.Atom (Types.N (Types.KI 1))) kl_V3004
                                                                       case kl_if_2 of
                                                                           Atom (B (True)) -> do return (Atom (B False))
                                                                           Atom (B (False)) -> do do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Abs_N) -> do !kl_if_4 <- kl_Abs_N `pseq` greaterThan (Types.Atom (Types.N (Types.KI 0))) kl_Abs_N
                                                                                                                                                                     case kl_if_4 of
                                                                                                                                                                         Atom (B (True)) -> do kl_V3004 `pseq` kl_integerP kl_V3004
                                                                                                                                                                         Atom (B (False)) -> do do kl_Abs_N `pseq` (kl_V3005 `pseq` kl_shen_integer_testP kl_Abs_N kl_V3005)
                                                                                                                                                                         _ -> throwError "if: expected boolean")))
                                                                                                     !appl_5 <- kl_V3004 `pseq` (kl_V3005 `pseq` Primitives.subtract kl_V3004 kl_V3005)
                                                                                                     appl_5 `pseq` applyWrapper appl_3 [appl_5]
                                                                           _ -> throwError "if: expected boolean"
                                                    in case kl_V3004 of
                                                           kl_V3004@(Atom (N (KI 0))) -> pat_cond_0
                                                           _ -> pat_cond_1

kl_mapcan :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_mapcan (!kl_V3010) (!kl_V3011) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                           pat_cond_1 kl_V3011 kl_V3011h kl_V3011t = do !appl_2 <- kl_V3011h `pseq` applyWrapper kl_V3010 [kl_V3011h]
                                                                                        !appl_3 <- kl_V3010 `pseq` (kl_V3011t `pseq` kl_mapcan kl_V3010 kl_V3011t)
                                                                                        appl_2 `pseq` (appl_3 `pseq` kl_append appl_2 appl_3)
                                           pat_cond_4 = do do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                              applyWrapper aw_5 [ApplC (wrapNamed "mapcan" kl_mapcan)]
                                        in case kl_V3011 of
                                               kl_V3011@(Atom (Nil)) -> pat_cond_0
                                               !(kl_V3011@(Cons (!kl_V3011h)
                                                                (!kl_V3011t))) -> pat_cond_1 kl_V3011 kl_V3011h kl_V3011t
                                               _ -> pat_cond_4

kl_EqEq :: Types.KLValue ->
           Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_EqEq (!kl_V3023) (!kl_V3024) = do !kl_if_0 <- kl_V3024 `pseq` (kl_V3023 `pseq` eq kl_V3024 kl_V3023)
                                     case kl_if_0 of
                                         Atom (B (True)) -> do return (Atom (B True))
                                         Atom (B (False)) -> do do return (Atom (B False))
                                         _ -> throwError "if: expected boolean"

kl_abort :: Types.KLContext Types.Env Types.KLValue
kl_abort = do simpleError (Types.Atom (Types.Str ""))

kl_boundP :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_boundP (!kl_V3026) = do !kl_if_0 <- kl_V3026 `pseq` kl_symbolP kl_V3026
                           case kl_if_0 of
                               Atom (B (True)) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Val) -> do let pat_cond_2 = do return (Atom (B False))
                                                                                                                       pat_cond_3 = do do return (Atom (B True))
                                                                                                                    in case kl_Val of
                                                                                                                           kl_Val@(Atom (UnboundSym "shen.this-symbol-is-unbound")) -> pat_cond_2
                                                                                                                           kl_Val@(ApplC (PL "shen.this-symbol-is-unbound"
                                                                                                                                             _)) -> pat_cond_2
                                                                                                                           kl_Val@(ApplC (Func "shen.this-symbol-is-unbound"
                                                                                                                                               _)) -> pat_cond_2
                                                                                                                           _ -> pat_cond_3)))
                                                     !appl_4 <- (do kl_V3026 `pseq` value kl_V3026) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.this-symbol-is-unbound")))
                                                     !kl_if_5 <- appl_4 `pseq` applyWrapper appl_1 [appl_4]
                                                     case kl_if_5 of
                                                         Atom (B (True)) -> do return (Atom (B True))
                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                         _ -> throwError "if: expected boolean"
                               Atom (B (False)) -> do do return (Atom (B False))
                               _ -> throwError "if: expected boolean"

kl_shen_string_RBbytes :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_string_RBbytes (!kl_V3028) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                            pat_cond_1 = do do !appl_2 <- kl_V3028 `pseq` pos kl_V3028 (Types.Atom (Types.N (Types.KI 0)))
                                                               !appl_3 <- appl_2 `pseq` stringToN appl_2
                                                               !appl_4 <- kl_V3028 `pseq` tlstr kl_V3028
                                                               !appl_5 <- appl_4 `pseq` kl_shen_string_RBbytes appl_4
                                                               appl_3 `pseq` (appl_5 `pseq` klCons appl_3 appl_5)
                                         in case kl_V3028 of
                                                kl_V3028@(Atom (Str "")) -> pat_cond_0
                                                _ -> pat_cond_1

kl_maxinferences :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_maxinferences (!kl_V3030) = do kl_V3030 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*maxinferences*")) kl_V3030

kl_inferences :: Types.KLContext Types.Env Types.KLValue
kl_inferences = do value (Types.Atom (Types.UnboundSym "shen.*infs*"))

kl_protect :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_protect (!kl_V3032) = do return kl_V3032

kl_stoutput :: Types.KLContext Types.Env Types.KLValue
kl_stoutput = do value (Types.Atom (Types.UnboundSym "*stoutput*"))

kl_string_RBsymbol :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_string_RBsymbol (!kl_V3034) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Symbol) -> do !kl_if_1 <- kl_Symbol `pseq` kl_symbolP kl_Symbol
                                                                                                     case kl_if_1 of
                                                                                                         Atom (B (True)) -> do return kl_Symbol
                                                                                                         Atom (B (False)) -> do do let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                   !appl_3 <- kl_V3034 `pseq` applyWrapper aw_2 [kl_V3034,
                                                                                                                                                                                 Types.Atom (Types.Str " to a symbol"),
                                                                                                                                                                                 Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                   !appl_4 <- appl_3 `pseq` cn (Types.Atom (Types.Str "cannot intern ")) appl_3
                                                                                                                                   appl_4 `pseq` simpleError appl_4
                                                                                                         _ -> throwError "if: expected boolean")))
                                    !appl_5 <- kl_V3034 `pseq` intern kl_V3034
                                    appl_5 `pseq` applyWrapper appl_0 [appl_5]

kl_optimise :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_optimise (!kl_V3040) = do let pat_cond_0 = do klSet (Types.Atom (Types.UnboundSym "shen.*optimise*")) (Atom (B True))
                                 pat_cond_1 = do klSet (Types.Atom (Types.UnboundSym "shen.*optimise*")) (Atom (B False))
                                 pat_cond_2 = do do simpleError (Types.Atom (Types.Str "optimise expects a + or a -.\n"))
                              in case kl_V3040 of
                                     kl_V3040@(Atom (UnboundSym "+")) -> pat_cond_0
                                     kl_V3040@(ApplC (PL "+" _)) -> pat_cond_0
                                     kl_V3040@(ApplC (Func "+" _)) -> pat_cond_0
                                     kl_V3040@(Atom (UnboundSym "-")) -> pat_cond_1
                                     kl_V3040@(ApplC (PL "-" _)) -> pat_cond_1
                                     kl_V3040@(ApplC (Func "-" _)) -> pat_cond_1
                                     _ -> pat_cond_2

kl_os :: Types.KLContext Types.Env Types.KLValue
kl_os = do value (Types.Atom (Types.UnboundSym "*os*"))

kl_language :: Types.KLContext Types.Env Types.KLValue
kl_language = do value (Types.Atom (Types.UnboundSym "*language*"))

kl_version :: Types.KLContext Types.Env Types.KLValue
kl_version = do value (Types.Atom (Types.UnboundSym "*version*"))

kl_port :: Types.KLContext Types.Env Types.KLValue
kl_port = do value (Types.Atom (Types.UnboundSym "*port*"))

kl_porters :: Types.KLContext Types.Env Types.KLValue
kl_porters = do value (Types.Atom (Types.UnboundSym "*porters*"))

kl_implementation :: Types.KLContext Types.Env Types.KLValue
kl_implementation = do value (Types.Atom (Types.UnboundSym "*implementation*"))

kl_release :: Types.KLContext Types.Env Types.KLValue
kl_release = do value (Types.Atom (Types.UnboundSym "*release*"))

kl_packageP :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_packageP (!kl_V3042) = do (do !appl_0 <- kl_V3042 `pseq` kl_external kl_V3042
                                 appl_0 `pseq` kl_do appl_0 (Atom (B True))) `catchError` (\(!kl_E) -> do return (Atom (B False)))

kl_function :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_function (!kl_V3044) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*symbol-table*"))
                             kl_V3044 `pseq` (appl_0 `pseq` kl_shen_lookup_func kl_V3044 appl_0)

kl_shen_lookup_func :: Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_lookup_func (!kl_V3054) (!kl_V3055) = do let pat_cond_0 = do let !aw_1 = Types.Atom (Types.UnboundSym "shen.app")
                                                                     !appl_2 <- kl_V3054 `pseq` applyWrapper aw_1 [kl_V3054,
                                                                                                                   Types.Atom (Types.Str " has no lambda expansion\n"),
                                                                                                                   Types.Atom (Types.UnboundSym "shen.a")]
                                                                     appl_2 `pseq` simpleError appl_2
                                                     pat_cond_3 kl_V3055 kl_V3055h kl_V3055hh kl_V3055ht kl_V3055t = do return kl_V3055ht
                                                     pat_cond_4 kl_V3055 kl_V3055h kl_V3055t = do kl_V3054 `pseq` (kl_V3055t `pseq` kl_shen_lookup_func kl_V3054 kl_V3055t)
                                                     pat_cond_5 = do do let !aw_6 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                        applyWrapper aw_6 [ApplC (wrapNamed "shen.lookup-func" kl_shen_lookup_func)]
                                                  in case kl_V3055 of
                                                         kl_V3055@(Atom (Nil)) -> pat_cond_0
                                                         !(kl_V3055@(Cons (!(kl_V3055h@(Cons (!kl_V3055hh)
                                                                                             (!kl_V3055ht))))
                                                                          (!kl_V3055t))) | eqCore kl_V3055hh kl_V3054 -> pat_cond_3 kl_V3055 kl_V3055h kl_V3055hh kl_V3055ht kl_V3055t
                                                         !(kl_V3055@(Cons (!kl_V3055h)
                                                                          (!kl_V3055t))) -> pat_cond_4 kl_V3055 kl_V3055h kl_V3055t
                                                         _ -> pat_cond_5

expr2 :: Types.KLContext Types.Env Types.KLValue
expr2 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
