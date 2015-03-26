{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

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

module Sys where

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

kl_thaw :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_thaw (!kl_V1483) = do applyWrapper kl_V1483 []

kl_eval :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_eval (!kl_V1484) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Macroexpand) -> do !kl_if_1 <- kl_Macroexpand `pseq` kl_shen_packagedP kl_Macroexpand
                                                                                               klIf kl_if_1 (do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_V1478) -> do kl_V1478 `pseq` kl_shen_eval_without_macros kl_V1478)))
                                                                                                                !appl_3 <- kl_Macroexpand `pseq` kl_shen_package_contents kl_Macroexpand
                                                                                                                appl_2 `pseq` (appl_3 `pseq` kl_map appl_2 appl_3)) (do kl_Macroexpand `pseq` kl_shen_eval_without_macros kl_Macroexpand))))
                         let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_V1477) -> do let !aw_5 = Types.Atom (Types.UnboundSym "macroexpand")
                                                                                         kl_V1477 `pseq` applyWrapper aw_5 [kl_V1477])))
                         !appl_6 <- appl_4 `pseq` (kl_V1484 `pseq` kl_shen_walk appl_4 kl_V1484)
                         appl_6 `pseq` applyWrapper appl_0 [appl_6]

kl_shen_eval_without_macros :: Types.KLValue ->
                               Types.KLContext Types.Env Types.KLValue
kl_shen_eval_without_macros (!kl_V1485) = do !appl_0 <- kl_V1485 `pseq` kl_shen_proc_inputPlus kl_V1485
                                             !appl_1 <- appl_0 `pseq` kl_shen_elim_def appl_0
                                             appl_1 `pseq` evalKL appl_1

kl_shen_proc_inputPlus :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_proc_inputPlus (!kl_V1486) = do !kl_if_0 <- kl_V1486 `pseq` consP kl_V1486
                                        !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V1486 `pseq` hd kl_V1486
                                                                     !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "input+")) appl_2
                                                                     klIf kl_if_3 (do !appl_4 <- kl_V1486 `pseq` tl kl_V1486
                                                                                      !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                      klIf kl_if_5 (do !appl_6 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                       !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                       !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                       klIf kl_if_8 (do let !appl_9 = List []
                                                                                                                        !appl_10 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                                        !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                        !appl_12 <- appl_11 `pseq` tl appl_11
                                                                                                                        appl_9 `pseq` (appl_12 `pseq` eq appl_9 appl_12)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                        klIf kl_if_1 (do !appl_13 <- kl_V1486 `pseq` tl kl_V1486
                                                         !appl_14 <- appl_13 `pseq` hd appl_13
                                                         let !aw_15 = Types.Atom (Types.UnboundSym "shen.rcons_form")
                                                         !appl_16 <- appl_14 `pseq` applyWrapper aw_15 [appl_14]
                                                         !appl_17 <- kl_V1486 `pseq` tl kl_V1486
                                                         !appl_18 <- appl_17 `pseq` tl appl_17
                                                         !appl_19 <- appl_16 `pseq` (appl_18 `pseq` klCons appl_16 appl_18)
                                                         appl_19 `pseq` klCons (Types.Atom (Types.UnboundSym "input+")) appl_19) (do !kl_if_20 <- kl_V1486 `pseq` consP kl_V1486
                                                                                                                                     !kl_if_21 <- klIf kl_if_20 (do !appl_22 <- kl_V1486 `pseq` hd kl_V1486
                                                                                                                                                                    !kl_if_23 <- appl_22 `pseq` eq (Types.Atom (Types.UnboundSym "shen.read+")) appl_22
                                                                                                                                                                    klIf kl_if_23 (do !appl_24 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                                                                                                      !kl_if_25 <- appl_24 `pseq` consP appl_24
                                                                                                                                                                                      klIf kl_if_25 (do !appl_26 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                                                                                                                        !appl_27 <- appl_26 `pseq` tl appl_26
                                                                                                                                                                                                        !kl_if_28 <- appl_27 `pseq` consP appl_27
                                                                                                                                                                                                        klIf kl_if_28 (do let !appl_29 = List []
                                                                                                                                                                                                                          !appl_30 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                                                                                                                                          !appl_31 <- appl_30 `pseq` tl appl_30
                                                                                                                                                                                                                          !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                                                          appl_29 `pseq` (appl_32 `pseq` eq appl_29 appl_32)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                     klIf kl_if_21 (do !appl_33 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                                                                       !appl_34 <- appl_33 `pseq` hd appl_33
                                                                                                                                                       let !aw_35 = Types.Atom (Types.UnboundSym "shen.rcons_form")
                                                                                                                                                       !appl_36 <- appl_34 `pseq` applyWrapper aw_35 [appl_34]
                                                                                                                                                       !appl_37 <- kl_V1486 `pseq` tl kl_V1486
                                                                                                                                                       !appl_38 <- appl_37 `pseq` tl appl_37
                                                                                                                                                       !appl_39 <- appl_36 `pseq` (appl_38 `pseq` klCons appl_36 appl_38)
                                                                                                                                                       appl_39 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.read+")) appl_39) (do !kl_if_40 <- kl_V1486 `pseq` consP kl_V1486
                                                                                                                                                                                                                                       klIf kl_if_40 (do let !appl_41 = ApplC (Func "lambda" (Context (\(!kl_V1479) -> do kl_V1479 `pseq` kl_shen_proc_inputPlus kl_V1479)))
                                                                                                                                                                                                                                                         appl_41 `pseq` (kl_V1486 `pseq` kl_map appl_41 kl_V1486)) (do klIf (Atom (B True)) (do return kl_V1486) (do return (List [])))))

kl_shen_elim_def :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_elim_def (!kl_V1487) = do !kl_if_0 <- kl_V1487 `pseq` consP kl_V1487
                                  !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V1487 `pseq` hd kl_V1487
                                                               !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "define")) appl_2
                                                               klIf kl_if_3 (do !appl_4 <- kl_V1487 `pseq` tl kl_V1487
                                                                                appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                  klIf kl_if_1 (do !appl_5 <- kl_V1487 `pseq` tl kl_V1487
                                                   !appl_6 <- appl_5 `pseq` hd appl_5
                                                   !appl_7 <- kl_V1487 `pseq` tl kl_V1487
                                                   !appl_8 <- appl_7 `pseq` tl appl_7
                                                   appl_6 `pseq` (appl_8 `pseq` kl_shen_shen_RBkl appl_6 appl_8)) (do !kl_if_9 <- kl_V1487 `pseq` consP kl_V1487
                                                                                                                      !kl_if_10 <- klIf kl_if_9 (do !appl_11 <- kl_V1487 `pseq` hd kl_V1487
                                                                                                                                                    !kl_if_12 <- appl_11 `pseq` eq (Types.Atom (Types.UnboundSym "defmacro")) appl_11
                                                                                                                                                    klIf kl_if_12 (do !appl_13 <- kl_V1487 `pseq` tl kl_V1487
                                                                                                                                                                      appl_13 `pseq` consP appl_13) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                      klIf kl_if_10 (do let !appl_14 = ApplC (Func "lambda" (Context (\(!kl_Default) -> do let !appl_15 = ApplC (Func "lambda" (Context (\(!kl_Def) -> do let !appl_16 = ApplC (Func "lambda" (Context (\(!kl_MacroAdd) -> do return kl_Def)))
                                                                                                                                                                                                                                                                          !appl_17 <- kl_V1487 `pseq` tl kl_V1487
                                                                                                                                                                                                                                                                          !appl_18 <- appl_17 `pseq` hd appl_17
                                                                                                                                                                                                                                                                          !appl_19 <- appl_18 `pseq` kl_shen_add_macro appl_18
                                                                                                                                                                                                                                                                          appl_19 `pseq` applyWrapper appl_16 [appl_19])))
                                                                                                                                                                                                           !appl_20 <- kl_V1487 `pseq` tl kl_V1487
                                                                                                                                                                                                           !appl_21 <- appl_20 `pseq` hd appl_20
                                                                                                                                                                                                           !appl_22 <- kl_V1487 `pseq` tl kl_V1487
                                                                                                                                                                                                           !appl_23 <- appl_22 `pseq` tl appl_22
                                                                                                                                                                                                           !appl_24 <- appl_23 `pseq` (kl_Default `pseq` kl_append appl_23 kl_Default)
                                                                                                                                                                                                           !appl_25 <- appl_21 `pseq` (appl_24 `pseq` klCons appl_21 appl_24)
                                                                                                                                                                                                           !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_25
                                                                                                                                                                                                           !appl_27 <- appl_26 `pseq` kl_shen_elim_def appl_26
                                                                                                                                                                                                           appl_27 `pseq` applyWrapper appl_15 [appl_27])))
                                                                                                                                        let !appl_28 = List []
                                                                                                                                        !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_28
                                                                                                                                        !appl_30 <- appl_29 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_29
                                                                                                                                        !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_30
                                                                                                                                        appl_31 `pseq` applyWrapper appl_14 [appl_31]) (do !kl_if_32 <- kl_V1487 `pseq` consP kl_V1487
                                                                                                                                                                                           !kl_if_33 <- klIf kl_if_32 (do !appl_34 <- kl_V1487 `pseq` hd kl_V1487
                                                                                                                                                                                                                          !kl_if_35 <- appl_34 `pseq` eq (Types.Atom (Types.UnboundSym "defcc")) appl_34
                                                                                                                                                                                                                          klIf kl_if_35 (do !appl_36 <- kl_V1487 `pseq` tl kl_V1487
                                                                                                                                                                                                                                            appl_36 `pseq` consP appl_36) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                           klIf kl_if_33 (do let !aw_37 = Types.Atom (Types.UnboundSym "shen.yacc")
                                                                                                                                                                                                             !appl_38 <- kl_V1487 `pseq` applyWrapper aw_37 [kl_V1487]
                                                                                                                                                                                                             appl_38 `pseq` kl_shen_elim_def appl_38) (do !kl_if_39 <- kl_V1487 `pseq` consP kl_V1487
                                                                                                                                                                                                                                                          klIf kl_if_39 (do let !appl_40 = ApplC (Func "lambda" (Context (\(!kl_V1480) -> do kl_V1480 `pseq` kl_shen_elim_def kl_V1480)))
                                                                                                                                                                                                                                                                            appl_40 `pseq` (kl_V1487 `pseq` kl_map appl_40 kl_V1487)) (do klIf (Atom (B True)) (do return kl_V1487) (do return (List []))))))

kl_shen_add_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_add_macro (!kl_V1488) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_MacroReg) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_NewMacroReg) -> do !kl_if_2 <- kl_MacroReg `pseq` (kl_NewMacroReg `pseq` eq kl_MacroReg kl_NewMacroReg)
                                                                                                                                                                            klIf kl_if_2 (do return (Types.Atom (Types.UnboundSym "shen.skip"))) (do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_V1481) -> do kl_V1481 `pseq` applyWrapper kl_V1488 [kl_V1481])))
                                                                                                                                                                                                                                                     !appl_4 <- value (Types.Atom (Types.UnboundSym "*macros*"))
                                                                                                                                                                                                                                                     !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                                                                                                                                                                     appl_5 `pseq` klSet (Types.Atom (Types.UnboundSym "*macros*")) appl_5))))
                                                                                                      !appl_6 <- value (Types.Atom (Types.UnboundSym "shen.*macroreg*"))
                                                                                                      let !aw_7 = Types.Atom (Types.UnboundSym "adjoin")
                                                                                                      !appl_8 <- kl_V1488 `pseq` (appl_6 `pseq` applyWrapper aw_7 [kl_V1488,
                                                                                                                                                                   appl_6])
                                                                                                      !appl_9 <- appl_8 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*macroreg*")) appl_8
                                                                                                      appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                                   !appl_10 <- value (Types.Atom (Types.UnboundSym "shen.*macroreg*"))
                                   appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_packagedP :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_packagedP (!kl_V1495) = do !kl_if_0 <- kl_V1495 `pseq` consP kl_V1495
                                   !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V1495 `pseq` hd kl_V1495
                                                                !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "package")) appl_2
                                                                klIf kl_if_3 (do !appl_4 <- kl_V1495 `pseq` tl kl_V1495
                                                                                 !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                 klIf kl_if_5 (do !appl_6 <- kl_V1495 `pseq` tl kl_V1495
                                                                                                  !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                  appl_7 `pseq` consP appl_7) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                   klIf kl_if_1 (do return (Atom (B True))) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List [])))

kl_external :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_external (!kl_V1496) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                 kl_V1496 `pseq` (appl_0 `pseq` kl_get kl_V1496 (Types.Atom (Types.UnboundSym "shen.external-symbols")) appl_0)) `catchError` (\(!kl_E) -> do let !aw_1 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                              !appl_2 <- kl_V1496 `pseq` applyWrapper aw_1 [kl_V1496,
                                                                                                                                                                                                                            Types.Atom (Types.Str " has not been used.\n"),
                                                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                                              !appl_3 <- appl_2 `pseq` cn (Types.Atom (Types.Str "package ")) appl_2
                                                                                                                                                                              appl_3 `pseq` simpleError appl_3)

kl_shen_package_contents :: Types.KLValue ->
                            Types.KLContext Types.Env Types.KLValue
kl_shen_package_contents (!kl_V1499) = do !kl_if_0 <- kl_V1499 `pseq` consP kl_V1499
                                          !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V1499 `pseq` hd kl_V1499
                                                                       !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "package")) appl_2
                                                                       klIf kl_if_3 (do !appl_4 <- kl_V1499 `pseq` tl kl_V1499
                                                                                        !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                        klIf kl_if_5 (do !appl_6 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                         !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                         !kl_if_8 <- appl_7 `pseq` eq (Types.Atom (Types.UnboundSym "null")) appl_7
                                                                                                         klIf kl_if_8 (do !appl_9 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                                          !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                          appl_10 `pseq` consP appl_10) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                          klIf kl_if_1 (do !appl_11 <- kl_V1499 `pseq` tl kl_V1499
                                                           !appl_12 <- appl_11 `pseq` tl appl_11
                                                           appl_12 `pseq` tl appl_12) (do !kl_if_13 <- kl_V1499 `pseq` consP kl_V1499
                                                                                          !kl_if_14 <- klIf kl_if_13 (do !appl_15 <- kl_V1499 `pseq` hd kl_V1499
                                                                                                                         !kl_if_16 <- appl_15 `pseq` eq (Types.Atom (Types.UnboundSym "package")) appl_15
                                                                                                                         klIf kl_if_16 (do !appl_17 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                                                           !kl_if_18 <- appl_17 `pseq` consP appl_17
                                                                                                                                           klIf kl_if_18 (do !appl_19 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                                                                             !appl_20 <- appl_19 `pseq` tl appl_19
                                                                                                                                                             appl_20 `pseq` consP appl_20) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                          klIf kl_if_14 (do !appl_21 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                            !appl_22 <- appl_21 `pseq` hd appl_21
                                                                                                            !appl_23 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                            !appl_24 <- appl_23 `pseq` tl appl_23
                                                                                                            !appl_25 <- appl_24 `pseq` hd appl_24
                                                                                                            !appl_26 <- kl_V1499 `pseq` tl kl_V1499
                                                                                                            !appl_27 <- appl_26 `pseq` tl appl_26
                                                                                                            !appl_28 <- appl_27 `pseq` tl appl_27
                                                                                                            let !aw_29 = Types.Atom (Types.UnboundSym "shen.packageh")
                                                                                                            appl_22 `pseq` (appl_25 `pseq` (appl_28 `pseq` applyWrapper aw_29 [appl_22,
                                                                                                                                                                               appl_25,
                                                                                                                                                                               appl_28]))) (do klIf (Atom (B True)) (do let !aw_30 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                        applyWrapper aw_30 [ApplC (wrapNamed "shen.package-contents" kl_shen_package_contents)]) (do return (List []))))

kl_shen_walk :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_walk (!kl_V1500) (!kl_V1501) = do !kl_if_0 <- kl_V1501 `pseq` consP kl_V1501
                                          klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_V1500 `pseq` (kl_Z `pseq` kl_shen_walk kl_V1500 kl_Z))))
                                                           !appl_2 <- appl_1 `pseq` (kl_V1501 `pseq` kl_map appl_1 kl_V1501)
                                                           appl_2 `pseq` applyWrapper kl_V1500 [appl_2]) (do klIf (Atom (B True)) (do kl_V1501 `pseq` applyWrapper kl_V1500 [kl_V1501]) (do return (List [])))

kl_compile :: Types.KLValue ->
              Types.KLValue ->
              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_compile (!kl_V1502) (!kl_V1503) (!kl_V1504) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_O) -> do let !aw_1 = Types.Atom (Types.UnboundSym "fail")
                                                                                                                !appl_2 <- applyWrapper aw_1 []
                                                                                                                !kl_if_3 <- appl_2 `pseq` (kl_O `pseq` eq appl_2 kl_O)
                                                                                                                !kl_if_4 <- klIf kl_if_3 (do return (Atom (B True))) (do !appl_5 <- kl_O `pseq` hd kl_O
                                                                                                                                                                         !appl_6 <- appl_5 `pseq` kl_emptyP appl_5
                                                                                                                                                                         appl_6 `pseq` kl_not appl_6)
                                                                                                                klIf kl_if_4 (do kl_O `pseq` applyWrapper kl_V1504 [kl_O]) (do let !aw_7 = Types.Atom (Types.UnboundSym "shen.hdtl")
                                                                                                                                                                               kl_O `pseq` applyWrapper aw_7 [kl_O]))))
                                                    let !appl_8 = List []
                                                    let !appl_9 = List []
                                                    !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                    !appl_11 <- kl_V1503 `pseq` (appl_10 `pseq` klCons kl_V1503 appl_10)
                                                    !appl_12 <- appl_11 `pseq` applyWrapper kl_V1502 [appl_11]
                                                    appl_12 `pseq` applyWrapper appl_0 [appl_12]

kl_fail_if :: Types.KLValue ->
              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_fail_if (!kl_V1505) (!kl_V1506) = do !kl_if_0 <- kl_V1506 `pseq` applyWrapper kl_V1505 [kl_V1506]
                                        klIf kl_if_0 (do let !aw_1 = Types.Atom (Types.UnboundSym "fail")
                                                         applyWrapper aw_1 []) (do return kl_V1506)

kl_Ats :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_Ats (!kl_V1507) (!kl_V1508) = do kl_V1507 `pseq` (kl_V1508 `pseq` cn kl_V1507 kl_V1508)

kl_tcP :: Types.KLContext Types.Env Types.KLValue
kl_tcP = do value (Types.Atom (Types.UnboundSym "shen.*tc*"))

kl_ps :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_ps (!kl_V1509) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                           kl_V1509 `pseq` (appl_0 `pseq` kl_get kl_V1509 (Types.Atom (Types.UnboundSym "shen.source")) appl_0)) `catchError` (\(!kl_E) -> do let !aw_1 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                              !appl_2 <- kl_V1509 `pseq` applyWrapper aw_1 [kl_V1509,
                                                                                                                                                                                                            Types.Atom (Types.Str " not found.\n"),
                                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                              appl_2 `pseq` simpleError appl_2)

kl_stinput :: Types.KLContext Types.Env Types.KLValue
kl_stinput = do value (Types.Atom (Types.UnboundSym "*stinput*"))

kl_shen_PlusvectorP :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_PlusvectorP (!kl_V1510) = do !kl_if_0 <- kl_V1510 `pseq` absvectorP kl_V1510
                                     klIf kl_if_0 (do !appl_1 <- kl_V1510 `pseq` addressFrom kl_V1510 (Types.Atom (Types.N (Types.KI 0)))
                                                      appl_1 `pseq` greaterThan appl_1 (Types.Atom (Types.N (Types.KI 0)))) (do return (Atom (B False)))

kl_vector :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_vector (!kl_V1511) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Vector) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_ZeroStamp) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Standard) -> do return kl_Standard)))
                                                                                                                                                                !kl_if_3 <- kl_V1511 `pseq` eq kl_V1511 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                !appl_4 <- klIf kl_if_3 (do return kl_ZeroStamp) (do let !aw_5 = Types.Atom (Types.UnboundSym "fail")
                                                                                                                                                                                                                     !appl_6 <- applyWrapper aw_5 []
                                                                                                                                                                                                                     kl_ZeroStamp `pseq` (kl_V1511 `pseq` (appl_6 `pseq` kl_shen_fillvector kl_ZeroStamp (Types.Atom (Types.N (Types.KI 1))) kl_V1511 appl_6)))
                                                                                                                                                                appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                            !appl_7 <- kl_Vector `pseq` (kl_V1511 `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 0))) kl_V1511)
                                                                                            appl_7 `pseq` applyWrapper appl_1 [appl_7])))
                           !appl_8 <- kl_V1511 `pseq` add kl_V1511 (Types.Atom (Types.N (Types.KI 1)))
                           !appl_9 <- appl_8 `pseq` absvector appl_8
                           appl_9 `pseq` applyWrapper appl_0 [appl_9]

kl_shen_fillvector :: Types.KLValue ->
                      Types.KLValue ->
                      Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_fillvector (!kl_V1513) (!kl_V1514) (!kl_V1515) (!kl_V1516) = do !kl_if_0 <- kl_V1515 `pseq` (kl_V1514 `pseq` eq kl_V1515 kl_V1514)
                                                                        klIf kl_if_0 (do kl_V1513 `pseq` (kl_V1515 `pseq` (kl_V1516 `pseq` addressTo kl_V1513 kl_V1515 kl_V1516))) (do klIf (Atom (B True)) (do !appl_1 <- kl_V1513 `pseq` (kl_V1514 `pseq` (kl_V1516 `pseq` addressTo kl_V1513 kl_V1514 kl_V1516))
                                                                                                                                                                                                                !appl_2 <- kl_V1514 `pseq` add (Types.Atom (Types.N (Types.KI 1))) kl_V1514
                                                                                                                                                                                                                appl_1 `pseq` (appl_2 `pseq` (kl_V1515 `pseq` (kl_V1516 `pseq` kl_shen_fillvector appl_1 appl_2 kl_V1515 kl_V1516)))) (do return (List [])))

kl_vectorP :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_vectorP (!kl_V1517) = do !kl_if_0 <- kl_V1517 `pseq` absvectorP kl_V1517
                            klIf kl_if_0 (do (do !appl_1 <- kl_V1517 `pseq` addressFrom kl_V1517 (Types.Atom (Types.N (Types.KI 0)))
                                                 appl_1 `pseq` greaterThanOrEqualTo appl_1 (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Atom (B False)))) (do return (Atom (B False)))

kl_vector_RB :: Types.KLValue ->
                Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_vector_RB (!kl_V1518) (!kl_V1519) (!kl_V1520) = do !kl_if_0 <- kl_V1519 `pseq` eq kl_V1519 (Types.Atom (Types.N (Types.KI 0)))
                                                      klIf kl_if_0 (do simpleError (Types.Atom (Types.Str "cannot access 0th element of a vector\n"))) (do kl_V1518 `pseq` (kl_V1519 `pseq` (kl_V1520 `pseq` addressTo kl_V1518 kl_V1519 kl_V1520)))

kl_LB_vector :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_LB_vector (!kl_V1521) (!kl_V1522) = do !kl_if_0 <- kl_V1522 `pseq` eq kl_V1522 (Types.Atom (Types.N (Types.KI 0)))
                                          klIf kl_if_0 (do simpleError (Types.Atom (Types.Str "cannot access 0th element of a vector\n"))) (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_VectorElement) -> do let !aw_2 = Types.Atom (Types.UnboundSym "fail")
                                                                                                                                                                                                                       !appl_3 <- applyWrapper aw_2 []
                                                                                                                                                                                                                       !kl_if_4 <- kl_VectorElement `pseq` (appl_3 `pseq` eq kl_VectorElement appl_3)
                                                                                                                                                                                                                       klIf kl_if_4 (do simpleError (Types.Atom (Types.Str "vector element not found\n"))) (do return kl_VectorElement))))
                                                                                                                                               !appl_5 <- kl_V1521 `pseq` (kl_V1522 `pseq` addressFrom kl_V1521 kl_V1522)
                                                                                                                                               appl_5 `pseq` applyWrapper appl_1 [appl_5])

kl_shen_posintP :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_posintP (!kl_V1523) = do !kl_if_0 <- kl_V1523 `pseq` kl_integerP kl_V1523
                                 klIf kl_if_0 (do kl_V1523 `pseq` greaterThanOrEqualTo kl_V1523 (Types.Atom (Types.N (Types.KI 0)))) (do return (Atom (B False)))

kl_limit :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_limit (!kl_V1524) = do kl_V1524 `pseq` addressFrom kl_V1524 (Types.Atom (Types.N (Types.KI 0)))

kl_symbolP :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_symbolP (!kl_V1525) = do !kl_if_0 <- kl_V1525 `pseq` kl_booleanP kl_V1525
                            !kl_if_1 <- klIf kl_if_0 (do return (Atom (B True))) (do !kl_if_2 <- kl_V1525 `pseq` numberP kl_V1525
                                                                                     klIf kl_if_2 (do return (Atom (B True))) (do kl_V1525 `pseq` stringP kl_V1525))
                            klIf kl_if_1 (do return (Atom (B False))) (do klIf (Atom (B True)) (do (do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_String) -> do kl_String `pseq` kl_shen_analyse_symbolP kl_String)))
                                                                                                       !appl_4 <- kl_V1525 `pseq` str kl_V1525
                                                                                                       appl_4 `pseq` applyWrapper appl_3 [appl_4]) `catchError` (\(!kl_E) -> do return (Atom (B False)))) (do return (List [])))

kl_shen_analyse_symbolP :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_analyse_symbolP (!kl_V1526) = do !kl_if_0 <- kl_V1526 `pseq` kl_shen_PlusstringP kl_V1526
                                         klIf kl_if_0 (do !appl_1 <- kl_V1526 `pseq` pos kl_V1526 (Types.Atom (Types.N (Types.KI 0)))
                                                          !kl_if_2 <- appl_1 `pseq` kl_shen_alphaP appl_1
                                                          klIf kl_if_2 (do !appl_3 <- kl_V1526 `pseq` tlstr kl_V1526
                                                                           appl_3 `pseq` kl_shen_alphanumsP appl_3) (do return (Atom (B False)))) (do klIf (Atom (B True)) (do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                               applyWrapper aw_4 [ApplC (wrapNamed "shen.analyse-symbol?" kl_shen_analyse_symbolP)]) (do return (List [])))

kl_shen_alphaP :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_alphaP (!kl_V1527) = do let !appl_0 = List []
                                !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.Str ".")) appl_0
                                !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.Str "'")) appl_1
                                !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.Str "#")) appl_2
                                !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str "`")) appl_3
                                !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.Str ";")) appl_4
                                !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.Str ":")) appl_5
                                !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.Str "}")) appl_6
                                !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.Str "{")) appl_7
                                !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.Str "%")) appl_8
                                !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.Str "&")) appl_9
                                !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.Str "<")) appl_10
                                !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.Str ">")) appl_11
                                !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.Str "~")) appl_12
                                !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.Str "@")) appl_13
                                !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.Str "!")) appl_14
                                !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.Str "$")) appl_15
                                !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.Str "?")) appl_16
                                !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.Str "_")) appl_17
                                !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.Str "-")) appl_18
                                !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.Str "+")) appl_19
                                !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.Str "/")) appl_20
                                !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.Str "*")) appl_21
                                !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.Str "=")) appl_22
                                !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.Str "z")) appl_23
                                !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.Str "y")) appl_24
                                !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.Str "x")) appl_25
                                !appl_27 <- appl_26 `pseq` klCons (Types.Atom (Types.Str "w")) appl_26
                                !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.Str "v")) appl_27
                                !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.Str "u")) appl_28
                                !appl_30 <- appl_29 `pseq` klCons (Types.Atom (Types.Str "t")) appl_29
                                !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.Str "s")) appl_30
                                !appl_32 <- appl_31 `pseq` klCons (Types.Atom (Types.Str "r")) appl_31
                                !appl_33 <- appl_32 `pseq` klCons (Types.Atom (Types.Str "q")) appl_32
                                !appl_34 <- appl_33 `pseq` klCons (Types.Atom (Types.Str "p")) appl_33
                                !appl_35 <- appl_34 `pseq` klCons (Types.Atom (Types.Str "o")) appl_34
                                !appl_36 <- appl_35 `pseq` klCons (Types.Atom (Types.Str "n")) appl_35
                                !appl_37 <- appl_36 `pseq` klCons (Types.Atom (Types.Str "m")) appl_36
                                !appl_38 <- appl_37 `pseq` klCons (Types.Atom (Types.Str "l")) appl_37
                                !appl_39 <- appl_38 `pseq` klCons (Types.Atom (Types.Str "k")) appl_38
                                !appl_40 <- appl_39 `pseq` klCons (Types.Atom (Types.Str "j")) appl_39
                                !appl_41 <- appl_40 `pseq` klCons (Types.Atom (Types.Str "i")) appl_40
                                !appl_42 <- appl_41 `pseq` klCons (Types.Atom (Types.Str "h")) appl_41
                                !appl_43 <- appl_42 `pseq` klCons (Types.Atom (Types.Str "g")) appl_42
                                !appl_44 <- appl_43 `pseq` klCons (Types.Atom (Types.Str "f")) appl_43
                                !appl_45 <- appl_44 `pseq` klCons (Types.Atom (Types.Str "e")) appl_44
                                !appl_46 <- appl_45 `pseq` klCons (Types.Atom (Types.Str "d")) appl_45
                                !appl_47 <- appl_46 `pseq` klCons (Types.Atom (Types.Str "c")) appl_46
                                !appl_48 <- appl_47 `pseq` klCons (Types.Atom (Types.Str "b")) appl_47
                                !appl_49 <- appl_48 `pseq` klCons (Types.Atom (Types.Str "a")) appl_48
                                !appl_50 <- appl_49 `pseq` klCons (Types.Atom (Types.Str "Z")) appl_49
                                !appl_51 <- appl_50 `pseq` klCons (Types.Atom (Types.Str "Y")) appl_50
                                !appl_52 <- appl_51 `pseq` klCons (Types.Atom (Types.Str "X")) appl_51
                                !appl_53 <- appl_52 `pseq` klCons (Types.Atom (Types.Str "W")) appl_52
                                !appl_54 <- appl_53 `pseq` klCons (Types.Atom (Types.Str "V")) appl_53
                                !appl_55 <- appl_54 `pseq` klCons (Types.Atom (Types.Str "U")) appl_54
                                !appl_56 <- appl_55 `pseq` klCons (Types.Atom (Types.Str "T")) appl_55
                                !appl_57 <- appl_56 `pseq` klCons (Types.Atom (Types.Str "S")) appl_56
                                !appl_58 <- appl_57 `pseq` klCons (Types.Atom (Types.Str "R")) appl_57
                                !appl_59 <- appl_58 `pseq` klCons (Types.Atom (Types.Str "Q")) appl_58
                                !appl_60 <- appl_59 `pseq` klCons (Types.Atom (Types.Str "P")) appl_59
                                !appl_61 <- appl_60 `pseq` klCons (Types.Atom (Types.Str "O")) appl_60
                                !appl_62 <- appl_61 `pseq` klCons (Types.Atom (Types.Str "N")) appl_61
                                !appl_63 <- appl_62 `pseq` klCons (Types.Atom (Types.Str "M")) appl_62
                                !appl_64 <- appl_63 `pseq` klCons (Types.Atom (Types.Str "L")) appl_63
                                !appl_65 <- appl_64 `pseq` klCons (Types.Atom (Types.Str "K")) appl_64
                                !appl_66 <- appl_65 `pseq` klCons (Types.Atom (Types.Str "J")) appl_65
                                !appl_67 <- appl_66 `pseq` klCons (Types.Atom (Types.Str "I")) appl_66
                                !appl_68 <- appl_67 `pseq` klCons (Types.Atom (Types.Str "H")) appl_67
                                !appl_69 <- appl_68 `pseq` klCons (Types.Atom (Types.Str "G")) appl_68
                                !appl_70 <- appl_69 `pseq` klCons (Types.Atom (Types.Str "F")) appl_69
                                !appl_71 <- appl_70 `pseq` klCons (Types.Atom (Types.Str "E")) appl_70
                                !appl_72 <- appl_71 `pseq` klCons (Types.Atom (Types.Str "D")) appl_71
                                !appl_73 <- appl_72 `pseq` klCons (Types.Atom (Types.Str "C")) appl_72
                                !appl_74 <- appl_73 `pseq` klCons (Types.Atom (Types.Str "B")) appl_73
                                !appl_75 <- appl_74 `pseq` klCons (Types.Atom (Types.Str "A")) appl_74
                                kl_V1527 `pseq` (appl_75 `pseq` kl_elementP kl_V1527 appl_75)

kl_shen_alphanumsP :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_alphanumsP (!kl_V1528) = do !kl_if_0 <- kl_V1528 `pseq` eq (Types.Atom (Types.Str "")) kl_V1528
                                    klIf kl_if_0 (do return (Atom (B True))) (do !kl_if_1 <- kl_V1528 `pseq` kl_shen_PlusstringP kl_V1528
                                                                                 klIf kl_if_1 (do !appl_2 <- kl_V1528 `pseq` pos kl_V1528 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                  !kl_if_3 <- appl_2 `pseq` kl_shen_alphanumP appl_2
                                                                                                  klIf kl_if_3 (do !appl_4 <- kl_V1528 `pseq` tlstr kl_V1528
                                                                                                                   appl_4 `pseq` kl_shen_alphanumsP appl_4) (do return (Atom (B False)))) (do klIf (Atom (B True)) (do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                       applyWrapper aw_5 [ApplC (wrapNamed "shen.alphanums?" kl_shen_alphanumsP)]) (do return (List []))))

kl_shen_alphanumP :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_alphanumP (!kl_V1529) = do !kl_if_0 <- kl_V1529 `pseq` kl_shen_alphaP kl_V1529
                                   klIf kl_if_0 (do return (Atom (B True))) (do kl_V1529 `pseq` kl_shen_digitP kl_V1529)

kl_shen_digitP :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_digitP (!kl_V1530) = do let !appl_0 = List []
                                !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.Str "0")) appl_0
                                !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.Str "9")) appl_1
                                !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.Str "8")) appl_2
                                !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str "7")) appl_3
                                !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.Str "6")) appl_4
                                !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.Str "5")) appl_5
                                !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.Str "4")) appl_6
                                !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.Str "3")) appl_7
                                !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.Str "2")) appl_8
                                !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.Str "1")) appl_9
                                kl_V1530 `pseq` (appl_10 `pseq` kl_elementP kl_V1530 appl_10)

kl_variableP :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_variableP (!kl_V1531) = do !kl_if_0 <- kl_V1531 `pseq` kl_booleanP kl_V1531
                              !kl_if_1 <- klIf kl_if_0 (do return (Atom (B True))) (do !kl_if_2 <- kl_V1531 `pseq` numberP kl_V1531
                                                                                       klIf kl_if_2 (do return (Atom (B True))) (do kl_V1531 `pseq` stringP kl_V1531))
                              klIf kl_if_1 (do return (Atom (B False))) (do klIf (Atom (B True)) (do (do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_String) -> do kl_String `pseq` kl_shen_analyse_variableP kl_String)))
                                                                                                         !appl_4 <- kl_V1531 `pseq` str kl_V1531
                                                                                                         appl_4 `pseq` applyWrapper appl_3 [appl_4]) `catchError` (\(!kl_E) -> do return (Atom (B False)))) (do return (List [])))

kl_shen_analyse_variableP :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_analyse_variableP (!kl_V1532) = do !kl_if_0 <- kl_V1532 `pseq` kl_shen_PlusstringP kl_V1532
                                           klIf kl_if_0 (do !appl_1 <- kl_V1532 `pseq` pos kl_V1532 (Types.Atom (Types.N (Types.KI 0)))
                                                            !kl_if_2 <- appl_1 `pseq` kl_shen_uppercaseP appl_1
                                                            klIf kl_if_2 (do !appl_3 <- kl_V1532 `pseq` tlstr kl_V1532
                                                                             appl_3 `pseq` kl_shen_alphanumsP appl_3) (do return (Atom (B False)))) (do klIf (Atom (B True)) (do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                 applyWrapper aw_4 [ApplC (wrapNamed "shen.analyse-variable?" kl_shen_analyse_variableP)]) (do return (List [])))

kl_shen_uppercaseP :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_uppercaseP (!kl_V1533) = do let !appl_0 = List []
                                    !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.Str "Z")) appl_0
                                    !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.Str "Y")) appl_1
                                    !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.Str "X")) appl_2
                                    !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.Str "W")) appl_3
                                    !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.Str "V")) appl_4
                                    !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.Str "U")) appl_5
                                    !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.Str "T")) appl_6
                                    !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.Str "S")) appl_7
                                    !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.Str "R")) appl_8
                                    !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.Str "Q")) appl_9
                                    !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.Str "P")) appl_10
                                    !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.Str "O")) appl_11
                                    !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.Str "N")) appl_12
                                    !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.Str "M")) appl_13
                                    !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.Str "L")) appl_14
                                    !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.Str "K")) appl_15
                                    !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.Str "J")) appl_16
                                    !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.Str "I")) appl_17
                                    !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.Str "H")) appl_18
                                    !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.Str "G")) appl_19
                                    !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.Str "F")) appl_20
                                    !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.Str "E")) appl_21
                                    !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.Str "D")) appl_22
                                    !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.Str "C")) appl_23
                                    !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.Str "B")) appl_24
                                    !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.Str "A")) appl_25
                                    kl_V1533 `pseq` (appl_26 `pseq` kl_elementP kl_V1533 appl_26)

kl_gensym :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_gensym (!kl_V1534) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*gensym*"))
                           !appl_1 <- appl_0 `pseq` add (Types.Atom (Types.N (Types.KI 1))) appl_0
                           !appl_2 <- appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*gensym*")) appl_1
                           kl_V1534 `pseq` (appl_2 `pseq` kl_concat kl_V1534 appl_2)

kl_concat :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_concat (!kl_V1535) (!kl_V1536) = do !appl_0 <- kl_V1535 `pseq` str kl_V1535
                                       !appl_1 <- kl_V1536 `pseq` str kl_V1536
                                       !appl_2 <- appl_0 `pseq` (appl_1 `pseq` cn appl_0 appl_1)
                                       appl_2 `pseq` intern appl_2

kl_Atp :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_Atp (!kl_V1537) (!kl_V1538) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Vector) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Tag) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Fst) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Snd) -> do return kl_Vector)))
                                                                                                                                                                                                                                 !appl_4 <- kl_Vector `pseq` (kl_V1538 `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 2))) kl_V1538)
                                                                                                                                                                                                                                 appl_4 `pseq` applyWrapper appl_3 [appl_4])))
                                                                                                                                                                   !appl_5 <- kl_Vector `pseq` (kl_V1537 `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 1))) kl_V1537)
                                                                                                                                                                   appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                                     !appl_6 <- kl_Vector `pseq` addressTo kl_Vector (Types.Atom (Types.N (Types.KI 0))) (Types.Atom (Types.UnboundSym "shen.tuple"))
                                                                                                     appl_6 `pseq` applyWrapper appl_1 [appl_6])))
                                    !appl_7 <- absvector (Types.Atom (Types.N (Types.KI 3)))
                                    appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_fst :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_fst (!kl_V1539) = do kl_V1539 `pseq` addressFrom kl_V1539 (Types.Atom (Types.N (Types.KI 1)))

kl_snd :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_snd (!kl_V1540) = do kl_V1540 `pseq` addressFrom kl_V1540 (Types.Atom (Types.N (Types.KI 2)))

kl_tupleP :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_tupleP (!kl_V1541) = do (do !kl_if_0 <- kl_V1541 `pseq` absvectorP kl_V1541
                               klIf kl_if_0 (do !appl_1 <- kl_V1541 `pseq` addressFrom kl_V1541 (Types.Atom (Types.N (Types.KI 0)))
                                                appl_1 `pseq` eq (Types.Atom (Types.UnboundSym "shen.tuple")) appl_1) (do return (Atom (B False)))) `catchError` (\(!kl_E) -> do return (Atom (B False)))

kl_append :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_append (!kl_V1542) (!kl_V1543) = do let !appl_0 = List []
                                       !kl_if_1 <- appl_0 `pseq` (kl_V1542 `pseq` eq appl_0 kl_V1542)
                                       klIf kl_if_1 (do return kl_V1543) (do !kl_if_2 <- kl_V1542 `pseq` consP kl_V1542
                                                                             klIf kl_if_2 (do !appl_3 <- kl_V1542 `pseq` hd kl_V1542
                                                                                              !appl_4 <- kl_V1542 `pseq` tl kl_V1542
                                                                                              !appl_5 <- appl_4 `pseq` (kl_V1543 `pseq` kl_append appl_4 kl_V1543)
                                                                                              appl_3 `pseq` (appl_5 `pseq` klCons appl_3 appl_5)) (do klIf (Atom (B True)) (do let !aw_6 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                               applyWrapper aw_6 [ApplC (wrapNamed "append" kl_append)]) (do return (List []))))

kl_Atv :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_Atv (!kl_V1544) (!kl_V1545) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_NewVector) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_XPlusNewVector) -> do !kl_if_3 <- kl_Limit `pseq` eq kl_Limit (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                                                                                 klIf kl_if_3 (do return kl_XPlusNewVector) (do kl_V1545 `pseq` (kl_Limit `pseq` (kl_XPlusNewVector `pseq` kl_shen_Atv_help kl_V1545 (Types.Atom (Types.N (Types.KI 1))) kl_Limit kl_XPlusNewVector))))))
                                                                                                                                                                        !appl_4 <- kl_NewVector `pseq` (kl_V1544 `pseq` kl_vector_RB kl_NewVector (Types.Atom (Types.N (Types.KI 1))) kl_V1544)
                                                                                                                                                                        appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                    !appl_5 <- kl_Limit `pseq` add kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                    !appl_6 <- appl_5 `pseq` kl_vector appl_5
                                                                                                    appl_6 `pseq` applyWrapper appl_1 [appl_6])))
                                    !appl_7 <- kl_V1545 `pseq` kl_limit kl_V1545
                                    appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_shen_Atv_help :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_Atv_help (!kl_V1547) (!kl_V1548) (!kl_V1549) (!kl_V1550) = do !kl_if_0 <- kl_V1549 `pseq` (kl_V1548 `pseq` eq kl_V1549 kl_V1548)
                                                                      klIf kl_if_0 (do !appl_1 <- kl_V1549 `pseq` add kl_V1549 (Types.Atom (Types.N (Types.KI 1)))
                                                                                       kl_V1547 `pseq` (kl_V1550 `pseq` (kl_V1549 `pseq` (appl_1 `pseq` kl_shen_copyfromvector kl_V1547 kl_V1550 kl_V1549 appl_1)))) (do klIf (Atom (B True)) (do !appl_2 <- kl_V1548 `pseq` add kl_V1548 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                  !appl_3 <- kl_V1548 `pseq` add kl_V1548 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                  !appl_4 <- kl_V1547 `pseq` (kl_V1550 `pseq` (kl_V1548 `pseq` (appl_3 `pseq` kl_shen_copyfromvector kl_V1547 kl_V1550 kl_V1548 appl_3)))
                                                                                                                                                                                                                                                  kl_V1547 `pseq` (appl_2 `pseq` (kl_V1549 `pseq` (appl_4 `pseq` kl_shen_Atv_help kl_V1547 appl_2 kl_V1549 appl_4)))) (do return (List [])))

kl_shen_copyfromvector :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_copyfromvector (!kl_V1551) (!kl_V1552) (!kl_V1553) (!kl_V1554) = do (do !appl_0 <- kl_V1551 `pseq` (kl_V1553 `pseq` kl_LB_vector kl_V1551 kl_V1553)
                                                                                kl_V1552 `pseq` (kl_V1554 `pseq` (appl_0 `pseq` kl_vector_RB kl_V1552 kl_V1554 appl_0))) `catchError` (\(!kl_E) -> do return kl_V1552)

kl_hdv :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_hdv (!kl_V1555) = do (do kl_V1555 `pseq` kl_LB_vector kl_V1555 (Types.Atom (Types.N (Types.KI 1)))) `catchError` (\(!kl_E) -> do let !aw_0 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                    !appl_1 <- kl_V1555 `pseq` applyWrapper aw_0 [kl_V1555,
                                                                                                                                                                                  Types.Atom (Types.Str "\n"),
                                                                                                                                                                                  Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                    !appl_2 <- appl_1 `pseq` cn (Types.Atom (Types.Str "hdv needs a non-empty vector as an argument; not ")) appl_1
                                                                                                                                    appl_2 `pseq` simpleError appl_2)

kl_tlv :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_tlv (!kl_V1556) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Limit) -> do !kl_if_1 <- kl_Limit `pseq` eq kl_Limit (Types.Atom (Types.N (Types.KI 0)))
                                                                                        klIf kl_if_1 (do simpleError (Types.Atom (Types.Str "cannot take the tail of the empty vector\n"))) (do !kl_if_2 <- kl_Limit `pseq` eq kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                klIf kl_if_2 (do kl_vector (Types.Atom (Types.N (Types.KI 0)))) (do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_NewVector) -> do !appl_4 <- kl_Limit `pseq` Primitives.subtract kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                                                                                        !appl_5 <- appl_4 `pseq` kl_vector appl_4
                                                                                                                                                                                                                                                                                                                                        kl_V1556 `pseq` (kl_Limit `pseq` (appl_5 `pseq` kl_shen_tlv_help kl_V1556 (Types.Atom (Types.N (Types.KI 2))) kl_Limit appl_5)))))
                                                                                                                                                                                                                                                                    !appl_6 <- kl_Limit `pseq` Primitives.subtract kl_Limit (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                    !appl_7 <- appl_6 `pseq` kl_vector appl_6
                                                                                                                                                                                                                                                                    appl_7 `pseq` applyWrapper appl_3 [appl_7])))))
                        !appl_8 <- kl_V1556 `pseq` kl_limit kl_V1556
                        appl_8 `pseq` applyWrapper appl_0 [appl_8]

kl_shen_tlv_help :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_tlv_help (!kl_V1558) (!kl_V1559) (!kl_V1560) (!kl_V1561) = do !kl_if_0 <- kl_V1560 `pseq` (kl_V1559 `pseq` eq kl_V1560 kl_V1559)
                                                                      klIf kl_if_0 (do !appl_1 <- kl_V1560 `pseq` Primitives.subtract kl_V1560 (Types.Atom (Types.N (Types.KI 1)))
                                                                                       kl_V1558 `pseq` (kl_V1561 `pseq` (kl_V1560 `pseq` (appl_1 `pseq` kl_shen_copyfromvector kl_V1558 kl_V1561 kl_V1560 appl_1)))) (do klIf (Atom (B True)) (do !appl_2 <- kl_V1559 `pseq` add kl_V1559 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                  !appl_3 <- kl_V1559 `pseq` Primitives.subtract kl_V1559 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                  !appl_4 <- kl_V1558 `pseq` (kl_V1561 `pseq` (kl_V1559 `pseq` (appl_3 `pseq` kl_shen_copyfromvector kl_V1558 kl_V1561 kl_V1559 appl_3)))
                                                                                                                                                                                                                                                  kl_V1558 `pseq` (appl_2 `pseq` (kl_V1560 `pseq` (appl_4 `pseq` kl_shen_tlv_help kl_V1558 appl_2 kl_V1560 appl_4)))) (do return (List [])))

kl_assoc :: Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_assoc (!kl_V1571) (!kl_V1572) = do let !appl_0 = List []
                                      !kl_if_1 <- appl_0 `pseq` (kl_V1572 `pseq` eq appl_0 kl_V1572)
                                      klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V1572 `pseq` consP kl_V1572
                                                                             !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V1572 `pseq` hd kl_V1572
                                                                                                          !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                          klIf kl_if_5 (do !appl_6 <- kl_V1572 `pseq` hd kl_V1572
                                                                                                                           !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                           appl_7 `pseq` (kl_V1571 `pseq` eq appl_7 kl_V1571)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                             klIf kl_if_3 (do kl_V1572 `pseq` hd kl_V1572) (do !kl_if_8 <- kl_V1572 `pseq` consP kl_V1572
                                                                                                                               klIf kl_if_8 (do !appl_9 <- kl_V1572 `pseq` tl kl_V1572
                                                                                                                                                kl_V1571 `pseq` (appl_9 `pseq` kl_assoc kl_V1571 appl_9)) (do klIf (Atom (B True)) (do let !aw_10 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                       applyWrapper aw_10 [ApplC (wrapNamed "assoc" kl_assoc)]) (do return (List [])))))

kl_booleanP :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_booleanP (!kl_V1577) = do !kl_if_0 <- kl_V1577 `pseq` eq (Atom (B True)) kl_V1577
                             klIf kl_if_0 (do return (Atom (B True))) (do !kl_if_1 <- kl_V1577 `pseq` eq (Atom (B False)) kl_V1577
                                                                          klIf kl_if_1 (do return (Atom (B True))) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List []))))

kl_nl :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_nl (!kl_V1578) = do !kl_if_0 <- kl_V1578 `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_V1578
                       klIf kl_if_0 (do return (Types.Atom (Types.N (Types.KI 0)))) (do klIf (Atom (B True)) (do !appl_1 <- kl_stoutput
                                                                                                                 let !aw_2 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                 !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [Types.Atom (Types.Str "\n"),
                                                                                                                                                             appl_1]
                                                                                                                 !appl_4 <- kl_V1578 `pseq` Primitives.subtract kl_V1578 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                 !appl_5 <- appl_4 `pseq` kl_nl appl_4
                                                                                                                 appl_3 `pseq` (appl_5 `pseq` kl_do appl_3 appl_5)) (do return (List [])))

kl_difference :: Types.KLValue ->
                 Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_difference (!kl_V1581) (!kl_V1582) = do let !appl_0 = List []
                                           !kl_if_1 <- appl_0 `pseq` (kl_V1581 `pseq` eq appl_0 kl_V1581)
                                           klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V1581 `pseq` consP kl_V1581
                                                                                  klIf kl_if_2 (do !appl_3 <- kl_V1581 `pseq` hd kl_V1581
                                                                                                   !kl_if_4 <- appl_3 `pseq` (kl_V1582 `pseq` kl_elementP appl_3 kl_V1582)
                                                                                                   klIf kl_if_4 (do !appl_5 <- kl_V1581 `pseq` tl kl_V1581
                                                                                                                    appl_5 `pseq` (kl_V1582 `pseq` kl_difference appl_5 kl_V1582)) (do !appl_6 <- kl_V1581 `pseq` hd kl_V1581
                                                                                                                                                                                       !appl_7 <- kl_V1581 `pseq` tl kl_V1581
                                                                                                                                                                                       !appl_8 <- appl_7 `pseq` (kl_V1582 `pseq` kl_difference appl_7 kl_V1582)
                                                                                                                                                                                       appl_6 `pseq` (appl_8 `pseq` klCons appl_6 appl_8))) (do klIf (Atom (B True)) (do let !aw_9 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                         applyWrapper aw_9 [ApplC (wrapNamed "difference" kl_difference)]) (do return (List []))))

kl_do :: Types.KLValue ->
         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_do (!kl_V1583) (!kl_V1584) = do return kl_V1584

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

kl_emptyP :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_emptyP (!kl_V1600) = do let !appl_0 = List []
                           !kl_if_1 <- appl_0 `pseq` (kl_V1600 `pseq` eq appl_0 kl_V1600)
                           klIf kl_if_1 (do return (Atom (B True))) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List [])))

kl_fix :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_fix (!kl_V1601) (!kl_V1602) = do !appl_0 <- kl_V1602 `pseq` applyWrapper kl_V1601 [kl_V1602]
                                    kl_V1601 `pseq` (kl_V1602 `pseq` (appl_0 `pseq` kl_shen_fix_help kl_V1601 kl_V1602 appl_0))

kl_shen_fix_help :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_fix_help (!kl_V1610) (!kl_V1611) (!kl_V1612) = do !kl_if_0 <- kl_V1612 `pseq` (kl_V1611 `pseq` eq kl_V1612 kl_V1611)
                                                          klIf kl_if_0 (do return kl_V1612) (do klIf (Atom (B True)) (do !appl_1 <- kl_V1612 `pseq` applyWrapper kl_V1610 [kl_V1612]
                                                                                                                         kl_V1610 `pseq` (kl_V1612 `pseq` (appl_1 `pseq` kl_shen_fix_help kl_V1610 kl_V1612 appl_1))) (do return (List [])))

kl_put :: Types.KLValue ->
          Types.KLValue ->
          Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_put (!kl_V1613) (!kl_V1614) (!kl_V1615) (!kl_V1616) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Change) -> do return kl_V1615)))
                                                                                                                                                                                        !appl_3 <- kl_V1613 `pseq` (kl_V1614 `pseq` (kl_V1615 `pseq` (kl_Entry `pseq` kl_shen_change_pointer_value kl_V1613 kl_V1614 kl_V1615 kl_Entry)))
                                                                                                                                                                                        !appl_4 <- kl_V1616 `pseq` (kl_N `pseq` (appl_3 `pseq` kl_vector_RB kl_V1616 kl_N appl_3))
                                                                                                                                                                                        appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                                        !appl_5 <- (do kl_V1616 `pseq` (kl_N `pseq` kl_LB_vector kl_V1616 kl_N)) `catchError` (\(!kl_E) -> do return (List []))
                                                                                                                        appl_5 `pseq` applyWrapper appl_1 [appl_5])))
                                                            !appl_6 <- kl_V1616 `pseq` kl_limit kl_V1616
                                                            !appl_7 <- kl_V1613 `pseq` (appl_6 `pseq` kl_hash kl_V1613 appl_6)
                                                            appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_unput :: Types.KLValue ->
            Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_unput (!kl_V1617) (!kl_V1618) (!kl_V1619) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Change) -> do return kl_V1617)))
                                                                                                                                                                              !appl_3 <- kl_V1617 `pseq` (kl_V1618 `pseq` (kl_Entry `pseq` kl_shen_remove_pointer kl_V1617 kl_V1618 kl_Entry))
                                                                                                                                                                              !appl_4 <- kl_V1619 `pseq` (kl_N `pseq` (appl_3 `pseq` kl_vector_RB kl_V1619 kl_N appl_3))
                                                                                                                                                                              appl_4 `pseq` applyWrapper appl_2 [appl_4])))
                                                                                                              !appl_5 <- (do kl_V1619 `pseq` (kl_N `pseq` kl_LB_vector kl_V1619 kl_N)) `catchError` (\(!kl_E) -> do return (List []))
                                                                                                              appl_5 `pseq` applyWrapper appl_1 [appl_5])))
                                                  !appl_6 <- kl_V1619 `pseq` kl_limit kl_V1619
                                                  !appl_7 <- kl_V1617 `pseq` (appl_6 `pseq` kl_hash kl_V1617 appl_6)
                                                  appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_shen_remove_pointer :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_remove_pointer (!kl_V1624) (!kl_V1625) (!kl_V1626) = do let !appl_0 = List []
                                                                !kl_if_1 <- appl_0 `pseq` (kl_V1626 `pseq` eq appl_0 kl_V1626)
                                                                klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V1626 `pseq` consP kl_V1626
                                                                                                       !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                    !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                                                    klIf kl_if_5 (do !appl_6 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                                     !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                                                     !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                                                                     klIf kl_if_8 (do !appl_9 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                                                      !appl_10 <- appl_9 `pseq` hd appl_9
                                                                                                                                                                      !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                                                                      !kl_if_12 <- appl_11 `pseq` consP appl_11
                                                                                                                                                                      klIf kl_if_12 (do let !appl_13 = List []
                                                                                                                                                                                        !appl_14 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                                                                        !appl_15 <- appl_14 `pseq` hd appl_14
                                                                                                                                                                                        !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                                                                        !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                                                                                                                        !kl_if_18 <- appl_13 `pseq` (appl_17 `pseq` eq appl_13 appl_17)
                                                                                                                                                                                        klIf kl_if_18 (do !appl_19 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                                                                                          !appl_20 <- appl_19 `pseq` hd appl_19
                                                                                                                                                                                                          !appl_21 <- appl_20 `pseq` tl appl_20
                                                                                                                                                                                                          !appl_22 <- appl_21 `pseq` hd appl_21
                                                                                                                                                                                                          !kl_if_23 <- appl_22 `pseq` (kl_V1625 `pseq` eq appl_22 kl_V1625)
                                                                                                                                                                                                          klIf kl_if_23 (do !appl_24 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                                                                                                            !appl_25 <- appl_24 `pseq` hd appl_24
                                                                                                                                                                                                                            !appl_26 <- appl_25 `pseq` hd appl_25
                                                                                                                                                                                                                            appl_26 `pseq` (kl_V1624 `pseq` eq appl_26 kl_V1624)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                       klIf kl_if_3 (do kl_V1626 `pseq` tl kl_V1626) (do !kl_if_27 <- kl_V1626 `pseq` consP kl_V1626
                                                                                                                                                         klIf kl_if_27 (do !appl_28 <- kl_V1626 `pseq` hd kl_V1626
                                                                                                                                                                           !appl_29 <- kl_V1626 `pseq` tl kl_V1626
                                                                                                                                                                           !appl_30 <- kl_V1624 `pseq` (kl_V1625 `pseq` (appl_29 `pseq` kl_shen_remove_pointer kl_V1624 kl_V1625 appl_29))
                                                                                                                                                                           appl_28 `pseq` (appl_30 `pseq` klCons appl_28 appl_30)) (do klIf (Atom (B True)) (do let !aw_31 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                applyWrapper aw_31 [ApplC (wrapNamed "shen.remove-pointer" kl_shen_remove_pointer)]) (do return (List [])))))

kl_shen_change_pointer_value :: Types.KLValue ->
                                Types.KLValue ->
                                Types.KLValue ->
                                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_change_pointer_value (!kl_V1631) (!kl_V1632) (!kl_V1633) (!kl_V1634) = do let !appl_0 = List []
                                                                                  !kl_if_1 <- appl_0 `pseq` (kl_V1634 `pseq` eq appl_0 kl_V1634)
                                                                                  klIf kl_if_1 (do let !appl_2 = List []
                                                                                                   !appl_3 <- kl_V1632 `pseq` (appl_2 `pseq` klCons kl_V1632 appl_2)
                                                                                                   !appl_4 <- kl_V1631 `pseq` (appl_3 `pseq` klCons kl_V1631 appl_3)
                                                                                                   !appl_5 <- appl_4 `pseq` (kl_V1633 `pseq` klCons appl_4 kl_V1633)
                                                                                                   let !appl_6 = List []
                                                                                                   appl_5 `pseq` (appl_6 `pseq` klCons appl_5 appl_6)) (do !kl_if_7 <- kl_V1634 `pseq` consP kl_V1634
                                                                                                                                                           !kl_if_8 <- klIf kl_if_7 (do !appl_9 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                        !kl_if_10 <- appl_9 `pseq` consP appl_9
                                                                                                                                                                                        klIf kl_if_10 (do !appl_11 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                                          !appl_12 <- appl_11 `pseq` hd appl_11
                                                                                                                                                                                                          !kl_if_13 <- appl_12 `pseq` consP appl_12
                                                                                                                                                                                                          klIf kl_if_13 (do !appl_14 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                                                            !appl_15 <- appl_14 `pseq` hd appl_14
                                                                                                                                                                                                                            !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                                                                                                            !kl_if_17 <- appl_16 `pseq` consP appl_16
                                                                                                                                                                                                                            klIf kl_if_17 (do let !appl_18 = List []
                                                                                                                                                                                                                                              !appl_19 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                                                                              !appl_20 <- appl_19 `pseq` hd appl_19
                                                                                                                                                                                                                                              !appl_21 <- appl_20 `pseq` tl appl_20
                                                                                                                                                                                                                                              !appl_22 <- appl_21 `pseq` tl appl_21
                                                                                                                                                                                                                                              !kl_if_23 <- appl_18 `pseq` (appl_22 `pseq` eq appl_18 appl_22)
                                                                                                                                                                                                                                              klIf kl_if_23 (do !appl_24 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                                                                                                !appl_25 <- appl_24 `pseq` hd appl_24
                                                                                                                                                                                                                                                                !appl_26 <- appl_25 `pseq` tl appl_25
                                                                                                                                                                                                                                                                !appl_27 <- appl_26 `pseq` hd appl_26
                                                                                                                                                                                                                                                                !kl_if_28 <- appl_27 `pseq` (kl_V1632 `pseq` eq appl_27 kl_V1632)
                                                                                                                                                                                                                                                                klIf kl_if_28 (do !appl_29 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                                                                                                                  !appl_30 <- appl_29 `pseq` hd appl_29
                                                                                                                                                                                                                                                                                  !appl_31 <- appl_30 `pseq` hd appl_30
                                                                                                                                                                                                                                                                                  appl_31 `pseq` (kl_V1631 `pseq` eq appl_31 kl_V1631)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                           klIf kl_if_8 (do !appl_32 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                            !appl_33 <- appl_32 `pseq` hd appl_32
                                                                                                                                                                            !appl_34 <- appl_33 `pseq` (kl_V1633 `pseq` klCons appl_33 kl_V1633)
                                                                                                                                                                            !appl_35 <- kl_V1634 `pseq` tl kl_V1634
                                                                                                                                                                            appl_34 `pseq` (appl_35 `pseq` klCons appl_34 appl_35)) (do !kl_if_36 <- kl_V1634 `pseq` consP kl_V1634
                                                                                                                                                                                                                                        klIf kl_if_36 (do !appl_37 <- kl_V1634 `pseq` hd kl_V1634
                                                                                                                                                                                                                                                          !appl_38 <- kl_V1634 `pseq` tl kl_V1634
                                                                                                                                                                                                                                                          !appl_39 <- kl_V1631 `pseq` (kl_V1632 `pseq` (kl_V1633 `pseq` (appl_38 `pseq` kl_shen_change_pointer_value kl_V1631 kl_V1632 kl_V1633 appl_38)))
                                                                                                                                                                                                                                                          appl_37 `pseq` (appl_39 `pseq` klCons appl_37 appl_39)) (do klIf (Atom (B True)) (do let !aw_40 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                               applyWrapper aw_40 [ApplC (wrapNamed "shen.change-pointer-value" kl_shen_change_pointer_value)]) (do return (List [])))))

kl_get :: Types.KLValue ->
          Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_get (!kl_V1635) (!kl_V1636) (!kl_V1637) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_N) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Entry) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Result) -> do !kl_if_3 <- kl_Result `pseq` kl_emptyP kl_Result
                                                                                                                                                                                                                                             klIf kl_if_3 (do simpleError (Types.Atom (Types.Str "value not found\n"))) (do kl_Result `pseq` tl kl_Result))))
                                                                                                                                                                            let !appl_4 = List []
                                                                                                                                                                            !appl_5 <- kl_V1636 `pseq` (appl_4 `pseq` klCons kl_V1636 appl_4)
                                                                                                                                                                            !appl_6 <- kl_V1635 `pseq` (appl_5 `pseq` klCons kl_V1635 appl_5)
                                                                                                                                                                            !appl_7 <- appl_6 `pseq` (kl_Entry `pseq` kl_assoc appl_6 kl_Entry)
                                                                                                                                                                            appl_7 `pseq` applyWrapper appl_2 [appl_7])))
                                                                                                            !appl_8 <- (do kl_V1637 `pseq` (kl_N `pseq` kl_LB_vector kl_V1637 kl_N)) `catchError` (\(!kl_E) -> do simpleError (Types.Atom (Types.Str "pointer not found\n")))
                                                                                                            appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                                                !appl_9 <- kl_V1637 `pseq` kl_limit kl_V1637
                                                !appl_10 <- kl_V1635 `pseq` (appl_9 `pseq` kl_hash kl_V1635 appl_9)
                                                appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_hash :: Types.KLValue ->
           Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_hash (!kl_V1638) (!kl_V1639) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Hash) -> do !kl_if_1 <- kl_Hash `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_Hash
                                                                                                    klIf kl_if_1 (do return (Types.Atom (Types.N (Types.KI 1)))) (do return kl_Hash))))
                                     let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_V1482) -> do kl_V1482 `pseq` stringToN kl_V1482)))
                                     !appl_3 <- kl_V1638 `pseq` kl_explode kl_V1638
                                     !appl_4 <- appl_2 `pseq` (appl_3 `pseq` kl_map appl_2 appl_3)
                                     !appl_5 <- appl_4 `pseq` kl_sum appl_4
                                     !appl_6 <- appl_5 `pseq` (kl_V1639 `pseq` kl_shen_mod appl_5 kl_V1639)
                                     appl_6 `pseq` applyWrapper appl_0 [appl_6]

kl_shen_mod :: Types.KLValue ->
               Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mod (!kl_V1640) (!kl_V1641) = do let !appl_0 = List []
                                         !appl_1 <- kl_V1641 `pseq` (appl_0 `pseq` klCons kl_V1641 appl_0)
                                         !appl_2 <- kl_V1640 `pseq` (appl_1 `pseq` kl_shen_multiples kl_V1640 appl_1)
                                         kl_V1640 `pseq` (appl_2 `pseq` kl_shen_modh kl_V1640 appl_2)

kl_shen_multiples :: Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_multiples (!kl_V1642) (!kl_V1643) = do !kl_if_0 <- kl_V1643 `pseq` consP kl_V1643
                                               !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V1643 `pseq` hd kl_V1643
                                                                            appl_2 `pseq` (kl_V1642 `pseq` greaterThan appl_2 kl_V1642)) (do return (Atom (B False)))
                                               klIf kl_if_1 (do kl_V1643 `pseq` tl kl_V1643) (do !kl_if_3 <- kl_V1643 `pseq` consP kl_V1643
                                                                                                 klIf kl_if_3 (do !appl_4 <- kl_V1643 `pseq` hd kl_V1643
                                                                                                                  !appl_5 <- appl_4 `pseq` multiply (Types.Atom (Types.N (Types.KI 2))) appl_4
                                                                                                                  !appl_6 <- appl_5 `pseq` (kl_V1643 `pseq` klCons appl_5 kl_V1643)
                                                                                                                  kl_V1642 `pseq` (appl_6 `pseq` kl_shen_multiples kl_V1642 appl_6)) (do klIf (Atom (B True)) (do let !aw_7 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                  applyWrapper aw_7 [ApplC (wrapNamed "shen.multiples" kl_shen_multiples)]) (do return (List []))))

kl_shen_modh :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_modh (!kl_V1646) (!kl_V1647) = do !kl_if_0 <- kl_V1646 `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_V1646
                                          klIf kl_if_0 (do return (Types.Atom (Types.N (Types.KI 0)))) (do let !appl_1 = List []
                                                                                                           !kl_if_2 <- appl_1 `pseq` (kl_V1647 `pseq` eq appl_1 kl_V1647)
                                                                                                           klIf kl_if_2 (do return kl_V1646) (do !kl_if_3 <- kl_V1647 `pseq` consP kl_V1647
                                                                                                                                                 !kl_if_4 <- klIf kl_if_3 (do !appl_5 <- kl_V1647 `pseq` hd kl_V1647
                                                                                                                                                                              appl_5 `pseq` (kl_V1646 `pseq` greaterThan appl_5 kl_V1646)) (do return (Atom (B False)))
                                                                                                                                                 klIf kl_if_4 (do !appl_6 <- kl_V1647 `pseq` tl kl_V1647
                                                                                                                                                                  !kl_if_7 <- appl_6 `pseq` kl_emptyP appl_6
                                                                                                                                                                  klIf kl_if_7 (do return kl_V1646) (do !appl_8 <- kl_V1647 `pseq` tl kl_V1647
                                                                                                                                                                                                        kl_V1646 `pseq` (appl_8 `pseq` kl_shen_modh kl_V1646 appl_8))) (do !kl_if_9 <- kl_V1647 `pseq` consP kl_V1647
                                                                                                                                                                                                                                                                           klIf kl_if_9 (do !appl_10 <- kl_V1647 `pseq` hd kl_V1647
                                                                                                                                                                                                                                                                                            !appl_11 <- kl_V1646 `pseq` (appl_10 `pseq` Primitives.subtract kl_V1646 appl_10)
                                                                                                                                                                                                                                                                                            appl_11 `pseq` (kl_V1647 `pseq` kl_shen_modh appl_11 kl_V1647)) (do klIf (Atom (B True)) (do let !aw_12 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                                                                         applyWrapper aw_12 [ApplC (wrapNamed "shen.modh" kl_shen_modh)]) (do return (List []))))))

kl_sum :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_sum (!kl_V1648) = do let !appl_0 = List []
                        !kl_if_1 <- appl_0 `pseq` (kl_V1648 `pseq` eq appl_0 kl_V1648)
                        klIf kl_if_1 (do return (Types.Atom (Types.N (Types.KI 0)))) (do !kl_if_2 <- kl_V1648 `pseq` consP kl_V1648
                                                                                         klIf kl_if_2 (do !appl_3 <- kl_V1648 `pseq` hd kl_V1648
                                                                                                          !appl_4 <- kl_V1648 `pseq` tl kl_V1648
                                                                                                          !appl_5 <- appl_4 `pseq` kl_sum appl_4
                                                                                                          appl_3 `pseq` (appl_5 `pseq` add appl_3 appl_5)) (do klIf (Atom (B True)) (do let !aw_6 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                        applyWrapper aw_6 [ApplC (wrapNamed "sum" kl_sum)]) (do return (List []))))

kl_head :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_head (!kl_V1655) = do !kl_if_0 <- kl_V1655 `pseq` consP kl_V1655
                         klIf kl_if_0 (do kl_V1655 `pseq` hd kl_V1655) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "head expects a non-empty list"))) (do return (List [])))

kl_tail :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_tail (!kl_V1662) = do !kl_if_0 <- kl_V1662 `pseq` consP kl_V1662
                         klIf kl_if_0 (do kl_V1662 `pseq` tl kl_V1662) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "tail expects a non-empty list"))) (do return (List [])))

kl_hdstr :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_hdstr (!kl_V1663) = do kl_V1663 `pseq` pos kl_V1663 (Types.Atom (Types.N (Types.KI 0)))

kl_intersection :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_intersection (!kl_V1666) (!kl_V1667) = do let !appl_0 = List []
                                             !kl_if_1 <- appl_0 `pseq` (kl_V1666 `pseq` eq appl_0 kl_V1666)
                                             klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V1666 `pseq` consP kl_V1666
                                                                                    klIf kl_if_2 (do !appl_3 <- kl_V1666 `pseq` hd kl_V1666
                                                                                                     !kl_if_4 <- appl_3 `pseq` (kl_V1667 `pseq` kl_elementP appl_3 kl_V1667)
                                                                                                     klIf kl_if_4 (do !appl_5 <- kl_V1666 `pseq` hd kl_V1666
                                                                                                                      !appl_6 <- kl_V1666 `pseq` tl kl_V1666
                                                                                                                      !appl_7 <- appl_6 `pseq` (kl_V1667 `pseq` kl_intersection appl_6 kl_V1667)
                                                                                                                      appl_5 `pseq` (appl_7 `pseq` klCons appl_5 appl_7)) (do !appl_8 <- kl_V1666 `pseq` tl kl_V1666
                                                                                                                                                                              appl_8 `pseq` (kl_V1667 `pseq` kl_intersection appl_8 kl_V1667))) (do klIf (Atom (B True)) (do let !aw_9 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                             applyWrapper aw_9 [ApplC (wrapNamed "intersection" kl_intersection)]) (do return (List []))))

kl_reverse :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_reverse (!kl_V1668) = do let !appl_0 = List []
                            kl_V1668 `pseq` (appl_0 `pseq` kl_shen_reverse_help kl_V1668 appl_0)

kl_shen_reverse_help :: Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_reverse_help (!kl_V1669) (!kl_V1670) = do let !appl_0 = List []
                                                  !kl_if_1 <- appl_0 `pseq` (kl_V1669 `pseq` eq appl_0 kl_V1669)
                                                  klIf kl_if_1 (do return kl_V1670) (do !kl_if_2 <- kl_V1669 `pseq` consP kl_V1669
                                                                                        klIf kl_if_2 (do !appl_3 <- kl_V1669 `pseq` tl kl_V1669
                                                                                                         !appl_4 <- kl_V1669 `pseq` hd kl_V1669
                                                                                                         !appl_5 <- appl_4 `pseq` (kl_V1670 `pseq` klCons appl_4 kl_V1670)
                                                                                                         appl_3 `pseq` (appl_5 `pseq` kl_shen_reverse_help appl_3 appl_5)) (do klIf (Atom (B True)) (do let !aw_6 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                        applyWrapper aw_6 [ApplC (wrapNamed "shen.reverse_help" kl_shen_reverse_help)]) (do return (List []))))

kl_union :: Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_union (!kl_V1671) (!kl_V1672) = do let !appl_0 = List []
                                      !kl_if_1 <- appl_0 `pseq` (kl_V1671 `pseq` eq appl_0 kl_V1671)
                                      klIf kl_if_1 (do return kl_V1672) (do !kl_if_2 <- kl_V1671 `pseq` consP kl_V1671
                                                                            klIf kl_if_2 (do !appl_3 <- kl_V1671 `pseq` hd kl_V1671
                                                                                             !kl_if_4 <- appl_3 `pseq` (kl_V1672 `pseq` kl_elementP appl_3 kl_V1672)
                                                                                             klIf kl_if_4 (do !appl_5 <- kl_V1671 `pseq` tl kl_V1671
                                                                                                              appl_5 `pseq` (kl_V1672 `pseq` kl_union appl_5 kl_V1672)) (do !appl_6 <- kl_V1671 `pseq` hd kl_V1671
                                                                                                                                                                            !appl_7 <- kl_V1671 `pseq` tl kl_V1671
                                                                                                                                                                            !appl_8 <- appl_7 `pseq` (kl_V1672 `pseq` kl_union appl_7 kl_V1672)
                                                                                                                                                                            appl_6 `pseq` (appl_8 `pseq` klCons appl_6 appl_8))) (do klIf (Atom (B True)) (do let !aw_9 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                              applyWrapper aw_9 [ApplC (wrapNamed "union" kl_union)]) (do return (List []))))

kl_y_or_nP :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_y_or_nP (!kl_V1673) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Message) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Y_or_N) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Input) -> do !kl_if_3 <- kl_Input `pseq` eq (Types.Atom (Types.Str "y")) kl_Input
                                                                                                                                                                                                                               klIf kl_if_3 (do return (Atom (B True))) (do !kl_if_4 <- kl_Input `pseq` eq (Types.Atom (Types.Str "n")) kl_Input
                                                                                                                                                                                                                                                                            klIf kl_if_4 (do return (Atom (B False))) (do !appl_5 <- kl_stoutput
                                                                                                                                                                                                                                                                                                                          let !aw_6 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                                                                          !appl_7 <- appl_5 `pseq` applyWrapper aw_6 [Types.Atom (Types.Str "please answer y or n\n"),
                                                                                                                                                                                                                                                                                                                                                                      appl_5]
                                                                                                                                                                                                                                                                                                                          !appl_8 <- kl_V1673 `pseq` kl_y_or_nP kl_V1673
                                                                                                                                                                                                                                                                                                                          appl_7 `pseq` (appl_8 `pseq` kl_do appl_7 appl_8))))))
                                                                                                                                                               !appl_9 <- kl_stinput
                                                                                                                                                               let !aw_10 = Types.Atom (Types.UnboundSym "read")
                                                                                                                                                               !appl_11 <- appl_9 `pseq` applyWrapper aw_10 [appl_9]
                                                                                                                                                               let !aw_12 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                               !appl_13 <- appl_11 `pseq` applyWrapper aw_12 [appl_11,
                                                                                                                                                                                                              Types.Atom (Types.Str ""),
                                                                                                                                                                                                              Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                                               appl_13 `pseq` applyWrapper appl_2 [appl_13])))
                                                                                              !appl_14 <- kl_stoutput
                                                                                              let !aw_15 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                              !appl_16 <- appl_14 `pseq` applyWrapper aw_15 [Types.Atom (Types.Str " (y/n) "),
                                                                                                                                             appl_14]
                                                                                              appl_16 `pseq` applyWrapper appl_1 [appl_16])))
                            let !aw_17 = Types.Atom (Types.UnboundSym "shen.proc-nl")
                            !appl_18 <- kl_V1673 `pseq` applyWrapper aw_17 [kl_V1673]
                            !appl_19 <- kl_stoutput
                            let !aw_20 = Types.Atom (Types.UnboundSym "shen.prhush")
                            !appl_21 <- appl_18 `pseq` (appl_19 `pseq` applyWrapper aw_20 [appl_18,
                                                                                           appl_19])
                            appl_21 `pseq` applyWrapper appl_0 [appl_21]

kl_not :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_not (!kl_V1674) = do klIf kl_V1674 (do return (Atom (B False))) (do return (Atom (B True)))

kl_subst :: Types.KLValue ->
            Types.KLValue ->
            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_subst (!kl_V1684) (!kl_V1685) (!kl_V1686) = do !kl_if_0 <- kl_V1686 `pseq` (kl_V1685 `pseq` eq kl_V1686 kl_V1685)
                                                  klIf kl_if_0 (do return kl_V1684) (do !kl_if_1 <- kl_V1686 `pseq` consP kl_V1686
                                                                                        klIf kl_if_1 (do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_W) -> do kl_V1684 `pseq` (kl_V1685 `pseq` (kl_W `pseq` kl_subst kl_V1684 kl_V1685 kl_W)))))
                                                                                                         appl_2 `pseq` (kl_V1686 `pseq` kl_map appl_2 kl_V1686)) (do klIf (Atom (B True)) (do return kl_V1686) (do return (List []))))

kl_explode :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_explode (!kl_V1687) = do let !aw_0 = Types.Atom (Types.UnboundSym "shen.app")
                            !appl_1 <- kl_V1687 `pseq` applyWrapper aw_0 [kl_V1687,
                                                                          Types.Atom (Types.Str ""),
                                                                          Types.Atom (Types.UnboundSym "shen.a")]
                            appl_1 `pseq` kl_shen_explode_h appl_1

kl_shen_explode_h :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_explode_h (!kl_V1688) = do !kl_if_0 <- kl_V1688 `pseq` eq (Types.Atom (Types.Str "")) kl_V1688
                                   klIf kl_if_0 (do return (List [])) (do !kl_if_1 <- kl_V1688 `pseq` kl_shen_PlusstringP kl_V1688
                                                                          klIf kl_if_1 (do !appl_2 <- kl_V1688 `pseq` pos kl_V1688 (Types.Atom (Types.N (Types.KI 0)))
                                                                                           !appl_3 <- kl_V1688 `pseq` tlstr kl_V1688
                                                                                           !appl_4 <- appl_3 `pseq` kl_shen_explode_h appl_3
                                                                                           appl_2 `pseq` (appl_4 `pseq` klCons appl_2 appl_4)) (do klIf (Atom (B True)) (do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                            applyWrapper aw_5 [ApplC (wrapNamed "shen.explode-h" kl_shen_explode_h)]) (do return (List []))))

kl_cd :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_cd (!kl_V1689) = do !kl_if_0 <- kl_V1689 `pseq` eq kl_V1689 (Types.Atom (Types.Str ""))
                       !appl_1 <- klIf kl_if_0 (do return (Types.Atom (Types.Str ""))) (do let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                           kl_V1689 `pseq` applyWrapper aw_2 [kl_V1689,
                                                                                                                              Types.Atom (Types.Str "/"),
                                                                                                                              Types.Atom (Types.UnboundSym "shen.a")])
                       appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "*home-directory*")) appl_1

kl_map :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_map (!kl_V1690) (!kl_V1691) = do let !appl_0 = List []
                                    kl_V1690 `pseq` (kl_V1691 `pseq` (appl_0 `pseq` kl_shen_map_h kl_V1690 kl_V1691 appl_0))

kl_shen_map_h :: Types.KLValue ->
                 Types.KLValue ->
                 Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_map_h (!kl_V1694) (!kl_V1695) (!kl_V1696) = do let !appl_0 = List []
                                                       !kl_if_1 <- appl_0 `pseq` (kl_V1695 `pseq` eq appl_0 kl_V1695)
                                                       klIf kl_if_1 (do kl_V1696 `pseq` kl_reverse kl_V1696) (do !kl_if_2 <- kl_V1695 `pseq` consP kl_V1695
                                                                                                                 klIf kl_if_2 (do !appl_3 <- kl_V1695 `pseq` tl kl_V1695
                                                                                                                                  !appl_4 <- kl_V1695 `pseq` hd kl_V1695
                                                                                                                                  !appl_5 <- appl_4 `pseq` applyWrapper kl_V1694 [appl_4]
                                                                                                                                  !appl_6 <- appl_5 `pseq` (kl_V1696 `pseq` klCons appl_5 kl_V1696)
                                                                                                                                  kl_V1694 `pseq` (appl_3 `pseq` (appl_6 `pseq` kl_shen_map_h kl_V1694 appl_3 appl_6))) (do klIf (Atom (B True)) (do let !aw_7 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                     applyWrapper aw_7 [ApplC (wrapNamed "shen.map-h" kl_shen_map_h)]) (do return (List []))))

kl_length :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_length (!kl_V1697) = do kl_V1697 `pseq` kl_shen_length_h kl_V1697 (Types.Atom (Types.N (Types.KI 0)))

kl_shen_length_h :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_length_h (!kl_V1698) (!kl_V1699) = do let !appl_0 = List []
                                              !kl_if_1 <- appl_0 `pseq` (kl_V1698 `pseq` eq appl_0 kl_V1698)
                                              klIf kl_if_1 (do return kl_V1699) (do klIf (Atom (B True)) (do !appl_2 <- kl_V1698 `pseq` tl kl_V1698
                                                                                                             !appl_3 <- kl_V1699 `pseq` add kl_V1699 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                             appl_2 `pseq` (appl_3 `pseq` kl_shen_length_h appl_2 appl_3)) (do return (List [])))

kl_occurrences :: Types.KLValue ->
                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_occurrences (!kl_V1709) (!kl_V1710) = do !kl_if_0 <- kl_V1710 `pseq` (kl_V1709 `pseq` eq kl_V1710 kl_V1709)
                                            klIf kl_if_0 (do return (Types.Atom (Types.N (Types.KI 1)))) (do !kl_if_1 <- kl_V1710 `pseq` consP kl_V1710
                                                                                                             klIf kl_if_1 (do !appl_2 <- kl_V1710 `pseq` hd kl_V1710
                                                                                                                              !appl_3 <- kl_V1709 `pseq` (appl_2 `pseq` kl_occurrences kl_V1709 appl_2)
                                                                                                                              !appl_4 <- kl_V1710 `pseq` tl kl_V1710
                                                                                                                              !appl_5 <- kl_V1709 `pseq` (appl_4 `pseq` kl_occurrences kl_V1709 appl_4)
                                                                                                                              appl_3 `pseq` (appl_5 `pseq` add appl_3 appl_5)) (do klIf (Atom (B True)) (do return (Types.Atom (Types.N (Types.KI 0)))) (do return (List []))))

kl_nth :: Types.KLValue ->
          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_nth (!kl_V1717) (!kl_V1718) = do !kl_if_0 <- kl_V1717 `pseq` eq (Types.Atom (Types.N (Types.KI 1))) kl_V1717
                                    !kl_if_1 <- klIf kl_if_0 (do kl_V1718 `pseq` consP kl_V1718) (do return (Atom (B False)))
                                    klIf kl_if_1 (do kl_V1718 `pseq` hd kl_V1718) (do !kl_if_2 <- kl_V1718 `pseq` consP kl_V1718
                                                                                      klIf kl_if_2 (do !appl_3 <- kl_V1717 `pseq` Primitives.subtract kl_V1717 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                       !appl_4 <- kl_V1718 `pseq` tl kl_V1718
                                                                                                       appl_3 `pseq` (appl_4 `pseq` kl_nth appl_3 appl_4)) (do klIf (Atom (B True)) (do let !aw_5 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                        applyWrapper aw_5 [ApplC (wrapNamed "nth" kl_nth)]) (do return (List []))))

kl_integerP :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_integerP (!kl_V1719) = do !kl_if_0 <- kl_V1719 `pseq` numberP kl_V1719
                             klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Abs) -> do !appl_2 <- kl_Abs `pseq` kl_shen_magless kl_Abs (Types.Atom (Types.N (Types.KI 1)))
                                                                                                            kl_Abs `pseq` (appl_2 `pseq` kl_shen_integer_testP kl_Abs appl_2))))
                                              !appl_3 <- kl_V1719 `pseq` kl_shen_abs kl_V1719
                                              appl_3 `pseq` applyWrapper appl_1 [appl_3]) (do return (Atom (B False)))

kl_shen_abs :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_shen_abs (!kl_V1720) = do !kl_if_0 <- kl_V1720 `pseq` greaterThan kl_V1720 (Types.Atom (Types.N (Types.KI 0)))
                             klIf kl_if_0 (do return kl_V1720) (do kl_V1720 `pseq` Primitives.subtract (Types.Atom (Types.N (Types.KI 0))) kl_V1720)

kl_shen_magless :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_magless (!kl_V1721) (!kl_V1722) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Nx2) -> do !kl_if_1 <- kl_Nx2 `pseq` (kl_V1721 `pseq` greaterThan kl_Nx2 kl_V1721)
                                                                                                           klIf kl_if_1 (do return kl_V1722) (do kl_V1721 `pseq` (kl_Nx2 `pseq` kl_shen_magless kl_V1721 kl_Nx2)))))
                                             !appl_2 <- kl_V1722 `pseq` multiply kl_V1722 (Types.Atom (Types.N (Types.KI 2)))
                                             appl_2 `pseq` applyWrapper appl_0 [appl_2]

kl_shen_integer_testP :: Types.KLValue ->
                         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_integer_testP (!kl_V1726) (!kl_V1727) = do !kl_if_0 <- kl_V1726 `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_V1726
                                                   klIf kl_if_0 (do return (Atom (B True))) (do !kl_if_1 <- kl_V1726 `pseq` greaterThan (Types.Atom (Types.N (Types.KI 1))) kl_V1726
                                                                                                klIf kl_if_1 (do return (Atom (B False))) (do klIf (Atom (B True)) (do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Abs_N) -> do !kl_if_3 <- kl_Abs_N `pseq` greaterThan (Types.Atom (Types.N (Types.KI 0))) kl_Abs_N
                                                                                                                                                                                                                                       klIf kl_if_3 (do kl_V1726 `pseq` kl_integerP kl_V1726) (do kl_Abs_N `pseq` (kl_V1727 `pseq` kl_shen_integer_testP kl_Abs_N kl_V1727)))))
                                                                                                                                                                       !appl_4 <- kl_V1726 `pseq` (kl_V1727 `pseq` Primitives.subtract kl_V1726 kl_V1727)
                                                                                                                                                                       appl_4 `pseq` applyWrapper appl_2 [appl_4]) (do return (List []))))

kl_mapcan :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_mapcan (!kl_V1730) (!kl_V1731) = do let !appl_0 = List []
                                       !kl_if_1 <- appl_0 `pseq` (kl_V1731 `pseq` eq appl_0 kl_V1731)
                                       klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V1731 `pseq` consP kl_V1731
                                                                              klIf kl_if_2 (do !appl_3 <- kl_V1731 `pseq` hd kl_V1731
                                                                                               !appl_4 <- appl_3 `pseq` applyWrapper kl_V1730 [appl_3]
                                                                                               !appl_5 <- kl_V1731 `pseq` tl kl_V1731
                                                                                               !appl_6 <- kl_V1730 `pseq` (appl_5 `pseq` kl_mapcan kl_V1730 appl_5)
                                                                                               appl_4 `pseq` (appl_6 `pseq` kl_append appl_4 appl_6)) (do klIf (Atom (B True)) (do let !aw_7 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                   applyWrapper aw_7 [ApplC (wrapNamed "mapcan" kl_mapcan)]) (do return (List []))))

kl_EqEq :: Types.KLValue ->
           Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_EqEq (!kl_V1741) (!kl_V1742) = do !kl_if_0 <- kl_V1742 `pseq` (kl_V1741 `pseq` eq kl_V1742 kl_V1741)
                                     klIf kl_if_0 (do return (Atom (B True))) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List [])))

kl_abort :: Types.KLContext Types.Env Types.KLValue
kl_abort = do simpleError (Types.Atom (Types.Str ""))

kl_boundP :: Types.KLValue ->
             Types.KLContext Types.Env Types.KLValue
kl_boundP (!kl_V1743) = do !kl_if_0 <- kl_V1743 `pseq` kl_symbolP kl_V1743
                           klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Val) -> do !kl_if_2 <- kl_Val `pseq` eq kl_Val (Types.Atom (Types.UnboundSym "shen.this-symbol-is-unbound"))
                                                                                                          klIf kl_if_2 (do return (Atom (B False))) (do return (Atom (B True))))))
                                            !appl_3 <- (do kl_V1743 `pseq` value kl_V1743) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.this-symbol-is-unbound")))
                                            appl_3 `pseq` applyWrapper appl_1 [appl_3]) (do return (Atom (B False)))

kl_shen_string_RBbytes :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_string_RBbytes (!kl_V1744) = do !kl_if_0 <- kl_V1744 `pseq` eq (Types.Atom (Types.Str "")) kl_V1744
                                        klIf kl_if_0 (do return (List [])) (do klIf (Atom (B True)) (do !appl_1 <- kl_V1744 `pseq` pos kl_V1744 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                        !appl_2 <- appl_1 `pseq` stringToN appl_1
                                                                                                        !appl_3 <- kl_V1744 `pseq` tlstr kl_V1744
                                                                                                        !appl_4 <- appl_3 `pseq` kl_shen_string_RBbytes appl_3
                                                                                                        appl_2 `pseq` (appl_4 `pseq` klCons appl_2 appl_4)) (do return (List [])))

kl_maxinferences :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_maxinferences (!kl_V1745) = do kl_V1745 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*maxinferences*")) kl_V1745

kl_inferences :: Types.KLContext Types.Env Types.KLValue
kl_inferences = do value (Types.Atom (Types.UnboundSym "shen.*infs*"))

kl_protect :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_protect (!kl_V1746) = do return kl_V1746

kl_stoutput :: Types.KLContext Types.Env Types.KLValue
kl_stoutput = do value (Types.Atom (Types.UnboundSym "*stoutput*"))

kl_string_RBsymbol :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_string_RBsymbol (!kl_V1747) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Symbol) -> do !kl_if_1 <- kl_Symbol `pseq` kl_symbolP kl_Symbol
                                                                                                     klIf kl_if_1 (do return kl_Symbol) (do let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                            !appl_3 <- kl_V1747 `pseq` applyWrapper aw_2 [kl_V1747,
                                                                                                                                                                                          Types.Atom (Types.Str " to a symbol"),
                                                                                                                                                                                          Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                            !appl_4 <- appl_3 `pseq` cn (Types.Atom (Types.Str "cannot intern ")) appl_3
                                                                                                                                            appl_4 `pseq` simpleError appl_4))))
                                    !appl_5 <- kl_V1747 `pseq` intern kl_V1747
                                    appl_5 `pseq` applyWrapper appl_0 [appl_5]

kl_optimise :: Types.KLValue ->
               Types.KLContext Types.Env Types.KLValue
kl_optimise (!kl_V1752) = do !kl_if_0 <- kl_V1752 `pseq` eq (ApplC (wrapNamed "+" add)) kl_V1752
                             klIf kl_if_0 (do klSet (Types.Atom (Types.UnboundSym "shen.*optimise*")) (Atom (B True))) (do !kl_if_1 <- kl_V1752 `pseq` eq (ApplC (wrapNamed "-" Primitives.subtract)) kl_V1752
                                                                                                                           klIf kl_if_1 (do klSet (Types.Atom (Types.UnboundSym "shen.*optimise*")) (Atom (B False))) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "optimise expects a + or a -.\n"))) (do return (List []))))

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
kl_packageP (!kl_V1753) = do (do !appl_0 <- kl_V1753 `pseq` kl_external kl_V1753
                                 appl_0 `pseq` kl_do appl_0 (Atom (B True))) `catchError` (\(!kl_E) -> do return (Atom (B False)))

expr2 :: Types.KLContext Types.Env Types.KLValue
expr2 = do (return $ List [])
