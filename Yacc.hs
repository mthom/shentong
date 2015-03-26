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

module Yacc where

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

kl_shen_yacc :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_shen_yacc (!kl_V2470) = do !kl_if_0 <- kl_V2470 `pseq` consP kl_V2470
                              !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2470 `pseq` hd kl_V2470
                                                           !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "defcc")) appl_2
                                                           klIf kl_if_3 (do !appl_4 <- kl_V2470 `pseq` tl kl_V2470
                                                                            appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                              klIf kl_if_1 (do !appl_5 <- kl_V2470 `pseq` tl kl_V2470
                                               !appl_6 <- appl_5 `pseq` hd appl_5
                                               !appl_7 <- kl_V2470 `pseq` tl kl_V2470
                                               !appl_8 <- appl_7 `pseq` tl appl_7
                                               appl_6 `pseq` (appl_8 `pseq` kl_shen_yacc_RBshen appl_6 appl_8)) (do klIf (Atom (B True)) (do let !aw_9 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                             applyWrapper aw_9 [ApplC (wrapNamed "shen.yacc" kl_shen_yacc)]) (do return (List [])))

kl_shen_yacc_RBshen :: Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_yacc_RBshen (!kl_V2471) (!kl_V2472) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_CCRules) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_CCBody) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_YaccCases) -> do !appl_3 <- kl_YaccCases `pseq` kl_shen_kill_code kl_YaccCases
                                                                                                                                                                                                                                                        let !appl_4 = List []
                                                                                                                                                                                                                                                        !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                                                                                                                                                                        !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_5
                                                                                                                                                                                                                                                        !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "Stream")) appl_6
                                                                                                                                                                                                                                                        !appl_8 <- kl_V2471 `pseq` (appl_7 `pseq` klCons kl_V2471 appl_7)
                                                                                                                                                                                                                                                        appl_8 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_8)))
                                                                                                                                                                                    !appl_9 <- kl_CCBody `pseq` kl_shen_yacc_cases kl_CCBody
                                                                                                                                                                                    appl_9 `pseq` applyWrapper appl_2 [appl_9])))
                                                                                                                   let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_V2468) -> do kl_V2468 `pseq` kl_shen_cc_body kl_V2468)))
                                                                                                                   !appl_11 <- appl_10 `pseq` (kl_CCRules `pseq` kl_map appl_10 kl_CCRules)
                                                                                                                   appl_11 `pseq` applyWrapper appl_1 [appl_11])))
                                                 let !appl_12 = List []
                                                 !appl_13 <- kl_V2472 `pseq` (appl_12 `pseq` kl_shen_split_cc_rules (Atom (B True)) kl_V2472 appl_12)
                                                 appl_13 `pseq` applyWrapper appl_0 [appl_13]

kl_shen_kill_code :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_kill_code (!kl_V2473) = do !appl_0 <- kl_V2473 `pseq` kl_occurrences (ApplC (PL "kill" kl_kill)) kl_V2473
                                   !kl_if_1 <- appl_0 `pseq` greaterThan appl_0 (Types.Atom (Types.N (Types.KI 0)))
                                   klIf kl_if_1 (do let !appl_2 = List []
                                                    !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_2
                                                    !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "shen.analyse-kill" kl_shen_analyse_kill)) appl_3
                                                    let !appl_5 = List []
                                                    !appl_6 <- appl_4 `pseq` (appl_5 `pseq` klCons appl_4 appl_5)
                                                    !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_6
                                                    !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_7
                                                    let !appl_9 = List []
                                                    !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                    !appl_11 <- kl_V2473 `pseq` (appl_10 `pseq` klCons kl_V2473 appl_10)
                                                    appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "trap-error")) appl_11) (do klIf (Atom (B True)) (do return kl_V2473) (do return (List [])))

kl_kill :: Types.KLContext Types.Env Types.KLValue
kl_kill = do simpleError (Types.Atom (Types.Str "yacc kill"))

kl_shen_analyse_kill :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_analyse_kill (!kl_V2474) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_String) -> do !kl_if_1 <- kl_String `pseq` eq kl_String (Types.Atom (Types.Str "yacc kill"))
                                                                                                       klIf kl_if_1 (do kl_fail) (do return kl_V2474))))
                                      !appl_2 <- kl_V2474 `pseq` errorToString kl_V2474
                                      appl_2 `pseq` applyWrapper appl_0 [appl_2]

kl_shen_split_cc_rules :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_split_cc_rules (!kl_V2477) (!kl_V2478) (!kl_V2479) = do let !appl_0 = List []
                                                                !kl_if_1 <- appl_0 `pseq` (kl_V2478 `pseq` eq appl_0 kl_V2478)
                                                                !kl_if_2 <- klIf kl_if_1 (do let !appl_3 = List []
                                                                                             appl_3 `pseq` (kl_V2479 `pseq` eq appl_3 kl_V2479)) (do return (Atom (B False)))
                                                                klIf kl_if_2 (do return (List [])) (do let !appl_4 = List []
                                                                                                       !kl_if_5 <- appl_4 `pseq` (kl_V2478 `pseq` eq appl_4 kl_V2478)
                                                                                                       klIf kl_if_5 (do !appl_6 <- kl_V2479 `pseq` kl_reverse kl_V2479
                                                                                                                        let !appl_7 = List []
                                                                                                                        !appl_8 <- kl_V2477 `pseq` (appl_6 `pseq` (appl_7 `pseq` kl_shen_split_cc_rule kl_V2477 appl_6 appl_7))
                                                                                                                        let !appl_9 = List []
                                                                                                                        appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)) (do !kl_if_10 <- kl_V2478 `pseq` consP kl_V2478
                                                                                                                                                                                !kl_if_11 <- klIf kl_if_10 (do !appl_12 <- kl_V2478 `pseq` hd kl_V2478
                                                                                                                                                                                                               appl_12 `pseq` eq (Types.Atom (Types.UnboundSym ";")) appl_12) (do return (Atom (B False)))
                                                                                                                                                                                klIf kl_if_11 (do !appl_13 <- kl_V2479 `pseq` kl_reverse kl_V2479
                                                                                                                                                                                                  let !appl_14 = List []
                                                                                                                                                                                                  !appl_15 <- kl_V2477 `pseq` (appl_13 `pseq` (appl_14 `pseq` kl_shen_split_cc_rule kl_V2477 appl_13 appl_14))
                                                                                                                                                                                                  !appl_16 <- kl_V2478 `pseq` tl kl_V2478
                                                                                                                                                                                                  let !appl_17 = List []
                                                                                                                                                                                                  !appl_18 <- kl_V2477 `pseq` (appl_16 `pseq` (appl_17 `pseq` kl_shen_split_cc_rules kl_V2477 appl_16 appl_17))
                                                                                                                                                                                                  appl_15 `pseq` (appl_18 `pseq` klCons appl_15 appl_18)) (do !kl_if_19 <- kl_V2478 `pseq` consP kl_V2478
                                                                                                                                                                                                                                                              klIf kl_if_19 (do !appl_20 <- kl_V2478 `pseq` tl kl_V2478
                                                                                                                                                                                                                                                                                !appl_21 <- kl_V2478 `pseq` hd kl_V2478
                                                                                                                                                                                                                                                                                !appl_22 <- appl_21 `pseq` (kl_V2479 `pseq` klCons appl_21 kl_V2479)
                                                                                                                                                                                                                                                                                kl_V2477 `pseq` (appl_20 `pseq` (appl_22 `pseq` kl_shen_split_cc_rules kl_V2477 appl_20 appl_22))) (do klIf (Atom (B True)) (do let !aw_23 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                                                                                                applyWrapper aw_23 [ApplC (wrapNamed "shen.split_cc_rules" kl_shen_split_cc_rules)]) (do return (List []))))))

kl_shen_split_cc_rule :: Types.KLValue ->
                         Types.KLValue ->
                         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_split_cc_rule (!kl_V2484) (!kl_V2485) (!kl_V2486) = do !kl_if_0 <- kl_V2485 `pseq` consP kl_V2485
                                                               !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2485 `pseq` hd kl_V2485
                                                                                            !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym ":=")) appl_2
                                                                                            klIf kl_if_3 (do !appl_4 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                             !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                             klIf kl_if_5 (do let !appl_6 = List []
                                                                                                                              !appl_7 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                              !appl_8 <- appl_7 `pseq` tl appl_7
                                                                                                                              appl_6 `pseq` (appl_8 `pseq` eq appl_6 appl_8)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                               klIf kl_if_1 (do !appl_9 <- kl_V2486 `pseq` kl_reverse kl_V2486
                                                                                !appl_10 <- kl_V2485 `pseq` tl kl_V2485
                                                                                appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)) (do !kl_if_11 <- kl_V2485 `pseq` consP kl_V2485
                                                                                                                                          !kl_if_12 <- klIf kl_if_11 (do !appl_13 <- kl_V2485 `pseq` hd kl_V2485
                                                                                                                                                                         !kl_if_14 <- appl_13 `pseq` eq (Types.Atom (Types.UnboundSym ":=")) appl_13
                                                                                                                                                                         klIf kl_if_14 (do !appl_15 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                                                           !kl_if_16 <- appl_15 `pseq` consP appl_15
                                                                                                                                                                                           klIf kl_if_16 (do !appl_17 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                                                                             !appl_18 <- appl_17 `pseq` tl appl_17
                                                                                                                                                                                                             !kl_if_19 <- appl_18 `pseq` consP appl_18
                                                                                                                                                                                                             klIf kl_if_19 (do !appl_20 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                                                                                               !appl_21 <- appl_20 `pseq` tl appl_20
                                                                                                                                                                                                                               !appl_22 <- appl_21 `pseq` hd appl_21
                                                                                                                                                                                                                               !kl_if_23 <- appl_22 `pseq` eq (Types.Atom (Types.UnboundSym "where")) appl_22
                                                                                                                                                                                                                               klIf kl_if_23 (do !appl_24 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                                                                                                                 !appl_25 <- appl_24 `pseq` tl appl_24
                                                                                                                                                                                                                                                 !appl_26 <- appl_25 `pseq` tl appl_25
                                                                                                                                                                                                                                                 !kl_if_27 <- appl_26 `pseq` consP appl_26
                                                                                                                                                                                                                                                 klIf kl_if_27 (do let !appl_28 = List []
                                                                                                                                                                                                                                                                   !appl_29 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                                                                                                                                   !appl_30 <- appl_29 `pseq` tl appl_29
                                                                                                                                                                                                                                                                   !appl_31 <- appl_30 `pseq` tl appl_30
                                                                                                                                                                                                                                                                   !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                                                                                                   appl_28 `pseq` (appl_32 `pseq` eq appl_28 appl_32)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                          klIf kl_if_12 (do !appl_33 <- kl_V2486 `pseq` kl_reverse kl_V2486
                                                                                                                                                            !appl_34 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                            !appl_35 <- appl_34 `pseq` tl appl_34
                                                                                                                                                            !appl_36 <- appl_35 `pseq` tl appl_35
                                                                                                                                                            !appl_37 <- appl_36 `pseq` hd appl_36
                                                                                                                                                            !appl_38 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                            !appl_39 <- appl_38 `pseq` hd appl_38
                                                                                                                                                            let !appl_40 = List []
                                                                                                                                                            !appl_41 <- appl_39 `pseq` (appl_40 `pseq` klCons appl_39 appl_40)
                                                                                                                                                            !appl_42 <- appl_37 `pseq` (appl_41 `pseq` klCons appl_37 appl_41)
                                                                                                                                                            !appl_43 <- appl_42 `pseq` klCons (Types.Atom (Types.UnboundSym "where")) appl_42
                                                                                                                                                            let !appl_44 = List []
                                                                                                                                                            !appl_45 <- appl_43 `pseq` (appl_44 `pseq` klCons appl_43 appl_44)
                                                                                                                                                            appl_33 `pseq` (appl_45 `pseq` klCons appl_33 appl_45)) (do let !appl_46 = List []
                                                                                                                                                                                                                        !kl_if_47 <- appl_46 `pseq` (kl_V2485 `pseq` eq appl_46 kl_V2485)
                                                                                                                                                                                                                        klIf kl_if_47 (do !appl_48 <- kl_V2484 `pseq` (kl_V2486 `pseq` kl_shen_semantic_completion_warning kl_V2484 kl_V2486)
                                                                                                                                                                                                                                          !appl_49 <- kl_V2486 `pseq` kl_reverse kl_V2486
                                                                                                                                                                                                                                          !appl_50 <- appl_49 `pseq` kl_shen_default_semantics appl_49
                                                                                                                                                                                                                                          let !appl_51 = List []
                                                                                                                                                                                                                                          !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                                                                                                                                                                                                                                          !appl_53 <- appl_52 `pseq` klCons (Types.Atom (Types.UnboundSym ":=")) appl_52
                                                                                                                                                                                                                                          !appl_54 <- kl_V2484 `pseq` (appl_53 `pseq` (kl_V2486 `pseq` kl_shen_split_cc_rule kl_V2484 appl_53 kl_V2486))
                                                                                                                                                                                                                                          appl_48 `pseq` (appl_54 `pseq` kl_do appl_48 appl_54)) (do !kl_if_55 <- kl_V2485 `pseq` consP kl_V2485
                                                                                                                                                                                                                                                                                                     klIf kl_if_55 (do !appl_56 <- kl_V2485 `pseq` tl kl_V2485
                                                                                                                                                                                                                                                                                                                       !appl_57 <- kl_V2485 `pseq` hd kl_V2485
                                                                                                                                                                                                                                                                                                                       !appl_58 <- appl_57 `pseq` (kl_V2486 `pseq` klCons appl_57 kl_V2486)
                                                                                                                                                                                                                                                                                                                       kl_V2484 `pseq` (appl_56 `pseq` (appl_58 `pseq` kl_shen_split_cc_rule kl_V2484 appl_56 appl_58))) (do klIf (Atom (B True)) (do let !aw_59 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                                                                                                                                      applyWrapper aw_59 [ApplC (wrapNamed "shen.split_cc_rule" kl_shen_split_cc_rule)]) (do return (List []))))))

kl_shen_semantic_completion_warning :: Types.KLValue ->
                                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_semantic_completion_warning (!kl_V2495) (!kl_V2496) = do !kl_if_0 <- kl_V2495 `pseq` eq (Atom (B True)) kl_V2495
                                                                 klIf kl_if_0 (do !appl_1 <- kl_stoutput
                                                                                  let !aw_2 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                  !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [Types.Atom (Types.Str "warning: "),
                                                                                                                              appl_1]
                                                                                  let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                              !appl_6 <- kl_X `pseq` applyWrapper aw_5 [kl_X,
                                                                                                                                                                                        Types.Atom (Types.Str " "),
                                                                                                                                                                                        Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                              !appl_7 <- kl_stoutput
                                                                                                                                              let !aw_8 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                              appl_6 `pseq` (appl_7 `pseq` applyWrapper aw_8 [appl_6,
                                                                                                                                                                                              appl_7]))))
                                                                                  !appl_9 <- kl_V2496 `pseq` kl_reverse kl_V2496
                                                                                  !appl_10 <- appl_4 `pseq` (appl_9 `pseq` kl_map appl_4 appl_9)
                                                                                  !appl_11 <- kl_stoutput
                                                                                  let !aw_12 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                  !appl_13 <- appl_11 `pseq` applyWrapper aw_12 [Types.Atom (Types.Str "has no semantics.\n"),
                                                                                                                                 appl_11]
                                                                                  !appl_14 <- appl_10 `pseq` (appl_13 `pseq` kl_do appl_10 appl_13)
                                                                                  appl_3 `pseq` (appl_14 `pseq` kl_do appl_3 appl_14)) (do klIf (Atom (B True)) (do return (Types.Atom (Types.UnboundSym "shen.skip"))) (do return (List [])))

kl_shen_default_semantics :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_default_semantics (!kl_V2497) = do let !appl_0 = List []
                                           !kl_if_1 <- appl_0 `pseq` (kl_V2497 `pseq` eq appl_0 kl_V2497)
                                           klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V2497 `pseq` consP kl_V2497
                                                                                  !kl_if_3 <- klIf kl_if_2 (do let !appl_4 = List []
                                                                                                               !appl_5 <- kl_V2497 `pseq` tl kl_V2497
                                                                                                               !kl_if_6 <- appl_4 `pseq` (appl_5 `pseq` eq appl_4 appl_5)
                                                                                                               klIf kl_if_6 (do !appl_7 <- kl_V2497 `pseq` hd kl_V2497
                                                                                                                                appl_7 `pseq` kl_shen_grammar_symbolP appl_7) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                  klIf kl_if_3 (do kl_V2497 `pseq` hd kl_V2497) (do !kl_if_8 <- kl_V2497 `pseq` consP kl_V2497
                                                                                                                                    !kl_if_9 <- klIf kl_if_8 (do !appl_10 <- kl_V2497 `pseq` hd kl_V2497
                                                                                                                                                                 appl_10 `pseq` kl_shen_grammar_symbolP appl_10) (do return (Atom (B False)))
                                                                                                                                    klIf kl_if_9 (do !appl_11 <- kl_V2497 `pseq` hd kl_V2497
                                                                                                                                                     !appl_12 <- kl_V2497 `pseq` tl kl_V2497
                                                                                                                                                     !appl_13 <- appl_12 `pseq` kl_shen_default_semantics appl_12
                                                                                                                                                     let !appl_14 = List []
                                                                                                                                                     !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                                                                                                                                                     !appl_16 <- appl_11 `pseq` (appl_15 `pseq` klCons appl_11 appl_15)
                                                                                                                                                     appl_16 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_16) (do !kl_if_17 <- kl_V2497 `pseq` consP kl_V2497
                                                                                                                                                                                                                               klIf kl_if_17 (do !appl_18 <- kl_V2497 `pseq` hd kl_V2497
                                                                                                                                                                                                                                                 !appl_19 <- kl_V2497 `pseq` tl kl_V2497
                                                                                                                                                                                                                                                 !appl_20 <- appl_19 `pseq` kl_shen_default_semantics appl_19
                                                                                                                                                                                                                                                 let !appl_21 = List []
                                                                                                                                                                                                                                                 !appl_22 <- appl_20 `pseq` (appl_21 `pseq` klCons appl_20 appl_21)
                                                                                                                                                                                                                                                 !appl_23 <- appl_18 `pseq` (appl_22 `pseq` klCons appl_18 appl_22)
                                                                                                                                                                                                                                                 appl_23 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_23) (do klIf (Atom (B True)) (do let !aw_24 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                               applyWrapper aw_24 [ApplC (wrapNamed "shen.default_semantics" kl_shen_default_semantics)]) (do return (List []))))))

kl_shen_grammar_symbolP :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_grammar_symbolP (!kl_V2498) = do !kl_if_0 <- kl_V2498 `pseq` kl_symbolP kl_V2498
                                         klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Cs) -> do !appl_2 <- kl_Cs `pseq` hd kl_Cs
                                                                                                                       !kl_if_3 <- appl_2 `pseq` eq appl_2 (Types.Atom (Types.Str "<"))
                                                                                                                       klIf kl_if_3 (do !appl_4 <- kl_Cs `pseq` kl_reverse kl_Cs
                                                                                                                                        !appl_5 <- appl_4 `pseq` hd appl_4
                                                                                                                                        appl_5 `pseq` eq appl_5 (Types.Atom (Types.Str ">"))) (do return (Atom (B False))))))
                                                          !appl_6 <- kl_V2498 `pseq` kl_explode kl_V2498
                                                          !appl_7 <- appl_6 `pseq` kl_shen_strip_pathname appl_6
                                                          appl_7 `pseq` applyWrapper appl_1 [appl_7]) (do return (Atom (B False)))

kl_shen_yacc_cases :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_yacc_cases (!kl_V2499) = do !kl_if_0 <- kl_V2499 `pseq` consP kl_V2499
                                    !kl_if_1 <- klIf kl_if_0 (do let !appl_2 = List []
                                                                 !appl_3 <- kl_V2499 `pseq` tl kl_V2499
                                                                 appl_2 `pseq` (appl_3 `pseq` eq appl_2 appl_3)) (do return (Atom (B False)))
                                    klIf kl_if_1 (do kl_V2499 `pseq` hd kl_V2499) (do !kl_if_4 <- kl_V2499 `pseq` consP kl_V2499
                                                                                      klIf kl_if_4 (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_P) -> do !appl_6 <- kl_V2499 `pseq` hd kl_V2499
                                                                                                                                                                   let !appl_7 = List []
                                                                                                                                                                   !appl_8 <- appl_7 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_7
                                                                                                                                                                   let !appl_9 = List []
                                                                                                                                                                   !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                                                                                                                                   !appl_11 <- kl_P `pseq` (appl_10 `pseq` klCons kl_P appl_10)
                                                                                                                                                                   !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_11
                                                                                                                                                                   !appl_13 <- kl_V2499 `pseq` tl kl_V2499
                                                                                                                                                                   !appl_14 <- appl_13 `pseq` kl_shen_yacc_cases appl_13
                                                                                                                                                                   let !appl_15 = List []
                                                                                                                                                                   !appl_16 <- kl_P `pseq` (appl_15 `pseq` klCons kl_P appl_15)
                                                                                                                                                                   !appl_17 <- appl_14 `pseq` (appl_16 `pseq` klCons appl_14 appl_16)
                                                                                                                                                                   !appl_18 <- appl_12 `pseq` (appl_17 `pseq` klCons appl_12 appl_17)
                                                                                                                                                                   !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_18
                                                                                                                                                                   let !appl_20 = List []
                                                                                                                                                                   !appl_21 <- appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)
                                                                                                                                                                   !appl_22 <- appl_6 `pseq` (appl_21 `pseq` klCons appl_6 appl_21)
                                                                                                                                                                   !appl_23 <- kl_P `pseq` (appl_22 `pseq` klCons kl_P appl_22)
                                                                                                                                                                   appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_23)))
                                                                                                       applyWrapper appl_5 [Types.Atom (Types.UnboundSym "YaccParse")]) (do klIf (Atom (B True)) (do let !aw_24 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                     applyWrapper aw_24 [ApplC (wrapNamed "shen.yacc_cases" kl_shen_yacc_cases)]) (do return (List []))))

kl_shen_cc_body :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_cc_body (!kl_V2500) = do !kl_if_0 <- kl_V2500 `pseq` consP kl_V2500
                                 !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2500 `pseq` tl kl_V2500
                                                              !kl_if_3 <- appl_2 `pseq` consP appl_2
                                                              klIf kl_if_3 (do let !appl_4 = List []
                                                                               !appl_5 <- kl_V2500 `pseq` tl kl_V2500
                                                                               !appl_6 <- appl_5 `pseq` tl appl_5
                                                                               appl_4 `pseq` (appl_6 `pseq` eq appl_4 appl_6)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                 klIf kl_if_1 (do !appl_7 <- kl_V2500 `pseq` hd kl_V2500
                                                  !appl_8 <- kl_V2500 `pseq` tl kl_V2500
                                                  !appl_9 <- appl_8 `pseq` hd appl_8
                                                  appl_7 `pseq` (appl_9 `pseq` kl_shen_syntax appl_7 (Types.Atom (Types.UnboundSym "Stream")) appl_9)) (do klIf (Atom (B True)) (do let !aw_10 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                    applyWrapper aw_10 [ApplC (wrapNamed "shen.cc_body" kl_shen_cc_body)]) (do return (List [])))

kl_shen_syntax :: Types.KLValue ->
                  Types.KLValue ->
                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_syntax (!kl_V2501) (!kl_V2502) (!kl_V2503) = do let !appl_0 = List []
                                                        !kl_if_1 <- appl_0 `pseq` (kl_V2501 `pseq` eq appl_0 kl_V2501)
                                                        !kl_if_2 <- klIf kl_if_1 (do !kl_if_3 <- kl_V2503 `pseq` consP kl_V2503
                                                                                     klIf kl_if_3 (do !appl_4 <- kl_V2503 `pseq` hd kl_V2503
                                                                                                      !kl_if_5 <- appl_4 `pseq` eq (Types.Atom (Types.UnboundSym "where")) appl_4
                                                                                                      klIf kl_if_5 (do !appl_6 <- kl_V2503 `pseq` tl kl_V2503
                                                                                                                       !kl_if_7 <- appl_6 `pseq` consP appl_6
                                                                                                                       klIf kl_if_7 (do !appl_8 <- kl_V2503 `pseq` tl kl_V2503
                                                                                                                                        !appl_9 <- appl_8 `pseq` tl appl_8
                                                                                                                                        !kl_if_10 <- appl_9 `pseq` consP appl_9
                                                                                                                                        klIf kl_if_10 (do let !appl_11 = List []
                                                                                                                                                          !appl_12 <- kl_V2503 `pseq` tl kl_V2503
                                                                                                                                                          !appl_13 <- appl_12 `pseq` tl appl_12
                                                                                                                                                          !appl_14 <- appl_13 `pseq` tl appl_13
                                                                                                                                                          appl_11 `pseq` (appl_14 `pseq` eq appl_11 appl_14)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                        klIf kl_if_2 (do !appl_15 <- kl_V2503 `pseq` tl kl_V2503
                                                                         !appl_16 <- appl_15 `pseq` hd appl_15
                                                                         !appl_17 <- appl_16 `pseq` kl_shen_semantics appl_16
                                                                         let !appl_18 = List []
                                                                         !appl_19 <- kl_V2502 `pseq` (appl_18 `pseq` klCons kl_V2502 appl_18)
                                                                         !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_19
                                                                         !appl_21 <- kl_V2503 `pseq` tl kl_V2503
                                                                         !appl_22 <- appl_21 `pseq` tl appl_21
                                                                         !appl_23 <- appl_22 `pseq` hd appl_22
                                                                         !appl_24 <- appl_23 `pseq` kl_shen_semantics appl_23
                                                                         let !appl_25 = List []
                                                                         !appl_26 <- appl_24 `pseq` (appl_25 `pseq` klCons appl_24 appl_25)
                                                                         !appl_27 <- appl_20 `pseq` (appl_26 `pseq` klCons appl_20 appl_26)
                                                                         !appl_28 <- appl_27 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_27
                                                                         let !appl_29 = List []
                                                                         !appl_30 <- appl_29 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_29
                                                                         let !appl_31 = List []
                                                                         !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                         !appl_33 <- appl_28 `pseq` (appl_32 `pseq` klCons appl_28 appl_32)
                                                                         !appl_34 <- appl_17 `pseq` (appl_33 `pseq` klCons appl_17 appl_33)
                                                                         appl_34 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_34) (do let !appl_35 = List []
                                                                                                                                                 !kl_if_36 <- appl_35 `pseq` (kl_V2501 `pseq` eq appl_35 kl_V2501)
                                                                                                                                                 klIf kl_if_36 (do let !appl_37 = List []
                                                                                                                                                                   !appl_38 <- kl_V2502 `pseq` (appl_37 `pseq` klCons kl_V2502 appl_37)
                                                                                                                                                                   !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_38
                                                                                                                                                                   !appl_40 <- kl_V2503 `pseq` kl_shen_semantics kl_V2503
                                                                                                                                                                   let !appl_41 = List []
                                                                                                                                                                   !appl_42 <- appl_40 `pseq` (appl_41 `pseq` klCons appl_40 appl_41)
                                                                                                                                                                   !appl_43 <- appl_39 `pseq` (appl_42 `pseq` klCons appl_39 appl_42)
                                                                                                                                                                   appl_43 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_43) (do !kl_if_44 <- kl_V2501 `pseq` consP kl_V2501
                                                                                                                                                                                                                                                   klIf kl_if_44 (do !appl_45 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                     !kl_if_46 <- appl_45 `pseq` kl_shen_grammar_symbolP appl_45
                                                                                                                                                                                                                                                                     klIf kl_if_46 (do kl_V2501 `pseq` (kl_V2502 `pseq` (kl_V2503 `pseq` kl_shen_recursive_descent kl_V2501 kl_V2502 kl_V2503))) (do !appl_47 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                     !kl_if_48 <- appl_47 `pseq` kl_variableP appl_47
                                                                                                                                                                                                                                                                                                                                                                                                     klIf kl_if_48 (do kl_V2501 `pseq` (kl_V2502 `pseq` (kl_V2503 `pseq` kl_shen_variable_match kl_V2501 kl_V2502 kl_V2503))) (do !appl_49 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  !kl_if_50 <- appl_49 `pseq` kl_shen_jump_streamP appl_49
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  klIf kl_if_50 (do kl_V2501 `pseq` (kl_V2502 `pseq` (kl_V2503 `pseq` kl_shen_jump_stream kl_V2501 kl_V2502 kl_V2503))) (do !appl_51 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            !kl_if_52 <- appl_51 `pseq` kl_shen_terminalP appl_51
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            klIf kl_if_52 (do kl_V2501 `pseq` (kl_V2502 `pseq` (kl_V2503 `pseq` kl_shen_check_stream kl_V2501 kl_V2502 kl_V2503))) (do !appl_53 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       !kl_if_54 <- appl_53 `pseq` consP appl_53
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       klIf kl_if_54 (do !appl_55 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         !appl_56 <- appl_55 `pseq` kl_shen_decons appl_55
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         !appl_57 <- kl_V2501 `pseq` tl kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         appl_56 `pseq` (appl_57 `pseq` (kl_V2502 `pseq` (kl_V2503 `pseq` kl_shen_list_stream appl_56 appl_57 kl_V2502 kl_V2503)))) (do !appl_58 <- kl_V2501 `pseq` hd kl_V2501
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        let !aw_59 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        !appl_60 <- appl_58 `pseq` applyWrapper aw_59 [appl_58,
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Types.Atom (Types.Str " is not legal syntax\n"),
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        appl_60 `pseq` simpleError appl_60)))))) (do klIf (Atom (B True)) (do let !aw_61 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              applyWrapper aw_61 [ApplC (wrapNamed "shen.syntax" kl_shen_syntax)]) (do return (List [])))))

kl_shen_list_stream :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_list_stream (!kl_V2504) (!kl_V2505) (!kl_V2506) (!kl_V2507) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Placeholder) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_RunOn) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_4 = List []
                                                                                                                                                                                                                                                                                                                                               !appl_5 <- appl_4 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_4
                                                                                                                                                                                                                                                                                                                                               let !appl_6 = List []
                                                                                                                                                                                                                                                                                                                                               !appl_7 <- appl_5 `pseq` (appl_6 `pseq` klCons appl_5 appl_6)
                                                                                                                                                                                                                                                                                                                                               !appl_8 <- kl_Action `pseq` (appl_7 `pseq` klCons kl_Action appl_7)
                                                                                                                                                                                                                                                                                                                                               !appl_9 <- kl_Test `pseq` (appl_8 `pseq` klCons kl_Test appl_8)
                                                                                                                                                                                                                                                                                                                                               appl_9 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_9)))
                                                                                                                                                                                                                                                                              let !appl_10 = List []
                                                                                                                                                                                                                                                                              !appl_11 <- kl_V2506 `pseq` (appl_10 `pseq` klCons kl_V2506 appl_10)
                                                                                                                                                                                                                                                                              !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_11
                                                                                                                                                                                                                                                                              let !appl_13 = List []
                                                                                                                                                                                                                                                                              !appl_14 <- appl_12 `pseq` (appl_13 `pseq` klCons appl_12 appl_13)
                                                                                                                                                                                                                                                                              !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_14
                                                                                                                                                                                                                                                                              let !appl_16 = List []
                                                                                                                                                                                                                                                                              !appl_17 <- kl_V2506 `pseq` (appl_16 `pseq` klCons kl_V2506 appl_16)
                                                                                                                                                                                                                                                                              !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_17
                                                                                                                                                                                                                                                                              let !appl_19 = List []
                                                                                                                                                                                                                                                                              !appl_20 <- appl_18 `pseq` (appl_19 `pseq` klCons appl_18 appl_19)
                                                                                                                                                                                                                                                                              !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_20
                                                                                                                                                                                                                                                                              let !appl_22 = List []
                                                                                                                                                                                                                                                                              !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                                                                                                                                                                                                                                                                              !appl_24 <- appl_15 `pseq` (appl_23 `pseq` klCons appl_15 appl_23)
                                                                                                                                                                                                                                                                              !appl_25 <- appl_24 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_24
                                                                                                                                                                                                                                                                              !appl_26 <- kl_V2504 `pseq` (appl_25 `pseq` (kl_Placeholder `pseq` kl_shen_syntax kl_V2504 appl_25 kl_Placeholder))
                                                                                                                                                                                                                                                                              !appl_27 <- kl_RunOn `pseq` (kl_Placeholder `pseq` (appl_26 `pseq` kl_shen_insert_runon kl_RunOn kl_Placeholder appl_26))
                                                                                                                                                                                                                                                                              appl_27 `pseq` applyWrapper appl_3 [appl_27])))
                                                                                                                                                                                                              let !appl_28 = List []
                                                                                                                                                                                                              !appl_29 <- kl_V2506 `pseq` (appl_28 `pseq` klCons kl_V2506 appl_28)
                                                                                                                                                                                                              !appl_30 <- appl_29 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_29
                                                                                                                                                                                                              let !appl_31 = List []
                                                                                                                                                                                                              !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                                                                                                                                                              !appl_33 <- appl_32 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_32
                                                                                                                                                                                                              let !appl_34 = List []
                                                                                                                                                                                                              !appl_35 <- kl_V2506 `pseq` (appl_34 `pseq` klCons kl_V2506 appl_34)
                                                                                                                                                                                                              !appl_36 <- appl_35 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_35
                                                                                                                                                                                                              let !appl_37 = List []
                                                                                                                                                                                                              !appl_38 <- appl_36 `pseq` (appl_37 `pseq` klCons appl_36 appl_37)
                                                                                                                                                                                                              !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_38
                                                                                                                                                                                                              let !appl_40 = List []
                                                                                                                                                                                                              !appl_41 <- appl_39 `pseq` (appl_40 `pseq` klCons appl_39 appl_40)
                                                                                                                                                                                                              !appl_42 <- appl_33 `pseq` (appl_41 `pseq` klCons appl_33 appl_41)
                                                                                                                                                                                                              !appl_43 <- appl_42 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_42
                                                                                                                                                                                                              !appl_44 <- kl_V2505 `pseq` (appl_43 `pseq` (kl_V2507 `pseq` kl_shen_syntax kl_V2505 appl_43 kl_V2507))
                                                                                                                                                                                                              appl_44 `pseq` applyWrapper appl_2 [appl_44])))
                                                                                                                                        !appl_45 <- kl_gensym (Types.Atom (Types.UnboundSym "shen.place"))
                                                                                                                                        appl_45 `pseq` applyWrapper appl_1 [appl_45])))
                                                                         let !appl_46 = List []
                                                                         !appl_47 <- kl_V2506 `pseq` (appl_46 `pseq` klCons kl_V2506 appl_46)
                                                                         !appl_48 <- appl_47 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_47
                                                                         let !appl_49 = List []
                                                                         !appl_50 <- appl_48 `pseq` (appl_49 `pseq` klCons appl_48 appl_49)
                                                                         !appl_51 <- appl_50 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_50
                                                                         let !appl_52 = List []
                                                                         !appl_53 <- kl_V2506 `pseq` (appl_52 `pseq` klCons kl_V2506 appl_52)
                                                                         !appl_54 <- appl_53 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_53
                                                                         let !appl_55 = List []
                                                                         !appl_56 <- appl_54 `pseq` (appl_55 `pseq` klCons appl_54 appl_55)
                                                                         !appl_57 <- appl_56 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_56
                                                                         let !appl_58 = List []
                                                                         !appl_59 <- appl_57 `pseq` (appl_58 `pseq` klCons appl_57 appl_58)
                                                                         !appl_60 <- appl_59 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_59
                                                                         let !appl_61 = List []
                                                                         !appl_62 <- appl_60 `pseq` (appl_61 `pseq` klCons appl_60 appl_61)
                                                                         !appl_63 <- appl_51 `pseq` (appl_62 `pseq` klCons appl_51 appl_62)
                                                                         !appl_64 <- appl_63 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_63
                                                                         appl_64 `pseq` applyWrapper appl_0 [appl_64]

kl_shen_decons :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_decons (!kl_V2508) = do !kl_if_0 <- kl_V2508 `pseq` consP kl_V2508
                                !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2508 `pseq` hd kl_V2508
                                                             !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "cons" klCons)) appl_2
                                                             klIf kl_if_3 (do !appl_4 <- kl_V2508 `pseq` tl kl_V2508
                                                                              !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                              klIf kl_if_5 (do !appl_6 <- kl_V2508 `pseq` tl kl_V2508
                                                                                               !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                               !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                               klIf kl_if_8 (do let !appl_9 = List []
                                                                                                                !appl_10 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                !appl_12 <- appl_11 `pseq` hd appl_11
                                                                                                                !kl_if_13 <- appl_9 `pseq` (appl_12 `pseq` eq appl_9 appl_12)
                                                                                                                klIf kl_if_13 (do let !appl_14 = List []
                                                                                                                                  !appl_15 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                                  !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                  !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                                                                  appl_14 `pseq` (appl_17 `pseq` eq appl_14 appl_17)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                klIf kl_if_1 (do !appl_18 <- kl_V2508 `pseq` tl kl_V2508
                                                 !appl_19 <- appl_18 `pseq` hd appl_18
                                                 let !appl_20 = List []
                                                 appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)) (do !kl_if_21 <- kl_V2508 `pseq` consP kl_V2508
                                                                                                             !kl_if_22 <- klIf kl_if_21 (do !appl_23 <- kl_V2508 `pseq` hd kl_V2508
                                                                                                                                            !kl_if_24 <- appl_23 `pseq` eq (ApplC (wrapNamed "cons" klCons)) appl_23
                                                                                                                                            klIf kl_if_24 (do !appl_25 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                                                              !kl_if_26 <- appl_25 `pseq` consP appl_25
                                                                                                                                                              klIf kl_if_26 (do !appl_27 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                                                                                !appl_28 <- appl_27 `pseq` tl appl_27
                                                                                                                                                                                !kl_if_29 <- appl_28 `pseq` consP appl_28
                                                                                                                                                                                klIf kl_if_29 (do let !appl_30 = List []
                                                                                                                                                                                                  !appl_31 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                                                                                                  !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                                  !appl_33 <- appl_32 `pseq` tl appl_32
                                                                                                                                                                                                  appl_30 `pseq` (appl_33 `pseq` eq appl_30 appl_33)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                             klIf kl_if_22 (do !appl_34 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                               !appl_35 <- appl_34 `pseq` hd appl_34
                                                                                                                               !appl_36 <- kl_V2508 `pseq` tl kl_V2508
                                                                                                                               !appl_37 <- appl_36 `pseq` tl appl_36
                                                                                                                               !appl_38 <- appl_37 `pseq` hd appl_37
                                                                                                                               !appl_39 <- appl_38 `pseq` kl_shen_decons appl_38
                                                                                                                               appl_35 `pseq` (appl_39 `pseq` klCons appl_35 appl_39)) (do klIf (Atom (B True)) (do return kl_V2508) (do return (List []))))

kl_shen_insert_runon :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert_runon (!kl_V2520) (!kl_V2521) (!kl_V2522) = do !kl_if_0 <- kl_V2522 `pseq` consP kl_V2522
                                                              !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2522 `pseq` hd kl_V2522
                                                                                           !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_2
                                                                                           klIf kl_if_3 (do !appl_4 <- kl_V2522 `pseq` tl kl_V2522
                                                                                                            !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                            klIf kl_if_5 (do !appl_6 <- kl_V2522 `pseq` tl kl_V2522
                                                                                                                             !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                                             !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                                             klIf kl_if_8 (do let !appl_9 = List []
                                                                                                                                              !appl_10 <- kl_V2522 `pseq` tl kl_V2522
                                                                                                                                              !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                                              !appl_12 <- appl_11 `pseq` tl appl_11
                                                                                                                                              !kl_if_13 <- appl_9 `pseq` (appl_12 `pseq` eq appl_9 appl_12)
                                                                                                                                              klIf kl_if_13 (do !appl_14 <- kl_V2522 `pseq` tl kl_V2522
                                                                                                                                                                !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                                                !appl_16 <- appl_15 `pseq` hd appl_15
                                                                                                                                                                appl_16 `pseq` (kl_V2521 `pseq` eq appl_16 kl_V2521)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                              klIf kl_if_1 (do return kl_V2520) (do !kl_if_17 <- kl_V2522 `pseq` consP kl_V2522
                                                                                                    klIf kl_if_17 (do let !appl_18 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_V2520 `pseq` (kl_V2521 `pseq` (kl_Z `pseq` kl_shen_insert_runon kl_V2520 kl_V2521 kl_Z)))))
                                                                                                                      appl_18 `pseq` (kl_V2522 `pseq` kl_map appl_18 kl_V2522)) (do klIf (Atom (B True)) (do return kl_V2522) (do return (List []))))

kl_shen_strip_pathname :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_strip_pathname (!kl_V2527) = do !appl_0 <- kl_V2527 `pseq` kl_elementP (Types.Atom (Types.Str ".")) kl_V2527
                                        !kl_if_1 <- appl_0 `pseq` kl_not appl_0
                                        klIf kl_if_1 (do return kl_V2527) (do !kl_if_2 <- kl_V2527 `pseq` consP kl_V2527
                                                                              klIf kl_if_2 (do !appl_3 <- kl_V2527 `pseq` tl kl_V2527
                                                                                               appl_3 `pseq` kl_shen_strip_pathname appl_3) (do klIf (Atom (B True)) (do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                         applyWrapper aw_4 [ApplC (wrapNamed "shen.strip-pathname" kl_shen_strip_pathname)]) (do return (List []))))

kl_shen_recursive_descent :: Types.KLValue ->
                             Types.KLValue ->
                             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_recursive_descent (!kl_V2528) (!kl_V2529) (!kl_V2530) = do !kl_if_0 <- kl_V2528 `pseq` consP kl_V2528
                                                                   klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do !appl_4 <- kl_V2528 `pseq` hd kl_V2528
                                                                                                                                                                                                                                                                                   !appl_5 <- appl_4 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) appl_4
                                                                                                                                                                                                                                                                                   let !appl_6 = List []
                                                                                                                                                                                                                                                                                   !appl_7 <- appl_6 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_6
                                                                                                                                                                                                                                                                                   !appl_8 <- kl_V2528 `pseq` hd kl_V2528
                                                                                                                                                                                                                                                                                   !appl_9 <- appl_8 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) appl_8
                                                                                                                                                                                                                                                                                   let !appl_10 = List []
                                                                                                                                                                                                                                                                                   !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                                                                                                                                                                                                                                                   !appl_12 <- appl_7 `pseq` (appl_11 `pseq` klCons appl_7 appl_11)
                                                                                                                                                                                                                                                                                   !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_12
                                                                                                                                                                                                                                                                                   let !appl_14 = List []
                                                                                                                                                                                                                                                                                   !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                                                                                                                                                                                                                                                                                   !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_15
                                                                                                                                                                                                                                                                                   let !appl_17 = List []
                                                                                                                                                                                                                                                                                   !appl_18 <- kl_Else `pseq` (appl_17 `pseq` klCons kl_Else appl_17)
                                                                                                                                                                                                                                                                                   !appl_19 <- kl_Action `pseq` (appl_18 `pseq` klCons kl_Action appl_18)
                                                                                                                                                                                                                                                                                   !appl_20 <- appl_16 `pseq` (appl_19 `pseq` klCons appl_16 appl_19)
                                                                                                                                                                                                                                                                                   !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_20
                                                                                                                                                                                                                                                                                   let !appl_22 = List []
                                                                                                                                                                                                                                                                                   !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                                                                                                                                                                                                                                                                                   !appl_24 <- kl_Test `pseq` (appl_23 `pseq` klCons kl_Test appl_23)
                                                                                                                                                                                                                                                                                   !appl_25 <- appl_5 `pseq` (appl_24 `pseq` klCons appl_5 appl_24)
                                                                                                                                                                                                                                                                                   appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_25)))
                                                                                                                                                                                                                    let !appl_26 = List []
                                                                                                                                                                                                                    !appl_27 <- appl_26 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_26
                                                                                                                                                                                                                    appl_27 `pseq` applyWrapper appl_3 [appl_27])))
                                                                                                                                                   !appl_28 <- kl_V2528 `pseq` tl kl_V2528
                                                                                                                                                   !appl_29 <- kl_V2528 `pseq` hd kl_V2528
                                                                                                                                                   !appl_30 <- appl_29 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) appl_29
                                                                                                                                                   !appl_31 <- appl_28 `pseq` (appl_30 `pseq` (kl_V2530 `pseq` kl_shen_syntax appl_28 appl_30 kl_V2530))
                                                                                                                                                   appl_31 `pseq` applyWrapper appl_2 [appl_31])))
                                                                                    !appl_32 <- kl_V2528 `pseq` hd kl_V2528
                                                                                    let !appl_33 = List []
                                                                                    !appl_34 <- kl_V2529 `pseq` (appl_33 `pseq` klCons kl_V2529 appl_33)
                                                                                    !appl_35 <- appl_32 `pseq` (appl_34 `pseq` klCons appl_32 appl_34)
                                                                                    appl_35 `pseq` applyWrapper appl_1 [appl_35]) (do klIf (Atom (B True)) (do let !aw_36 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                               applyWrapper aw_36 [ApplC (wrapNamed "shen.recursive_descent" kl_shen_recursive_descent)]) (do return (List [])))

kl_shen_variable_match :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_variable_match (!kl_V2531) (!kl_V2532) (!kl_V2533) = do !kl_if_0 <- kl_V2531 `pseq` consP kl_V2531
                                                                klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do let !appl_4 = List []
                                                                                                                                                                                                                                                                                !appl_5 <- kl_Else `pseq` (appl_4 `pseq` klCons kl_Else appl_4)
                                                                                                                                                                                                                                                                                !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                                !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                                appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                                 let !appl_8 = List []
                                                                                                                                                                                                                 !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_8
                                                                                                                                                                                                                 appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                                                                                !appl_10 <- kl_V2531 `pseq` hd kl_V2531
                                                                                                                                                !appl_11 <- appl_10 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) appl_10
                                                                                                                                                let !appl_12 = List []
                                                                                                                                                !appl_13 <- kl_V2532 `pseq` (appl_12 `pseq` klCons kl_V2532 appl_12)
                                                                                                                                                !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_13
                                                                                                                                                let !appl_15 = List []
                                                                                                                                                !appl_16 <- appl_14 `pseq` (appl_15 `pseq` klCons appl_14 appl_15)
                                                                                                                                                !appl_17 <- appl_16 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_16
                                                                                                                                                !appl_18 <- kl_V2531 `pseq` tl kl_V2531
                                                                                                                                                let !appl_19 = List []
                                                                                                                                                !appl_20 <- kl_V2532 `pseq` (appl_19 `pseq` klCons kl_V2532 appl_19)
                                                                                                                                                !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_20
                                                                                                                                                let !appl_22 = List []
                                                                                                                                                !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                                                                                                                                                !appl_24 <- appl_23 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_23
                                                                                                                                                let !appl_25 = List []
                                                                                                                                                !appl_26 <- kl_V2532 `pseq` (appl_25 `pseq` klCons kl_V2532 appl_25)
                                                                                                                                                !appl_27 <- appl_26 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_26
                                                                                                                                                let !appl_28 = List []
                                                                                                                                                !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                                                                                                                !appl_30 <- appl_24 `pseq` (appl_29 `pseq` klCons appl_24 appl_29)
                                                                                                                                                !appl_31 <- appl_30 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_30
                                                                                                                                                !appl_32 <- appl_18 `pseq` (appl_31 `pseq` (kl_V2533 `pseq` kl_shen_syntax appl_18 appl_31 kl_V2533))
                                                                                                                                                let !appl_33 = List []
                                                                                                                                                !appl_34 <- appl_32 `pseq` (appl_33 `pseq` klCons appl_32 appl_33)
                                                                                                                                                !appl_35 <- appl_17 `pseq` (appl_34 `pseq` klCons appl_17 appl_34)
                                                                                                                                                !appl_36 <- appl_11 `pseq` (appl_35 `pseq` klCons appl_11 appl_35)
                                                                                                                                                !appl_37 <- appl_36 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_36
                                                                                                                                                appl_37 `pseq` applyWrapper appl_2 [appl_37])))
                                                                                 let !appl_38 = List []
                                                                                 !appl_39 <- kl_V2532 `pseq` (appl_38 `pseq` klCons kl_V2532 appl_38)
                                                                                 !appl_40 <- appl_39 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_39
                                                                                 let !appl_41 = List []
                                                                                 !appl_42 <- appl_40 `pseq` (appl_41 `pseq` klCons appl_40 appl_41)
                                                                                 !appl_43 <- appl_42 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_42
                                                                                 appl_43 `pseq` applyWrapper appl_1 [appl_43]) (do klIf (Atom (B True)) (do let !aw_44 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                            applyWrapper aw_44 [ApplC (wrapNamed "shen.variable-match" kl_shen_variable_match)]) (do return (List [])))

kl_shen_terminalP :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_terminalP (!kl_V2542) = do !kl_if_0 <- kl_V2542 `pseq` consP kl_V2542
                                   klIf kl_if_0 (do return (Atom (B False))) (do !kl_if_1 <- kl_V2542 `pseq` kl_variableP kl_V2542
                                                                                 klIf kl_if_1 (do return (Atom (B False))) (do klIf (Atom (B True)) (do return (Atom (B True))) (do return (List []))))

kl_shen_jump_streamP :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_jump_streamP (!kl_V2547) = do !kl_if_0 <- kl_V2547 `pseq` eq kl_V2547 (Types.Atom (Types.UnboundSym "_"))
                                      klIf kl_if_0 (do return (Atom (B True))) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List [])))

kl_shen_check_stream :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_check_stream (!kl_V2548) (!kl_V2549) (!kl_V2550) = do !kl_if_0 <- kl_V2548 `pseq` consP kl_V2548
                                                              klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do let !appl_4 = List []
                                                                                                                                                                                                                                                                              !appl_5 <- kl_Else `pseq` (appl_4 `pseq` klCons kl_Else appl_4)
                                                                                                                                                                                                                                                                              !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                              !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                              appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                               let !appl_8 = List []
                                                                                                                                                                                                               !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_8
                                                                                                                                                                                                               appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                                                                              !appl_10 <- kl_V2548 `pseq` tl kl_V2548
                                                                                                                                              let !appl_11 = List []
                                                                                                                                              !appl_12 <- kl_V2549 `pseq` (appl_11 `pseq` klCons kl_V2549 appl_11)
                                                                                                                                              !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_12
                                                                                                                                              let !appl_14 = List []
                                                                                                                                              !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                                                                                                                                              !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_15
                                                                                                                                              let !appl_17 = List []
                                                                                                                                              !appl_18 <- kl_V2549 `pseq` (appl_17 `pseq` klCons kl_V2549 appl_17)
                                                                                                                                              !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_18
                                                                                                                                              let !appl_20 = List []
                                                                                                                                              !appl_21 <- appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)
                                                                                                                                              !appl_22 <- appl_16 `pseq` (appl_21 `pseq` klCons appl_16 appl_21)
                                                                                                                                              !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_22
                                                                                                                                              !appl_24 <- appl_10 `pseq` (appl_23 `pseq` (kl_V2550 `pseq` kl_shen_syntax appl_10 appl_23 kl_V2550))
                                                                                                                                              appl_24 `pseq` applyWrapper appl_2 [appl_24])))
                                                                               let !appl_25 = List []
                                                                               !appl_26 <- kl_V2549 `pseq` (appl_25 `pseq` klCons kl_V2549 appl_25)
                                                                               !appl_27 <- appl_26 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_26
                                                                               let !appl_28 = List []
                                                                               !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                                               !appl_30 <- appl_29 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_29
                                                                               !appl_31 <- kl_V2548 `pseq` hd kl_V2548
                                                                               let !appl_32 = List []
                                                                               !appl_33 <- kl_V2549 `pseq` (appl_32 `pseq` klCons kl_V2549 appl_32)
                                                                               !appl_34 <- appl_33 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_33
                                                                               let !appl_35 = List []
                                                                               !appl_36 <- appl_34 `pseq` (appl_35 `pseq` klCons appl_34 appl_35)
                                                                               !appl_37 <- appl_36 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_36
                                                                               let !appl_38 = List []
                                                                               !appl_39 <- appl_37 `pseq` (appl_38 `pseq` klCons appl_37 appl_38)
                                                                               !appl_40 <- appl_31 `pseq` (appl_39 `pseq` klCons appl_31 appl_39)
                                                                               !appl_41 <- appl_40 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_40
                                                                               let !appl_42 = List []
                                                                               !appl_43 <- appl_41 `pseq` (appl_42 `pseq` klCons appl_41 appl_42)
                                                                               !appl_44 <- appl_30 `pseq` (appl_43 `pseq` klCons appl_30 appl_43)
                                                                               !appl_45 <- appl_44 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_44
                                                                               appl_45 `pseq` applyWrapper appl_1 [appl_45]) (do klIf (Atom (B True)) (do let !aw_46 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                          applyWrapper aw_46 [ApplC (wrapNamed "shen.check_stream" kl_shen_check_stream)]) (do return (List [])))

kl_shen_jump_stream :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_jump_stream (!kl_V2551) (!kl_V2552) (!kl_V2553) = do !kl_if_0 <- kl_V2551 `pseq` consP kl_V2551
                                                             klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do let !appl_4 = List []
                                                                                                                                                                                                                                                                             !appl_5 <- kl_Else `pseq` (appl_4 `pseq` klCons kl_Else appl_4)
                                                                                                                                                                                                                                                                             !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                             !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                             appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                              let !appl_8 = List []
                                                                                                                                                                                                              !appl_9 <- appl_8 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_8
                                                                                                                                                                                                              appl_9 `pseq` applyWrapper appl_3 [appl_9])))
                                                                                                                                             !appl_10 <- kl_V2551 `pseq` tl kl_V2551
                                                                                                                                             let !appl_11 = List []
                                                                                                                                             !appl_12 <- kl_V2552 `pseq` (appl_11 `pseq` klCons kl_V2552 appl_11)
                                                                                                                                             !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_12
                                                                                                                                             let !appl_14 = List []
                                                                                                                                             !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                                                                                                                                             !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_15
                                                                                                                                             let !appl_17 = List []
                                                                                                                                             !appl_18 <- kl_V2552 `pseq` (appl_17 `pseq` klCons kl_V2552 appl_17)
                                                                                                                                             !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_18
                                                                                                                                             let !appl_20 = List []
                                                                                                                                             !appl_21 <- appl_19 `pseq` (appl_20 `pseq` klCons appl_19 appl_20)
                                                                                                                                             !appl_22 <- appl_16 `pseq` (appl_21 `pseq` klCons appl_16 appl_21)
                                                                                                                                             !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_22
                                                                                                                                             !appl_24 <- appl_10 `pseq` (appl_23 `pseq` (kl_V2553 `pseq` kl_shen_syntax appl_10 appl_23 kl_V2553))
                                                                                                                                             appl_24 `pseq` applyWrapper appl_2 [appl_24])))
                                                                              let !appl_25 = List []
                                                                              !appl_26 <- kl_V2552 `pseq` (appl_25 `pseq` klCons kl_V2552 appl_25)
                                                                              !appl_27 <- appl_26 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_26
                                                                              let !appl_28 = List []
                                                                              !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                                              !appl_30 <- appl_29 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_29
                                                                              appl_30 `pseq` applyWrapper appl_1 [appl_30]) (do klIf (Atom (B True)) (do let !aw_31 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                         applyWrapper aw_31 [ApplC (wrapNamed "shen.jump_stream" kl_shen_jump_stream)]) (do return (List [])))

kl_shen_semantics :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_semantics (!kl_V2554) = do let !appl_0 = List []
                                   !kl_if_1 <- appl_0 `pseq` (kl_V2554 `pseq` eq appl_0 kl_V2554)
                                   klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V2554 `pseq` kl_shen_grammar_symbolP kl_V2554
                                                                          klIf kl_if_2 (do !appl_3 <- kl_V2554 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V2554
                                                                                           let !appl_4 = List []
                                                                                           !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                           appl_5 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_5) (do !kl_if_6 <- kl_V2554 `pseq` kl_variableP kl_V2554
                                                                                                                                                                         klIf kl_if_6 (do kl_V2554 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V2554) (do !kl_if_7 <- kl_V2554 `pseq` consP kl_V2554
                                                                                                                                                                                                                                                                           klIf kl_if_7 (do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_V2469) -> do kl_V2469 `pseq` kl_shen_semantics kl_V2469)))
                                                                                                                                                                                                                                                                                            appl_8 `pseq` (kl_V2554 `pseq` kl_map appl_8 kl_V2554)) (do klIf (Atom (B True)) (do return kl_V2554) (do return (List []))))))

kl_shen_snd_or_fail :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_snd_or_fail (!kl_V2561) = do !kl_if_0 <- kl_V2561 `pseq` consP kl_V2561
                                     !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2561 `pseq` tl kl_V2561
                                                                  !kl_if_3 <- appl_2 `pseq` consP appl_2
                                                                  klIf kl_if_3 (do let !appl_4 = List []
                                                                                   !appl_5 <- kl_V2561 `pseq` tl kl_V2561
                                                                                   !appl_6 <- appl_5 `pseq` tl appl_5
                                                                                   appl_4 `pseq` (appl_6 `pseq` eq appl_4 appl_6)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                     klIf kl_if_1 (do !appl_7 <- kl_V2561 `pseq` tl kl_V2561
                                                      appl_7 `pseq` hd appl_7) (do klIf (Atom (B True)) (do kl_fail) (do return (List [])))

kl_fail :: Types.KLContext Types.Env Types.KLValue
kl_fail = do return (Types.Atom (Types.UnboundSym "shen.fail!"))

kl_shen_pair :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_pair (!kl_V2562) (!kl_V2563) = do let !appl_0 = List []
                                          !appl_1 <- kl_V2563 `pseq` (appl_0 `pseq` klCons kl_V2563 appl_0)
                                          kl_V2562 `pseq` (appl_1 `pseq` klCons kl_V2562 appl_1)

kl_shen_hdtl :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_shen_hdtl (!kl_V2564) = do !appl_0 <- kl_V2564 `pseq` tl kl_V2564
                              appl_0 `pseq` hd appl_0

kl_shen_LBExclRB :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_LBExclRB (!kl_V2571) = do !kl_if_0 <- kl_V2571 `pseq` consP kl_V2571
                                  !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2571 `pseq` tl kl_V2571
                                                               !kl_if_3 <- appl_2 `pseq` consP appl_2
                                                               klIf kl_if_3 (do let !appl_4 = List []
                                                                                !appl_5 <- kl_V2571 `pseq` tl kl_V2571
                                                                                !appl_6 <- appl_5 `pseq` tl appl_5
                                                                                appl_4 `pseq` (appl_6 `pseq` eq appl_4 appl_6)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                  klIf kl_if_1 (do let !appl_7 = List []
                                                   !appl_8 <- kl_V2571 `pseq` hd kl_V2571
                                                   let !appl_9 = List []
                                                   !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                   appl_7 `pseq` (appl_10 `pseq` klCons appl_7 appl_10)) (do klIf (Atom (B True)) (do kl_fail) (do return (List [])))

kl_LBeRB :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_LBeRB (!kl_V2576) = do !kl_if_0 <- kl_V2576 `pseq` consP kl_V2576
                          !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2576 `pseq` tl kl_V2576
                                                       !kl_if_3 <- appl_2 `pseq` consP appl_2
                                                       klIf kl_if_3 (do let !appl_4 = List []
                                                                        !appl_5 <- kl_V2576 `pseq` tl kl_V2576
                                                                        !appl_6 <- appl_5 `pseq` tl appl_5
                                                                        appl_4 `pseq` (appl_6 `pseq` eq appl_4 appl_6)) (do return (Atom (B False)))) (do return (Atom (B False)))
                          klIf kl_if_1 (do !appl_7 <- kl_V2576 `pseq` hd kl_V2576
                                           let !appl_8 = List []
                                           let !appl_9 = List []
                                           !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                           appl_7 `pseq` (appl_10 `pseq` klCons appl_7 appl_10)) (do klIf (Atom (B True)) (do let !aw_11 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                              applyWrapper aw_11 [ApplC (wrapNamed "<e>" kl_LBeRB)]) (do return (List [])))

expr4 :: Types.KLContext Types.Env Types.KLValue
expr4 = do (return $ List [])
