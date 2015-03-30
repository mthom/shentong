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

module Shentong.Backend.Toplevel where

import Control.Monad.Except
import Control.Parallel
import Shentong.Environment
import Shentong.Primitives as Primitives
import Shentong.Backend.Utils
import Shentong.Types as Types
import Shentong.Utils
import Shentong.Wrap

kl_shen_shen :: Types.KLContext Types.Env Types.KLValue
kl_shen_shen = do !appl_0 <- kl_shen_credits
                  !appl_1 <- kl_shen_loop
                  let !aw_2 = Types.Atom (Types.UnboundSym "do")
                  appl_0 `pseq` (appl_1 `pseq` applyWrapper aw_2 [appl_0, appl_1])

kl_shen_loop :: Types.KLContext Types.Env Types.KLValue
kl_shen_loop = do !appl_0 <- kl_shen_initialise_environment
                  !appl_1 <- kl_shen_prompt
                  !appl_2 <- (do kl_shen_read_evaluate_print) `catchError` (\(!kl_E) -> do !appl_3 <- kl_E `pseq` errorToString (Excep kl_E)
                                                                                           let !aw_4 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                           !appl_5 <- applyWrapper aw_4 []
                                                                                           let !aw_6 = Types.Atom (Types.UnboundSym "pr")
                                                                                           appl_3 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_3,
                                                                                                                                           appl_5]))
                  !appl_7 <- kl_shen_loop
                  let !aw_8 = Types.Atom (Types.UnboundSym "do")
                  !appl_9 <- appl_2 `pseq` (appl_7 `pseq` applyWrapper aw_8 [appl_2,
                                                                             appl_7])
                  let !aw_10 = Types.Atom (Types.UnboundSym "do")
                  !appl_11 <- appl_1 `pseq` (appl_9 `pseq` applyWrapper aw_10 [appl_1,
                                                                               appl_9])
                  let !aw_12 = Types.Atom (Types.UnboundSym "do")
                  appl_0 `pseq` (appl_11 `pseq` applyWrapper aw_12 [appl_0, appl_11])

kl_shen_credits :: Types.KLContext Types.Env Types.KLValue
kl_shen_credits = do let !aw_0 = Types.Atom (Types.UnboundSym "stoutput")
                     !appl_1 <- applyWrapper aw_0 []
                     let !aw_2 = Types.Atom (Types.UnboundSym "shen.prhush")
                     !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [Types.Atom (Types.Str "\nShen, copyright (C) 2010-2015 Mark Tarver\n"),
                                                                 appl_1]
                     !appl_4 <- value (Types.Atom (Types.UnboundSym "*version*"))
                     let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                     !appl_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4,
                                                                 Types.Atom (Types.Str "\n"),
                                                                 Types.Atom (Types.UnboundSym "shen.a")]
                     !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str "www.shenlanguage.org, ")) appl_6
                     let !aw_8 = Types.Atom (Types.UnboundSym "stoutput")
                     !appl_9 <- applyWrapper aw_8 []
                     let !aw_10 = Types.Atom (Types.UnboundSym "shen.prhush")
                     !appl_11 <- appl_7 `pseq` (appl_9 `pseq` applyWrapper aw_10 [appl_7,
                                                                                  appl_9])
                     !appl_12 <- value (Types.Atom (Types.UnboundSym "*language*"))
                     !appl_13 <- value (Types.Atom (Types.UnboundSym "*implementation*"))
                     let !aw_14 = Types.Atom (Types.UnboundSym "shen.app")
                     !appl_15 <- appl_13 `pseq` applyWrapper aw_14 [appl_13,
                                                                    Types.Atom (Types.Str ""),
                                                                    Types.Atom (Types.UnboundSym "shen.a")]
                     !appl_16 <- appl_15 `pseq` cn (Types.Atom (Types.Str ", implementation: ")) appl_15
                     let !aw_17 = Types.Atom (Types.UnboundSym "shen.app")
                     !appl_18 <- appl_12 `pseq` (appl_16 `pseq` applyWrapper aw_17 [appl_12,
                                                                                    appl_16,
                                                                                    Types.Atom (Types.UnboundSym "shen.a")])
                     !appl_19 <- appl_18 `pseq` cn (Types.Atom (Types.Str "running under ")) appl_18
                     let !aw_20 = Types.Atom (Types.UnboundSym "stoutput")
                     !appl_21 <- applyWrapper aw_20 []
                     let !aw_22 = Types.Atom (Types.UnboundSym "shen.prhush")
                     !appl_23 <- appl_19 `pseq` (appl_21 `pseq` applyWrapper aw_22 [appl_19,
                                                                                    appl_21])
                     !appl_24 <- value (Types.Atom (Types.UnboundSym "*port*"))
                     !appl_25 <- value (Types.Atom (Types.UnboundSym "*porters*"))
                     let !aw_26 = Types.Atom (Types.UnboundSym "shen.app")
                     !appl_27 <- appl_25 `pseq` applyWrapper aw_26 [appl_25,
                                                                    Types.Atom (Types.Str "\n"),
                                                                    Types.Atom (Types.UnboundSym "shen.a")]
                     !appl_28 <- appl_27 `pseq` cn (Types.Atom (Types.Str " ported by ")) appl_27
                     let !aw_29 = Types.Atom (Types.UnboundSym "shen.app")
                     !appl_30 <- appl_24 `pseq` (appl_28 `pseq` applyWrapper aw_29 [appl_24,
                                                                                    appl_28,
                                                                                    Types.Atom (Types.UnboundSym "shen.a")])
                     !appl_31 <- appl_30 `pseq` cn (Types.Atom (Types.Str "\nport ")) appl_30
                     let !aw_32 = Types.Atom (Types.UnboundSym "stoutput")
                     !appl_33 <- applyWrapper aw_32 []
                     let !aw_34 = Types.Atom (Types.UnboundSym "shen.prhush")
                     !appl_35 <- appl_31 `pseq` (appl_33 `pseq` applyWrapper aw_34 [appl_31,
                                                                                    appl_33])
                     let !aw_36 = Types.Atom (Types.UnboundSym "do")
                     !appl_37 <- appl_23 `pseq` (appl_35 `pseq` applyWrapper aw_36 [appl_23,
                                                                                    appl_35])
                     let !aw_38 = Types.Atom (Types.UnboundSym "do")
                     !appl_39 <- appl_11 `pseq` (appl_37 `pseq` applyWrapper aw_38 [appl_11,
                                                                                    appl_37])
                     let !aw_40 = Types.Atom (Types.UnboundSym "do")
                     appl_3 `pseq` (appl_39 `pseq` applyWrapper aw_40 [appl_3, appl_39])

kl_shen_initialise_environment :: Types.KLContext Types.Env
                                                  Types.KLValue
kl_shen_initialise_environment = do let !appl_0 = List []
                                    !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_0
                                    !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*catch*")) appl_1
                                    !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_2
                                    !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*process-counter*")) appl_3
                                    !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_4
                                    !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*infs*")) appl_5
                                    !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_6
                                    !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_7
                                    appl_8 `pseq` kl_shen_multiple_set appl_8

kl_shen_multiple_set :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_multiple_set (!kl_V2248) = do let !appl_0 = List []
                                      !kl_if_1 <- appl_0 `pseq` (kl_V2248 `pseq` eq appl_0 kl_V2248)
                                      klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V2248 `pseq` consP kl_V2248
                                                                             !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V2248 `pseq` tl kl_V2248
                                                                                                          appl_4 `pseq` consP appl_4) (do return (Atom (B False)))
                                                                             klIf kl_if_3 (do !appl_5 <- kl_V2248 `pseq` hd kl_V2248
                                                                                              !appl_6 <- kl_V2248 `pseq` tl kl_V2248
                                                                                              !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                              !appl_8 <- appl_5 `pseq` (appl_7 `pseq` klSet appl_5 appl_7)
                                                                                              !appl_9 <- kl_V2248 `pseq` tl kl_V2248
                                                                                              !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                              !appl_11 <- appl_10 `pseq` kl_shen_multiple_set appl_10
                                                                                              let !aw_12 = Types.Atom (Types.UnboundSym "do")
                                                                                              appl_8 `pseq` (appl_11 `pseq` applyWrapper aw_12 [appl_8,
                                                                                                                                                appl_11])) (do klIf (Atom (B True)) (do let !aw_13 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                        applyWrapper aw_13 [ApplC (wrapNamed "shen.multiple-set" kl_shen_multiple_set)]) (do return (List []))))

kl_destroy :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_destroy (!kl_V2249) = do let !aw_0 = Types.Atom (Types.UnboundSym "declare")
                            kl_V2249 `pseq` applyWrapper aw_0 [kl_V2249,
                                                               Types.Atom (Types.UnboundSym "symbol")]

kl_shen_read_evaluate_print :: Types.KLContext Types.Env
                                               Types.KLValue
kl_shen_read_evaluate_print = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Lineread) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_History) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_NewLineread) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_NewHistory) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parsed) -> do kl_Parsed `pseq` kl_shen_toplevel kl_Parsed)))
                                                                                                                                                                                                                                                                                                                 let !aw_5 = Types.Atom (Types.UnboundSym "fst")
                                                                                                                                                                                                                                                                                                                 !appl_6 <- kl_NewLineread `pseq` applyWrapper aw_5 [kl_NewLineread]
                                                                                                                                                                                                                                                                                                                 appl_6 `pseq` applyWrapper appl_4 [appl_6])))
                                                                                                                                                                                                                                            !appl_7 <- kl_NewLineread `pseq` (kl_History `pseq` kl_shen_update_history kl_NewLineread kl_History)
                                                                                                                                                                                                                                            appl_7 `pseq` applyWrapper appl_3 [appl_7])))
                                                                                                                                                                      !appl_8 <- kl_Lineread `pseq` (kl_History `pseq` kl_shen_retrieve_from_history_if_needed kl_Lineread kl_History)
                                                                                                                                                                      appl_8 `pseq` applyWrapper appl_2 [appl_8])))
                                                                                                    !appl_9 <- value (Types.Atom (Types.UnboundSym "shen.*history*"))
                                                                                                    appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                                 !appl_10 <- kl_shen_toplineread
                                 appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_retrieve_from_history_if_needed :: Types.KLValue ->
                                           Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_retrieve_from_history_if_needed (!kl_V2259) (!kl_V2260) = do let !aw_0 = Types.Atom (Types.UnboundSym "tuple?")
                                                                     !kl_if_1 <- kl_V2259 `pseq` applyWrapper aw_0 [kl_V2259]
                                                                     !kl_if_2 <- klIf kl_if_1 (do let !aw_3 = Types.Atom (Types.UnboundSym "snd")
                                                                                                  !appl_4 <- kl_V2259 `pseq` applyWrapper aw_3 [kl_V2259]
                                                                                                  !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                  klIf kl_if_5 (do let !aw_6 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                   !appl_7 <- kl_V2259 `pseq` applyWrapper aw_6 [kl_V2259]
                                                                                                                   !appl_8 <- appl_7 `pseq` hd appl_7
                                                                                                                   !appl_9 <- kl_shen_space
                                                                                                                   !appl_10 <- kl_shen_newline
                                                                                                                   let !appl_11 = List []
                                                                                                                   !appl_12 <- appl_10 `pseq` (appl_11 `pseq` klCons appl_10 appl_11)
                                                                                                                   !appl_13 <- appl_9 `pseq` (appl_12 `pseq` klCons appl_9 appl_12)
                                                                                                                   let !aw_14 = Types.Atom (Types.UnboundSym "element?")
                                                                                                                   appl_8 `pseq` (appl_13 `pseq` applyWrapper aw_14 [appl_8,
                                                                                                                                                                     appl_13])) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                     klIf kl_if_2 (do let !aw_15 = Types.Atom (Types.UnboundSym "fst")
                                                                                      !appl_16 <- kl_V2259 `pseq` applyWrapper aw_15 [kl_V2259]
                                                                                      let !aw_17 = Types.Atom (Types.UnboundSym "snd")
                                                                                      !appl_18 <- kl_V2259 `pseq` applyWrapper aw_17 [kl_V2259]
                                                                                      !appl_19 <- appl_18 `pseq` tl appl_18
                                                                                      let !aw_20 = Types.Atom (Types.UnboundSym "@p")
                                                                                      !appl_21 <- appl_16 `pseq` (appl_19 `pseq` applyWrapper aw_20 [appl_16,
                                                                                                                                                     appl_19])
                                                                                      appl_21 `pseq` (kl_V2260 `pseq` kl_shen_retrieve_from_history_if_needed appl_21 kl_V2260)) (do let !aw_22 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                     !kl_if_23 <- kl_V2259 `pseq` applyWrapper aw_22 [kl_V2259]
                                                                                                                                                                                     !kl_if_24 <- klIf kl_if_23 (do let !aw_25 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                    !appl_26 <- kl_V2259 `pseq` applyWrapper aw_25 [kl_V2259]
                                                                                                                                                                                                                    !kl_if_27 <- appl_26 `pseq` consP appl_26
                                                                                                                                                                                                                    klIf kl_if_27 (do let !aw_28 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                      !appl_29 <- kl_V2259 `pseq` applyWrapper aw_28 [kl_V2259]
                                                                                                                                                                                                                                      !appl_30 <- appl_29 `pseq` tl appl_29
                                                                                                                                                                                                                                      !kl_if_31 <- appl_30 `pseq` consP appl_30
                                                                                                                                                                                                                                      klIf kl_if_31 (do let !appl_32 = List []
                                                                                                                                                                                                                                                        let !aw_33 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                        !appl_34 <- kl_V2259 `pseq` applyWrapper aw_33 [kl_V2259]
                                                                                                                                                                                                                                                        !appl_35 <- appl_34 `pseq` tl appl_34
                                                                                                                                                                                                                                                        !appl_36 <- appl_35 `pseq` tl appl_35
                                                                                                                                                                                                                                                        !kl_if_37 <- appl_32 `pseq` (appl_36 `pseq` eq appl_32 appl_36)
                                                                                                                                                                                                                                                        klIf kl_if_37 (do !kl_if_38 <- kl_V2260 `pseq` consP kl_V2260
                                                                                                                                                                                                                                                                          klIf kl_if_38 (do let !aw_39 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                            !appl_40 <- kl_V2259 `pseq` applyWrapper aw_39 [kl_V2259]
                                                                                                                                                                                                                                                                                            !appl_41 <- appl_40 `pseq` hd appl_40
                                                                                                                                                                                                                                                                                            !appl_42 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                            !kl_if_43 <- appl_41 `pseq` (appl_42 `pseq` eq appl_41 appl_42)
                                                                                                                                                                                                                                                                                            klIf kl_if_43 (do let !aw_44 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                              !appl_45 <- kl_V2259 `pseq` applyWrapper aw_44 [kl_V2259]
                                                                                                                                                                                                                                                                                                              !appl_46 <- appl_45 `pseq` tl appl_45
                                                                                                                                                                                                                                                                                                              !appl_47 <- appl_46 `pseq` hd appl_46
                                                                                                                                                                                                                                                                                                              !appl_48 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                                              appl_47 `pseq` (appl_48 `pseq` eq appl_47 appl_48)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                     klIf kl_if_24 (do let !appl_49 = ApplC (Func "lambda" (Context (\(!kl_PastPrint) -> do kl_V2260 `pseq` hd kl_V2260)))
                                                                                                                                                                                                       !appl_50 <- kl_V2260 `pseq` hd kl_V2260
                                                                                                                                                                                                       let !aw_51 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                       !appl_52 <- appl_50 `pseq` applyWrapper aw_51 [appl_50]
                                                                                                                                                                                                       !appl_53 <- appl_52 `pseq` kl_shen_prbytes appl_52
                                                                                                                                                                                                       appl_53 `pseq` applyWrapper appl_49 [appl_53]) (do let !aw_54 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                                                                                          !kl_if_55 <- kl_V2259 `pseq` applyWrapper aw_54 [kl_V2259]
                                                                                                                                                                                                                                                          !kl_if_56 <- klIf kl_if_55 (do let !aw_57 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                         !appl_58 <- kl_V2259 `pseq` applyWrapper aw_57 [kl_V2259]
                                                                                                                                                                                                                                                                                         !kl_if_59 <- appl_58 `pseq` consP appl_58
                                                                                                                                                                                                                                                                                         klIf kl_if_59 (do let !aw_60 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                           !appl_61 <- kl_V2259 `pseq` applyWrapper aw_60 [kl_V2259]
                                                                                                                                                                                                                                                                                                           !appl_62 <- appl_61 `pseq` hd appl_61
                                                                                                                                                                                                                                                                                                           !appl_63 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                                           appl_62 `pseq` (appl_63 `pseq` eq appl_62 appl_63)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                          klIf kl_if_56 (do let !appl_64 = ApplC (Func "lambda" (Context (\(!kl_KeyP) -> do let !appl_65 = ApplC (Func "lambda" (Context (\(!kl_Find) -> do let !appl_66 = ApplC (Func "lambda" (Context (\(!kl_PastPrint) -> do return kl_Find)))
                                                                                                                                                                                                                                                                                                                                                                                                            let !aw_67 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                                                            !appl_68 <- kl_Find `pseq` applyWrapper aw_67 [kl_Find]
                                                                                                                                                                                                                                                                                                                                                                                                            !appl_69 <- appl_68 `pseq` kl_shen_prbytes appl_68
                                                                                                                                                                                                                                                                                                                                                                                                            appl_69 `pseq` applyWrapper appl_66 [appl_69])))
                                                                                                                                                                                                                                                                                                                                            !appl_70 <- kl_KeyP `pseq` (kl_V2260 `pseq` kl_shen_find_past_inputs kl_KeyP kl_V2260)
                                                                                                                                                                                                                                                                                                                                            let !aw_71 = Types.Atom (Types.UnboundSym "head")
                                                                                                                                                                                                                                                                                                                                            !appl_72 <- appl_70 `pseq` applyWrapper aw_71 [appl_70]
                                                                                                                                                                                                                                                                                                                                            appl_72 `pseq` applyWrapper appl_65 [appl_72])))
                                                                                                                                                                                                                                                                            let !aw_73 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                            !appl_74 <- kl_V2259 `pseq` applyWrapper aw_73 [kl_V2259]
                                                                                                                                                                                                                                                                            !appl_75 <- appl_74 `pseq` tl appl_74
                                                                                                                                                                                                                                                                            !appl_76 <- appl_75 `pseq` (kl_V2260 `pseq` kl_shen_make_key appl_75 kl_V2260)
                                                                                                                                                                                                                                                                            appl_76 `pseq` applyWrapper appl_64 [appl_76]) (do let !aw_77 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                                                                                                                                                               !kl_if_78 <- kl_V2259 `pseq` applyWrapper aw_77 [kl_V2259]
                                                                                                                                                                                                                                                                                                                               !kl_if_79 <- klIf kl_if_78 (do let !aw_80 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                              !appl_81 <- kl_V2259 `pseq` applyWrapper aw_80 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                              !kl_if_82 <- appl_81 `pseq` consP appl_81
                                                                                                                                                                                                                                                                                                                                                              klIf kl_if_82 (do let !appl_83 = List []
                                                                                                                                                                                                                                                                                                                                                                                let !aw_84 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                                !appl_85 <- kl_V2259 `pseq` applyWrapper aw_84 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                                                !appl_86 <- appl_85 `pseq` tl appl_85
                                                                                                                                                                                                                                                                                                                                                                                !kl_if_87 <- appl_83 `pseq` (appl_86 `pseq` eq appl_83 appl_86)
                                                                                                                                                                                                                                                                                                                                                                                klIf kl_if_87 (do let !aw_88 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                                                  !appl_89 <- kl_V2259 `pseq` applyWrapper aw_88 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                                                                  !appl_90 <- appl_89 `pseq` hd appl_89
                                                                                                                                                                                                                                                                                                                                                                                                  !appl_91 <- kl_shen_percent
                                                                                                                                                                                                                                                                                                                                                                                                  appl_90 `pseq` (appl_91 `pseq` eq appl_90 appl_91)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                                                                               klIf kl_if_79 (do let !appl_92 = ApplC (Func "lambda" (Context (\(!kl_X) -> do return (Atom (B True)))))
                                                                                                                                                                                                                                                                                                                                                 let !aw_93 = Types.Atom (Types.UnboundSym "reverse")
                                                                                                                                                                                                                                                                                                                                                 !appl_94 <- kl_V2260 `pseq` applyWrapper aw_93 [kl_V2260]
                                                                                                                                                                                                                                                                                                                                                 !appl_95 <- appl_92 `pseq` (appl_94 `pseq` kl_shen_print_past_inputs appl_92 appl_94 (Types.Atom (Types.N (Types.KI 0))))
                                                                                                                                                                                                                                                                                                                                                 let !aw_96 = Types.Atom (Types.UnboundSym "abort")
                                                                                                                                                                                                                                                                                                                                                 !appl_97 <- applyWrapper aw_96 []
                                                                                                                                                                                                                                                                                                                                                 let !aw_98 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                                                                                                                                                                                                                 appl_95 `pseq` (appl_97 `pseq` applyWrapper aw_98 [appl_95,
                                                                                                                                                                                                                                                                                                                                                                                                    appl_97])) (do let !aw_99 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                                                                                                                                                                                                                                                   !kl_if_100 <- kl_V2259 `pseq` applyWrapper aw_99 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                                                                                   !kl_if_101 <- klIf kl_if_100 (do let !aw_102 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                                                                                                    !appl_103 <- kl_V2259 `pseq` applyWrapper aw_102 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                                                                                                                    !kl_if_104 <- appl_103 `pseq` consP appl_103
                                                                                                                                                                                                                                                                                                                                                                                                                                                    klIf kl_if_104 (do let !aw_105 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       !appl_106 <- kl_V2259 `pseq` applyWrapper aw_105 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       !appl_107 <- appl_106 `pseq` hd appl_106
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       !appl_108 <- kl_shen_percent
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       appl_107 `pseq` (appl_108 `pseq` eq appl_107 appl_108)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                                                                                                                                                                   klIf kl_if_101 (do let !appl_109 = ApplC (Func "lambda" (Context (\(!kl_KeyP) -> do let !appl_110 = ApplC (Func "lambda" (Context (\(!kl_Pastprint) -> do let !aw_111 = Types.Atom (Types.UnboundSym "abort")
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             applyWrapper aw_111 [])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       let !aw_112 = Types.Atom (Types.UnboundSym "reverse")
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       !appl_113 <- kl_V2260 `pseq` applyWrapper aw_112 [kl_V2260]
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       !appl_114 <- kl_KeyP `pseq` (appl_113 `pseq` kl_shen_print_past_inputs kl_KeyP appl_113 (Types.Atom (Types.N (Types.KI 0))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       appl_114 `pseq` applyWrapper appl_110 [appl_114])))
                                                                                                                                                                                                                                                                                                                                                                                                                                      let !aw_115 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                                                                                      !appl_116 <- kl_V2259 `pseq` applyWrapper aw_115 [kl_V2259]
                                                                                                                                                                                                                                                                                                                                                                                                                                      !appl_117 <- appl_116 `pseq` tl appl_116
                                                                                                                                                                                                                                                                                                                                                                                                                                      !appl_118 <- appl_117 `pseq` (kl_V2260 `pseq` kl_shen_make_key appl_117 kl_V2260)
                                                                                                                                                                                                                                                                                                                                                                                                                                      appl_118 `pseq` applyWrapper appl_109 [appl_118]) (do klIf (Atom (B True)) (do return kl_V2259) (do return (List [])))))))

kl_shen_percent :: Types.KLContext Types.Env Types.KLValue
kl_shen_percent = do return (Types.Atom (Types.N (Types.KI 37)))

kl_shen_exclamation :: Types.KLContext Types.Env Types.KLValue
kl_shen_exclamation = do return (Types.Atom (Types.N (Types.KI 33)))

kl_shen_prbytes :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_prbytes (!kl_V2261) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Byte) -> do !appl_1 <- kl_Byte `pseq` nToString kl_Byte
                                                                                                let !aw_2 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                !appl_3 <- applyWrapper aw_2 []
                                                                                                let !aw_4 = Types.Atom (Types.UnboundSym "pr")
                                                                                                appl_1 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_1,
                                                                                                                                                appl_3]))))
                                 let !aw_5 = Types.Atom (Types.UnboundSym "map")
                                 !appl_6 <- appl_0 `pseq` (kl_V2261 `pseq` applyWrapper aw_5 [appl_0,
                                                                                              kl_V2261])
                                 let !aw_7 = Types.Atom (Types.UnboundSym "nl")
                                 !appl_8 <- applyWrapper aw_7 [Types.Atom (Types.N (Types.KI 1))]
                                 let !aw_9 = Types.Atom (Types.UnboundSym "do")
                                 appl_6 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_6, appl_8])

kl_shen_update_history :: Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_update_history (!kl_V2262) (!kl_V2263) = do !appl_0 <- kl_V2262 `pseq` (kl_V2263 `pseq` klCons kl_V2262 kl_V2263)
                                                    appl_0 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*history*")) appl_0

kl_shen_toplineread :: Types.KLContext Types.Env Types.KLValue
kl_shen_toplineread = do let !aw_0 = Types.Atom (Types.UnboundSym "stinput")
                         !appl_1 <- applyWrapper aw_0 []
                         !appl_2 <- appl_1 `pseq` readByte appl_1
                         let !appl_3 = List []
                         appl_2 `pseq` (appl_3 `pseq` kl_shen_toplineread_loop appl_2 appl_3)

kl_shen_toplineread_loop :: Types.KLValue ->
                            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_toplineread_loop (!kl_V2265) (!kl_V2266) = do !appl_0 <- kl_shen_hat
                                                      !kl_if_1 <- kl_V2265 `pseq` (appl_0 `pseq` eq kl_V2265 appl_0)
                                                      klIf kl_if_1 (do simpleError (Types.Atom (Types.Str "line read aborted"))) (do !appl_2 <- kl_shen_newline
                                                                                                                                     !appl_3 <- kl_shen_carriage_return
                                                                                                                                     let !appl_4 = List []
                                                                                                                                     !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                                                                                                     !appl_6 <- appl_2 `pseq` (appl_5 `pseq` klCons appl_2 appl_5)
                                                                                                                                     let !aw_7 = Types.Atom (Types.UnboundSym "element?")
                                                                                                                                     !kl_if_8 <- kl_V2265 `pseq` (appl_6 `pseq` applyWrapper aw_7 [kl_V2265,
                                                                                                                                                                                                   appl_6])
                                                                                                                                     klIf kl_if_8 (do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Line) -> do let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_It) -> do !kl_if_11 <- kl_Line `pseq` eq kl_Line (Types.Atom (Types.UnboundSym "shen.nextline"))
                                                                                                                                                                                                                                                                                   !kl_if_12 <- klIf kl_if_11 (do return (Atom (B True))) (do let !aw_13 = Types.Atom (Types.UnboundSym "empty?")
                                                                                                                                                                                                                                                                                                                                              kl_Line `pseq` applyWrapper aw_13 [kl_Line])
                                                                                                                                                                                                                                                                                   klIf kl_if_12 (do let !aw_14 = Types.Atom (Types.UnboundSym "stinput")
                                                                                                                                                                                                                                                                                                     !appl_15 <- applyWrapper aw_14 []
                                                                                                                                                                                                                                                                                                     !appl_16 <- appl_15 `pseq` readByte appl_15
                                                                                                                                                                                                                                                                                                     let !appl_17 = List []
                                                                                                                                                                                                                                                                                                     !appl_18 <- kl_V2265 `pseq` (appl_17 `pseq` klCons kl_V2265 appl_17)
                                                                                                                                                                                                                                                                                                     let !aw_19 = Types.Atom (Types.UnboundSym "append")
                                                                                                                                                                                                                                                                                                     !appl_20 <- kl_V2266 `pseq` (appl_18 `pseq` applyWrapper aw_19 [kl_V2266,
                                                                                                                                                                                                                                                                                                                                                                     appl_18])
                                                                                                                                                                                                                                                                                                     appl_16 `pseq` (appl_20 `pseq` kl_shen_toplineread_loop appl_16 appl_20)) (do let !aw_21 = Types.Atom (Types.UnboundSym "@p")
                                                                                                                                                                                                                                                                                                                                                                                   kl_Line `pseq` (kl_V2266 `pseq` applyWrapper aw_21 [kl_Line,
                                                                                                                                                                                                                                                                                                                                                                                                                                       kl_V2266])))))
                                                                                                                                                                                                                     let !aw_22 = Types.Atom (Types.UnboundSym "shen.record-it")
                                                                                                                                                                                                                     !appl_23 <- kl_V2266 `pseq` applyWrapper aw_22 [kl_V2266]
                                                                                                                                                                                                                     appl_23 `pseq` applyWrapper appl_10 [appl_23])))
                                                                                                                                                      let !appl_24 = ApplC (Func "lambda" (Context (\(!kl_V2246) -> do let !aw_25 = Types.Atom (Types.UnboundSym "shen.<st_input>")
                                                                                                                                                                                                                       kl_V2246 `pseq` applyWrapper aw_25 [kl_V2246])))
                                                                                                                                                      let !appl_26 = ApplC (Func "lambda" (Context (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.nextline")))))
                                                                                                                                                      let !aw_27 = Types.Atom (Types.UnboundSym "compile")
                                                                                                                                                      !appl_28 <- appl_24 `pseq` (kl_V2266 `pseq` (appl_26 `pseq` applyWrapper aw_27 [appl_24,
                                                                                                                                                                                                                                      kl_V2266,
                                                                                                                                                                                                                                      appl_26]))
                                                                                                                                                      appl_28 `pseq` applyWrapper appl_9 [appl_28]) (do klIf (Atom (B True)) (do let !aw_29 = Types.Atom (Types.UnboundSym "stinput")
                                                                                                                                                                                                                                 !appl_30 <- applyWrapper aw_29 []
                                                                                                                                                                                                                                 !appl_31 <- appl_30 `pseq` readByte appl_30
                                                                                                                                                                                                                                 let !appl_32 = List []
                                                                                                                                                                                                                                 !appl_33 <- kl_V2265 `pseq` (appl_32 `pseq` klCons kl_V2265 appl_32)
                                                                                                                                                                                                                                 let !aw_34 = Types.Atom (Types.UnboundSym "append")
                                                                                                                                                                                                                                 !appl_35 <- kl_V2266 `pseq` (appl_33 `pseq` applyWrapper aw_34 [kl_V2266,
                                                                                                                                                                                                                                                                                                 appl_33])
                                                                                                                                                                                                                                 appl_31 `pseq` (appl_35 `pseq` kl_shen_toplineread_loop appl_31 appl_35)) (do return (List []))))

kl_shen_hat :: Types.KLContext Types.Env Types.KLValue
kl_shen_hat = do return (Types.Atom (Types.N (Types.KI 94)))

kl_shen_newline :: Types.KLContext Types.Env Types.KLValue
kl_shen_newline = do return (Types.Atom (Types.N (Types.KI 10)))

kl_shen_carriage_return :: Types.KLContext Types.Env Types.KLValue
kl_shen_carriage_return = do return (Types.Atom (Types.N (Types.KI 13)))

kl_tc :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_tc (!kl_V2271) = do !kl_if_0 <- kl_V2271 `pseq` eq (ApplC (wrapNamed "+" add)) kl_V2271
                       klIf kl_if_0 (do klSet (Types.Atom (Types.UnboundSym "shen.*tc*")) (Atom (B True))) (do !kl_if_1 <- kl_V2271 `pseq` eq (ApplC (wrapNamed "-" Primitives.subtract)) kl_V2271
                                                                                                               klIf kl_if_1 (do klSet (Types.Atom (Types.UnboundSym "shen.*tc*")) (Atom (B False))) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "tc expects a + or -"))) (do return (List []))))

kl_shen_prompt :: Types.KLContext Types.Env Types.KLValue
kl_shen_prompt = do !kl_if_0 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                    klIf kl_if_0 (do !appl_1 <- value (Types.Atom (Types.UnboundSym "shen.*history*"))
                                     let !aw_2 = Types.Atom (Types.UnboundSym "length")
                                     !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [appl_1]
                                     let !aw_4 = Types.Atom (Types.UnboundSym "shen.app")
                                     !appl_5 <- appl_3 `pseq` applyWrapper aw_4 [appl_3,
                                                                                 Types.Atom (Types.Str "+) "),
                                                                                 Types.Atom (Types.UnboundSym "shen.a")]
                                     !appl_6 <- appl_5 `pseq` cn (Types.Atom (Types.Str "\n\n(")) appl_5
                                     let !aw_7 = Types.Atom (Types.UnboundSym "stoutput")
                                     !appl_8 <- applyWrapper aw_7 []
                                     let !aw_9 = Types.Atom (Types.UnboundSym "shen.prhush")
                                     appl_6 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_6,
                                                                                     appl_8])) (do !appl_10 <- value (Types.Atom (Types.UnboundSym "shen.*history*"))
                                                                                                   let !aw_11 = Types.Atom (Types.UnboundSym "length")
                                                                                                   !appl_12 <- appl_10 `pseq` applyWrapper aw_11 [appl_10]
                                                                                                   let !aw_13 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                   !appl_14 <- appl_12 `pseq` applyWrapper aw_13 [appl_12,
                                                                                                                                                  Types.Atom (Types.Str "-) "),
                                                                                                                                                  Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                   !appl_15 <- appl_14 `pseq` cn (Types.Atom (Types.Str "\n\n(")) appl_14
                                                                                                   let !aw_16 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                   !appl_17 <- applyWrapper aw_16 []
                                                                                                   let !aw_18 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                   appl_15 `pseq` (appl_17 `pseq` applyWrapper aw_18 [appl_15,
                                                                                                                                                      appl_17]))

kl_shen_toplevel :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_toplevel (!kl_V2272) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                                  kl_V2272 `pseq` (appl_0 `pseq` kl_shen_toplevel_evaluate kl_V2272 appl_0)

kl_shen_find_past_inputs :: Types.KLValue ->
                            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_find_past_inputs (!kl_V2273) (!kl_V2274) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_F) -> do let !aw_1 = Types.Atom (Types.UnboundSym "empty?")
                                                                                                                  !kl_if_2 <- kl_F `pseq` applyWrapper aw_1 [kl_F]
                                                                                                                  klIf kl_if_2 (do simpleError (Types.Atom (Types.Str "input not found\n"))) (do return kl_F))))
                                                      !appl_3 <- kl_V2273 `pseq` (kl_V2274 `pseq` kl_shen_find kl_V2273 kl_V2274)
                                                      appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_make_key :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_make_key (!kl_V2275) (!kl_V2276) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Atom) -> do let !aw_1 = Types.Atom (Types.UnboundSym "integer?")
                                                                                                             !kl_if_2 <- kl_Atom `pseq` applyWrapper aw_1 [kl_Atom]
                                                                                                             klIf kl_if_2 (do return (ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_3 <- kl_Atom `pseq` add kl_Atom (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                    let !aw_4 = Types.Atom (Types.UnboundSym "reverse")
                                                                                                                                                                                    !appl_5 <- kl_V2276 `pseq` applyWrapper aw_4 [kl_V2276]
                                                                                                                                                                                    let !aw_6 = Types.Atom (Types.UnboundSym "nth")
                                                                                                                                                                                    !appl_7 <- appl_3 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_3,
                                                                                                                                                                                                                                               appl_5])
                                                                                                                                                                                    kl_X `pseq` (appl_7 `pseq` eq kl_X appl_7)))))) (do return (ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_8 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                              !appl_9 <- kl_X `pseq` applyWrapper aw_8 [kl_X]
                                                                                                                                                                                                                                                                                              !appl_10 <- appl_9 `pseq` kl_shen_trim_gubbins appl_9
                                                                                                                                                                                                                                                                                              kl_V2275 `pseq` (appl_10 `pseq` kl_shen_prefixP kl_V2275 appl_10)))))))))
                                              let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_V2247) -> do let !aw_12 = Types.Atom (Types.UnboundSym "shen.<st_input>")
                                                                                                               kl_V2247 `pseq` applyWrapper aw_12 [kl_V2247])))
                                              let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_E) -> do !kl_if_14 <- kl_E `pseq` consP kl_E
                                                                                                           klIf kl_if_14 (do let !aw_15 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                             !appl_16 <- kl_E `pseq` applyWrapper aw_15 [kl_E,
                                                                                                                                                                         Types.Atom (Types.Str "\n"),
                                                                                                                                                                         Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                             !appl_17 <- appl_16 `pseq` cn (Types.Atom (Types.Str "parse error here: ")) appl_16
                                                                                                                             appl_17 `pseq` simpleError appl_17) (do simpleError (Types.Atom (Types.Str "parse error\n"))))))
                                              let !aw_18 = Types.Atom (Types.UnboundSym "compile")
                                              !appl_19 <- appl_11 `pseq` (kl_V2275 `pseq` (appl_13 `pseq` applyWrapper aw_18 [appl_11,
                                                                                                                              kl_V2275,
                                                                                                                              appl_13]))
                                              !appl_20 <- appl_19 `pseq` hd appl_19
                                              appl_20 `pseq` applyWrapper appl_0 [appl_20]

kl_shen_trim_gubbins :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_trim_gubbins (!kl_V2277) = do !kl_if_0 <- kl_V2277 `pseq` consP kl_V2277
                                      !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2277 `pseq` hd kl_V2277
                                                                   !appl_3 <- kl_shen_space
                                                                   appl_2 `pseq` (appl_3 `pseq` eq appl_2 appl_3)) (do return (Atom (B False)))
                                      klIf kl_if_1 (do !appl_4 <- kl_V2277 `pseq` tl kl_V2277
                                                       appl_4 `pseq` kl_shen_trim_gubbins appl_4) (do !kl_if_5 <- kl_V2277 `pseq` consP kl_V2277
                                                                                                      !kl_if_6 <- klIf kl_if_5 (do !appl_7 <- kl_V2277 `pseq` hd kl_V2277
                                                                                                                                   !appl_8 <- kl_shen_newline
                                                                                                                                   appl_7 `pseq` (appl_8 `pseq` eq appl_7 appl_8)) (do return (Atom (B False)))
                                                                                                      klIf kl_if_6 (do !appl_9 <- kl_V2277 `pseq` tl kl_V2277
                                                                                                                       appl_9 `pseq` kl_shen_trim_gubbins appl_9) (do !kl_if_10 <- kl_V2277 `pseq` consP kl_V2277
                                                                                                                                                                      !kl_if_11 <- klIf kl_if_10 (do !appl_12 <- kl_V2277 `pseq` hd kl_V2277
                                                                                                                                                                                                     !appl_13 <- kl_shen_carriage_return
                                                                                                                                                                                                     appl_12 `pseq` (appl_13 `pseq` eq appl_12 appl_13)) (do return (Atom (B False)))
                                                                                                                                                                      klIf kl_if_11 (do !appl_14 <- kl_V2277 `pseq` tl kl_V2277
                                                                                                                                                                                        appl_14 `pseq` kl_shen_trim_gubbins appl_14) (do !kl_if_15 <- kl_V2277 `pseq` consP kl_V2277
                                                                                                                                                                                                                                         !kl_if_16 <- klIf kl_if_15 (do !appl_17 <- kl_V2277 `pseq` hd kl_V2277
                                                                                                                                                                                                                                                                        !appl_18 <- kl_shen_tab
                                                                                                                                                                                                                                                                        appl_17 `pseq` (appl_18 `pseq` eq appl_17 appl_18)) (do return (Atom (B False)))
                                                                                                                                                                                                                                         klIf kl_if_16 (do !appl_19 <- kl_V2277 `pseq` tl kl_V2277
                                                                                                                                                                                                                                                           appl_19 `pseq` kl_shen_trim_gubbins appl_19) (do !kl_if_20 <- kl_V2277 `pseq` consP kl_V2277
                                                                                                                                                                                                                                                                                                            !kl_if_21 <- klIf kl_if_20 (do !appl_22 <- kl_V2277 `pseq` hd kl_V2277
                                                                                                                                                                                                                                                                                                                                           !appl_23 <- kl_shen_left_round
                                                                                                                                                                                                                                                                                                                                           appl_22 `pseq` (appl_23 `pseq` eq appl_22 appl_23)) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                                                            klIf kl_if_21 (do !appl_24 <- kl_V2277 `pseq` tl kl_V2277
                                                                                                                                                                                                                                                                                                                              appl_24 `pseq` kl_shen_trim_gubbins appl_24) (do klIf (Atom (B True)) (do return kl_V2277) (do return (List [])))))))

kl_shen_space :: Types.KLContext Types.Env Types.KLValue
kl_shen_space = do return (Types.Atom (Types.N (Types.KI 32)))

kl_shen_tab :: Types.KLContext Types.Env Types.KLValue
kl_shen_tab = do return (Types.Atom (Types.N (Types.KI 9)))

kl_shen_left_round :: Types.KLContext Types.Env Types.KLValue
kl_shen_left_round = do return (Types.Atom (Types.N (Types.KI 40)))

kl_shen_find :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_find (!kl_V2284) (!kl_V2285) = do let !appl_0 = List []
                                          !kl_if_1 <- appl_0 `pseq` (kl_V2285 `pseq` eq appl_0 kl_V2285)
                                          klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V2285 `pseq` consP kl_V2285
                                                                                 !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V2285 `pseq` hd kl_V2285
                                                                                                              appl_4 `pseq` applyWrapper kl_V2284 [appl_4]) (do return (Atom (B False)))
                                                                                 klIf kl_if_3 (do !appl_5 <- kl_V2285 `pseq` hd kl_V2285
                                                                                                  !appl_6 <- kl_V2285 `pseq` tl kl_V2285
                                                                                                  !appl_7 <- kl_V2284 `pseq` (appl_6 `pseq` kl_shen_find kl_V2284 appl_6)
                                                                                                  appl_5 `pseq` (appl_7 `pseq` klCons appl_5 appl_7)) (do !kl_if_8 <- kl_V2285 `pseq` consP kl_V2285
                                                                                                                                                          klIf kl_if_8 (do !appl_9 <- kl_V2285 `pseq` tl kl_V2285
                                                                                                                                                                           kl_V2284 `pseq` (appl_9 `pseq` kl_shen_find kl_V2284 appl_9)) (do klIf (Atom (B True)) (do let !aw_10 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                      applyWrapper aw_10 [ApplC (wrapNamed "shen.find" kl_shen_find)]) (do return (List [])))))

kl_shen_prefixP :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_prefixP (!kl_V2297) (!kl_V2298) = do let !appl_0 = List []
                                             !kl_if_1 <- appl_0 `pseq` (kl_V2297 `pseq` eq appl_0 kl_V2297)
                                             klIf kl_if_1 (do return (Atom (B True))) (do !kl_if_2 <- kl_V2297 `pseq` consP kl_V2297
                                                                                          !kl_if_3 <- klIf kl_if_2 (do !kl_if_4 <- kl_V2298 `pseq` consP kl_V2298
                                                                                                                       klIf kl_if_4 (do !appl_5 <- kl_V2298 `pseq` hd kl_V2298
                                                                                                                                        !appl_6 <- kl_V2297 `pseq` hd kl_V2297
                                                                                                                                        appl_5 `pseq` (appl_6 `pseq` eq appl_5 appl_6)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                          klIf kl_if_3 (do !appl_7 <- kl_V2297 `pseq` tl kl_V2297
                                                                                                           !appl_8 <- kl_V2298 `pseq` tl kl_V2298
                                                                                                           appl_7 `pseq` (appl_8 `pseq` kl_shen_prefixP appl_7 appl_8)) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List []))))

kl_shen_print_past_inputs :: Types.KLValue ->
                             Types.KLValue ->
                             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_print_past_inputs (!kl_V2307) (!kl_V2308) (!kl_V2309) = do let !appl_0 = List []
                                                                   !kl_if_1 <- appl_0 `pseq` (kl_V2308 `pseq` eq appl_0 kl_V2308)
                                                                   klIf kl_if_1 (do return (Types.Atom (Types.UnboundSym "_"))) (do !kl_if_2 <- kl_V2308 `pseq` consP kl_V2308
                                                                                                                                    !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V2308 `pseq` hd kl_V2308
                                                                                                                                                                 !appl_5 <- appl_4 `pseq` applyWrapper kl_V2307 [appl_4]
                                                                                                                                                                 let !aw_6 = Types.Atom (Types.UnboundSym "not")
                                                                                                                                                                 appl_5 `pseq` applyWrapper aw_6 [appl_5]) (do return (Atom (B False)))
                                                                                                                                    klIf kl_if_3 (do !appl_7 <- kl_V2308 `pseq` tl kl_V2308
                                                                                                                                                     !appl_8 <- kl_V2309 `pseq` add kl_V2309 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                     kl_V2307 `pseq` (appl_7 `pseq` (appl_8 `pseq` kl_shen_print_past_inputs kl_V2307 appl_7 appl_8))) (do !kl_if_9 <- kl_V2308 `pseq` consP kl_V2308
                                                                                                                                                                                                                                                           !kl_if_10 <- klIf kl_if_9 (do !appl_11 <- kl_V2308 `pseq` hd kl_V2308
                                                                                                                                                                                                                                                                                         let !aw_12 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                                                                                                                         appl_11 `pseq` applyWrapper aw_12 [appl_11]) (do return (Atom (B False)))
                                                                                                                                                                                                                                                           klIf kl_if_10 (do let !aw_13 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                             !appl_14 <- kl_V2309 `pseq` applyWrapper aw_13 [kl_V2309,
                                                                                                                                                                                                                                                                                                                             Types.Atom (Types.Str ". "),
                                                                                                                                                                                                                                                                                                                             Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                                                                                                                                             let !aw_15 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                                                                                                                                                                                             !appl_16 <- applyWrapper aw_15 []
                                                                                                                                                                                                                                                                             let !aw_17 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                             !appl_18 <- appl_14 `pseq` (appl_16 `pseq` applyWrapper aw_17 [appl_14,
                                                                                                                                                                                                                                                                                                                                            appl_16])
                                                                                                                                                                                                                                                                             !appl_19 <- kl_V2308 `pseq` hd kl_V2308
                                                                                                                                                                                                                                                                             let !aw_20 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                             !appl_21 <- appl_19 `pseq` applyWrapper aw_20 [appl_19]
                                                                                                                                                                                                                                                                             !appl_22 <- appl_21 `pseq` kl_shen_prbytes appl_21
                                                                                                                                                                                                                                                                             !appl_23 <- kl_V2308 `pseq` tl kl_V2308
                                                                                                                                                                                                                                                                             !appl_24 <- kl_V2309 `pseq` add kl_V2309 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                             !appl_25 <- kl_V2307 `pseq` (appl_23 `pseq` (appl_24 `pseq` kl_shen_print_past_inputs kl_V2307 appl_23 appl_24))
                                                                                                                                                                                                                                                                             let !aw_26 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                                                                                                                                             !appl_27 <- appl_22 `pseq` (appl_25 `pseq` applyWrapper aw_26 [appl_22,
                                                                                                                                                                                                                                                                                                                                            appl_25])
                                                                                                                                                                                                                                                                             let !aw_28 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                                                                                                                                             appl_18 `pseq` (appl_27 `pseq` applyWrapper aw_28 [appl_18,
                                                                                                                                                                                                                                                                                                                                appl_27])) (do klIf (Atom (B True)) (do let !aw_29 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                                                        applyWrapper aw_29 [ApplC (wrapNamed "shen.print-past-inputs" kl_shen_print_past_inputs)]) (do return (List [])))))

kl_shen_toplevel_evaluate :: Types.KLValue ->
                             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_toplevel_evaluate (!kl_V2310) (!kl_V2311) = do !kl_if_0 <- kl_V2310 `pseq` consP kl_V2310
                                                       !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2310 `pseq` tl kl_V2310
                                                                                    !kl_if_3 <- appl_2 `pseq` consP appl_2
                                                                                    klIf kl_if_3 (do !appl_4 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                     !appl_5 <- appl_4 `pseq` hd appl_4
                                                                                                     !kl_if_6 <- appl_5 `pseq` eq (Types.Atom (Types.UnboundSym ":")) appl_5
                                                                                                     klIf kl_if_6 (do !appl_7 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                                      !appl_8 <- appl_7 `pseq` tl appl_7
                                                                                                                      !kl_if_9 <- appl_8 `pseq` consP appl_8
                                                                                                                      klIf kl_if_9 (do let !appl_10 = List []
                                                                                                                                       !appl_11 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                                                       !appl_12 <- appl_11 `pseq` tl appl_11
                                                                                                                                       !appl_13 <- appl_12 `pseq` tl appl_12
                                                                                                                                       !kl_if_14 <- appl_10 `pseq` (appl_13 `pseq` eq appl_10 appl_13)
                                                                                                                                       klIf kl_if_14 (do kl_V2311 `pseq` eq (Atom (B True)) kl_V2311) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                       klIf kl_if_1 (do !appl_15 <- kl_V2310 `pseq` hd kl_V2310
                                                                        !appl_16 <- kl_V2310 `pseq` tl kl_V2310
                                                                        !appl_17 <- appl_16 `pseq` tl appl_16
                                                                        !appl_18 <- appl_17 `pseq` hd appl_17
                                                                        appl_15 `pseq` (appl_18 `pseq` kl_shen_typecheck_and_evaluate appl_15 appl_18)) (do !kl_if_19 <- kl_V2310 `pseq` consP kl_V2310
                                                                                                                                                            !kl_if_20 <- klIf kl_if_19 (do !appl_21 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                                                                                                           appl_21 `pseq` consP appl_21) (do return (Atom (B False)))
                                                                                                                                                            klIf kl_if_20 (do !appl_22 <- kl_V2310 `pseq` hd kl_V2310
                                                                                                                                                                              let !appl_23 = List []
                                                                                                                                                                              !appl_24 <- appl_22 `pseq` (appl_23 `pseq` klCons appl_22 appl_23)
                                                                                                                                                                              !appl_25 <- appl_24 `pseq` (kl_V2311 `pseq` kl_shen_toplevel_evaluate appl_24 kl_V2311)
                                                                                                                                                                              let !aw_26 = Types.Atom (Types.UnboundSym "nl")
                                                                                                                                                                              !appl_27 <- applyWrapper aw_26 [Types.Atom (Types.N (Types.KI 1))]
                                                                                                                                                                              !appl_28 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                                                                                              !appl_29 <- appl_28 `pseq` (kl_V2311 `pseq` kl_shen_toplevel_evaluate appl_28 kl_V2311)
                                                                                                                                                                              let !aw_30 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                                              !appl_31 <- appl_27 `pseq` (appl_29 `pseq` applyWrapper aw_30 [appl_27,
                                                                                                                                                                                                                                             appl_29])
                                                                                                                                                                              let !aw_32 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                                              appl_25 `pseq` (appl_31 `pseq` applyWrapper aw_32 [appl_25,
                                                                                                                                                                                                                                 appl_31])) (do !kl_if_33 <- kl_V2310 `pseq` consP kl_V2310
                                                                                                                                                                                                                                                !kl_if_34 <- klIf kl_if_33 (do let !appl_35 = List []
                                                                                                                                                                                                                                                                               !appl_36 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                                                                                                                                                                                               !kl_if_37 <- appl_35 `pseq` (appl_36 `pseq` eq appl_35 appl_36)
                                                                                                                                                                                                                                                                               klIf kl_if_37 (do kl_V2311 `pseq` eq (Atom (B True)) kl_V2311) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                klIf kl_if_34 (do !appl_38 <- kl_V2310 `pseq` hd kl_V2310
                                                                                                                                                                                                                                                                  let !aw_39 = Types.Atom (Types.UnboundSym "gensym")
                                                                                                                                                                                                                                                                  !appl_40 <- applyWrapper aw_39 [Types.Atom (Types.UnboundSym "A")]
                                                                                                                                                                                                                                                                  appl_38 `pseq` (appl_40 `pseq` kl_shen_typecheck_and_evaluate appl_38 appl_40)) (do !kl_if_41 <- kl_V2310 `pseq` consP kl_V2310
                                                                                                                                                                                                                                                                                                                                                      !kl_if_42 <- klIf kl_if_41 (do let !appl_43 = List []
                                                                                                                                                                                                                                                                                                                                                                                     !appl_44 <- kl_V2310 `pseq` tl kl_V2310
                                                                                                                                                                                                                                                                                                                                                                                     !kl_if_45 <- appl_43 `pseq` (appl_44 `pseq` eq appl_43 appl_44)
                                                                                                                                                                                                                                                                                                                                                                                     klIf kl_if_45 (do kl_V2311 `pseq` eq (Atom (B False)) kl_V2311) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                                                                                                      klIf kl_if_42 (do let !appl_46 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do let !aw_47 = Types.Atom (Types.UnboundSym "print")
                                                                                                                                                                                                                                                                                                                                                                                                                                        kl_Eval `pseq` applyWrapper aw_47 [kl_Eval])))
                                                                                                                                                                                                                                                                                                                                                                        !appl_48 <- kl_V2310 `pseq` hd kl_V2310
                                                                                                                                                                                                                                                                                                                                                                        let !aw_49 = Types.Atom (Types.UnboundSym "shen.eval-without-macros")
                                                                                                                                                                                                                                                                                                                                                                        !appl_50 <- appl_48 `pseq` applyWrapper aw_49 [appl_48]
                                                                                                                                                                                                                                                                                                                                                                        appl_50 `pseq` applyWrapper appl_46 [appl_50]) (do klIf (Atom (B True)) (do let !aw_51 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                                                                                                                                                                                                    applyWrapper aw_51 [ApplC (wrapNamed "shen.toplevel_evaluate" kl_shen_toplevel_evaluate)]) (do return (List []))))))

kl_shen_typecheck_and_evaluate :: Types.KLValue ->
                                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_typecheck_and_evaluate (!kl_V2312) (!kl_V2313) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Typecheck) -> do !kl_if_1 <- kl_Typecheck `pseq` eq kl_Typecheck (Atom (B False))
                                                                                                                                klIf kl_if_1 (do simpleError (Types.Atom (Types.Str "type error\n"))) (do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Type) -> do let !aw_4 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                                                                        !appl_5 <- kl_Type `pseq` applyWrapper aw_4 [kl_Type,
                                                                                                                                                                                                                                                                                                                                                                                      Types.Atom (Types.Str ""),
                                                                                                                                                                                                                                                                                                                                                                                      Types.Atom (Types.UnboundSym "shen.r")]
                                                                                                                                                                                                                                                                                                                                        !appl_6 <- appl_5 `pseq` cn (Types.Atom (Types.Str " : ")) appl_5
                                                                                                                                                                                                                                                                                                                                        let !aw_7 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                                                                        !appl_8 <- kl_Eval `pseq` (appl_6 `pseq` applyWrapper aw_7 [kl_Eval,
                                                                                                                                                                                                                                                                                                                                                                                                    appl_6,
                                                                                                                                                                                                                                                                                                                                                                                                    Types.Atom (Types.UnboundSym "shen.s")])
                                                                                                                                                                                                                                                                                                                                        let !aw_9 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                                                                                                                                                                                                                                                        !appl_10 <- applyWrapper aw_9 []
                                                                                                                                                                                                                                                                                                                                        let !aw_11 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                                                                                        appl_8 `pseq` (appl_10 `pseq` applyWrapper aw_11 [appl_8,
                                                                                                                                                                                                                                                                                                                                                                                          appl_10]))))
                                                                                                                                                                                                                                                                         !appl_12 <- kl_Typecheck `pseq` kl_shen_pretty_type kl_Typecheck
                                                                                                                                                                                                                                                                         appl_12 `pseq` applyWrapper appl_3 [appl_12])))
                                                                                                                                                                                                          let !aw_13 = Types.Atom (Types.UnboundSym "shen.eval-without-macros")
                                                                                                                                                                                                          !appl_14 <- kl_V2312 `pseq` applyWrapper aw_13 [kl_V2312]
                                                                                                                                                                                                          appl_14 `pseq` applyWrapper appl_2 [appl_14]))))
                                                            let !aw_15 = Types.Atom (Types.UnboundSym "shen.typecheck")
                                                            !appl_16 <- kl_V2312 `pseq` (kl_V2313 `pseq` applyWrapper aw_15 [kl_V2312,
                                                                                                                             kl_V2313])
                                                            appl_16 `pseq` applyWrapper appl_0 [appl_16]

kl_shen_pretty_type :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_pretty_type (!kl_V2314) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*alphabet*"))
                                     !appl_1 <- kl_V2314 `pseq` kl_shen_extract_pvars kl_V2314
                                     appl_0 `pseq` (appl_1 `pseq` (kl_V2314 `pseq` kl_shen_mult_subst appl_0 appl_1 kl_V2314))

kl_shen_extract_pvars :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_extract_pvars (!kl_V2319) = do let !aw_0 = Types.Atom (Types.UnboundSym "shen.pvar?")
                                       !kl_if_1 <- kl_V2319 `pseq` applyWrapper aw_0 [kl_V2319]
                                       klIf kl_if_1 (do let !appl_2 = List []
                                                        kl_V2319 `pseq` (appl_2 `pseq` klCons kl_V2319 appl_2)) (do !kl_if_3 <- kl_V2319 `pseq` consP kl_V2319
                                                                                                                    klIf kl_if_3 (do !appl_4 <- kl_V2319 `pseq` hd kl_V2319
                                                                                                                                     !appl_5 <- appl_4 `pseq` kl_shen_extract_pvars appl_4
                                                                                                                                     !appl_6 <- kl_V2319 `pseq` tl kl_V2319
                                                                                                                                     !appl_7 <- appl_6 `pseq` kl_shen_extract_pvars appl_6
                                                                                                                                     let !aw_8 = Types.Atom (Types.UnboundSym "union")
                                                                                                                                     appl_5 `pseq` (appl_7 `pseq` applyWrapper aw_8 [appl_5,
                                                                                                                                                                                     appl_7])) (do klIf (Atom (B True)) (do return (List [])) (do return (List []))))

kl_shen_mult_subst :: Types.KLValue ->
                      Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mult_subst (!kl_V2324) (!kl_V2325) (!kl_V2326) = do let !appl_0 = List []
                                                            !kl_if_1 <- appl_0 `pseq` (kl_V2324 `pseq` eq appl_0 kl_V2324)
                                                            klIf kl_if_1 (do return kl_V2326) (do let !appl_2 = List []
                                                                                                  !kl_if_3 <- appl_2 `pseq` (kl_V2325 `pseq` eq appl_2 kl_V2325)
                                                                                                  klIf kl_if_3 (do return kl_V2326) (do !kl_if_4 <- kl_V2324 `pseq` consP kl_V2324
                                                                                                                                        !kl_if_5 <- klIf kl_if_4 (do kl_V2325 `pseq` consP kl_V2325) (do return (Atom (B False)))
                                                                                                                                        klIf kl_if_5 (do !appl_6 <- kl_V2324 `pseq` tl kl_V2324
                                                                                                                                                         !appl_7 <- kl_V2325 `pseq` tl kl_V2325
                                                                                                                                                         !appl_8 <- kl_V2324 `pseq` hd kl_V2324
                                                                                                                                                         !appl_9 <- kl_V2325 `pseq` hd kl_V2325
                                                                                                                                                         let !aw_10 = Types.Atom (Types.UnboundSym "subst")
                                                                                                                                                         !appl_11 <- appl_8 `pseq` (appl_9 `pseq` (kl_V2326 `pseq` applyWrapper aw_10 [appl_8,
                                                                                                                                                                                                                                       appl_9,
                                                                                                                                                                                                                                       kl_V2326]))
                                                                                                                                                         appl_6 `pseq` (appl_7 `pseq` (appl_11 `pseq` kl_shen_mult_subst appl_6 appl_7 appl_11))) (do klIf (Atom (B True)) (do let !aw_12 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                                                                                                                               applyWrapper aw_12 [ApplC (wrapNamed "shen.mult_subst" kl_shen_mult_subst)]) (do return (List [])))))

expr0 :: Types.KLContext Types.Env Types.KLValue
expr0 = do (do let !appl_0 = List []
               appl_0 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*history*")) appl_0) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
