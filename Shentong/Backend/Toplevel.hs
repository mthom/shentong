{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Backend.Toplevel where

import Control.Monad.Except
import Control.Parallel
import Shentong.Environment
import Shentong.Primitives as Primitives
import Shentong.Backend.Utils
import Shentong.Types as Types
import Shentong.Utils
import Shentong.Wrap

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
kl_shen_initialise_environment = do !appl_0 <- klCons (Types.Atom (Types.N (Types.KI 0))) (Types.Atom Types.Nil)
                                    !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*catch*")) appl_0
                                    !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_1
                                    !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*process-counter*")) appl_2
                                    !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_3
                                    !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*infs*")) appl_4
                                    !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_5
                                    !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_6
                                    appl_7 `pseq` kl_shen_multiple_set appl_7

kl_shen_multiple_set :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_multiple_set (!kl_V3668) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                          pat_cond_1 kl_V3668 kl_V3668h kl_V3668t kl_V3668th kl_V3668tt = do !appl_2 <- kl_V3668h `pseq` (kl_V3668th `pseq` klSet kl_V3668h kl_V3668th)
                                                                                                             !appl_3 <- kl_V3668tt `pseq` kl_shen_multiple_set kl_V3668tt
                                                                                                             let !aw_4 = Types.Atom (Types.UnboundSym "do")
                                                                                                             appl_2 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_2,
                                                                                                                                                             appl_3])
                                          pat_cond_5 = do do let !aw_6 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                             applyWrapper aw_6 [ApplC (wrapNamed "shen.multiple-set" kl_shen_multiple_set)]
                                       in case kl_V3668 of
                                              kl_V3668@(Atom (Nil)) -> pat_cond_0
                                              !(kl_V3668@(Cons (!kl_V3668h)
                                                               (!(kl_V3668t@(Cons (!kl_V3668th)
                                                                                  (!kl_V3668tt)))))) -> pat_cond_1 kl_V3668 kl_V3668h kl_V3668t kl_V3668th kl_V3668tt
                                              _ -> pat_cond_5

kl_destroy :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_destroy (!kl_V3670) = do let !aw_0 = Types.Atom (Types.UnboundSym "declare")
                            kl_V3670 `pseq` applyWrapper aw_0 [kl_V3670,
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
kl_shen_retrieve_from_history_if_needed (!kl_V3682) (!kl_V3683) = do let !aw_0 = Types.Atom (Types.UnboundSym "tuple?")
                                                                     !kl_if_1 <- kl_V3682 `pseq` applyWrapper aw_0 [kl_V3682]
                                                                     !kl_if_2 <- case kl_if_1 of
                                                                                     Atom (B (True)) -> do let !aw_3 = Types.Atom (Types.UnboundSym "snd")
                                                                                                           !appl_4 <- kl_V3682 `pseq` applyWrapper aw_3 [kl_V3682]
                                                                                                           !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                           !kl_if_6 <- case kl_if_5 of
                                                                                                                           Atom (B (True)) -> do let !aw_7 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                 !appl_8 <- kl_V3682 `pseq` applyWrapper aw_7 [kl_V3682]
                                                                                                                                                 !appl_9 <- appl_8 `pseq` hd appl_8
                                                                                                                                                 !appl_10 <- kl_shen_space
                                                                                                                                                 !appl_11 <- kl_shen_newline
                                                                                                                                                 !appl_12 <- appl_11 `pseq` klCons appl_11 (Types.Atom Types.Nil)
                                                                                                                                                 !appl_13 <- appl_10 `pseq` (appl_12 `pseq` klCons appl_10 appl_12)
                                                                                                                                                 let !aw_14 = Types.Atom (Types.UnboundSym "element?")
                                                                                                                                                 !kl_if_15 <- appl_9 `pseq` (appl_13 `pseq` applyWrapper aw_14 [appl_9,
                                                                                                                                                                                                                appl_13])
                                                                                                                                                 case kl_if_15 of
                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                           case kl_if_6 of
                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                               _ -> throwError "if: expected boolean"
                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                     _ -> throwError "if: expected boolean"
                                                                     case kl_if_2 of
                                                                         Atom (B (True)) -> do let !aw_16 = Types.Atom (Types.UnboundSym "fst")
                                                                                               !appl_17 <- kl_V3682 `pseq` applyWrapper aw_16 [kl_V3682]
                                                                                               let !aw_18 = Types.Atom (Types.UnboundSym "snd")
                                                                                               !appl_19 <- kl_V3682 `pseq` applyWrapper aw_18 [kl_V3682]
                                                                                               !appl_20 <- appl_19 `pseq` tl appl_19
                                                                                               let !aw_21 = Types.Atom (Types.UnboundSym "@p")
                                                                                               !appl_22 <- appl_17 `pseq` (appl_20 `pseq` applyWrapper aw_21 [appl_17,
                                                                                                                                                              appl_20])
                                                                                               appl_22 `pseq` (kl_V3683 `pseq` kl_shen_retrieve_from_history_if_needed appl_22 kl_V3683)
                                                                         Atom (B (False)) -> do let !aw_23 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                !kl_if_24 <- kl_V3682 `pseq` applyWrapper aw_23 [kl_V3682]
                                                                                                !kl_if_25 <- case kl_if_24 of
                                                                                                                 Atom (B (True)) -> do let !aw_26 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                       !appl_27 <- kl_V3682 `pseq` applyWrapper aw_26 [kl_V3682]
                                                                                                                                       !kl_if_28 <- appl_27 `pseq` consP appl_27
                                                                                                                                       !kl_if_29 <- case kl_if_28 of
                                                                                                                                                        Atom (B (True)) -> do let !aw_30 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                              !appl_31 <- kl_V3682 `pseq` applyWrapper aw_30 [kl_V3682]
                                                                                                                                                                              !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                              !kl_if_33 <- appl_32 `pseq` consP appl_32
                                                                                                                                                                              !kl_if_34 <- case kl_if_33 of
                                                                                                                                                                                               Atom (B (True)) -> do let !aw_35 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                     !appl_36 <- kl_V3682 `pseq` applyWrapper aw_35 [kl_V3682]
                                                                                                                                                                                                                     !appl_37 <- appl_36 `pseq` tl appl_36
                                                                                                                                                                                                                     !appl_38 <- appl_37 `pseq` tl appl_37
                                                                                                                                                                                                                     !kl_if_39 <- appl_38 `pseq` eq (Types.Atom Types.Nil) appl_38
                                                                                                                                                                                                                     !kl_if_40 <- case kl_if_39 of
                                                                                                                                                                                                                                      Atom (B (True)) -> do !kl_if_41 <- let pat_cond_42 kl_V3683 kl_V3683h kl_V3683t = do let !aw_43 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                           !appl_44 <- kl_V3682 `pseq` applyWrapper aw_43 [kl_V3682]
                                                                                                                                                                                                                                                                                                                           !appl_45 <- appl_44 `pseq` hd appl_44
                                                                                                                                                                                                                                                                                                                           !appl_46 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                                                           !kl_if_47 <- appl_45 `pseq` (appl_46 `pseq` eq appl_45 appl_46)
                                                                                                                                                                                                                                                                                                                           !kl_if_48 <- case kl_if_47 of
                                                                                                                                                                                                                                                                                                                                            Atom (B (True)) -> do let !aw_49 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                                                                                                  !appl_50 <- kl_V3682 `pseq` applyWrapper aw_49 [kl_V3682]
                                                                                                                                                                                                                                                                                                                                                                  !appl_51 <- appl_50 `pseq` tl appl_50
                                                                                                                                                                                                                                                                                                                                                                  !appl_52 <- appl_51 `pseq` hd appl_51
                                                                                                                                                                                                                                                                                                                                                                  !appl_53 <- kl_shen_exclamation
                                                                                                                                                                                                                                                                                                                                                                  !kl_if_54 <- appl_52 `pseq` (appl_53 `pseq` eq appl_52 appl_53)
                                                                                                                                                                                                                                                                                                                                                                  case kl_if_54 of
                                                                                                                                                                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                           case kl_if_48 of
                                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                             pat_cond_55 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                          in case kl_V3683 of
                                                                                                                                                                                                                                                                                 !(kl_V3683@(Cons (!kl_V3683h)
                                                                                                                                                                                                                                                                                                  (!kl_V3683t))) -> pat_cond_42 kl_V3683 kl_V3683h kl_V3683t
                                                                                                                                                                                                                                                                                 _ -> pat_cond_55
                                                                                                                                                                                                                                                            case kl_if_41 of
                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                     case kl_if_40 of
                                                                                                                                                                                                                         Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                              case kl_if_34 of
                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                       case kl_if_29 of
                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                case kl_if_25 of
                                                                                                    Atom (B (True)) -> do let !appl_56 = ApplC (Func "lambda" (Context (\(!kl_PastPrint) -> do kl_V3683 `pseq` hd kl_V3683)))
                                                                                                                          !appl_57 <- kl_V3683 `pseq` hd kl_V3683
                                                                                                                          let !aw_58 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                          !appl_59 <- appl_57 `pseq` applyWrapper aw_58 [appl_57]
                                                                                                                          !appl_60 <- appl_59 `pseq` kl_shen_prbytes appl_59
                                                                                                                          appl_60 `pseq` applyWrapper appl_56 [appl_60]
                                                                                                    Atom (B (False)) -> do let !aw_61 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                           !kl_if_62 <- kl_V3682 `pseq` applyWrapper aw_61 [kl_V3682]
                                                                                                                           !kl_if_63 <- case kl_if_62 of
                                                                                                                                            Atom (B (True)) -> do let !aw_64 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                  !appl_65 <- kl_V3682 `pseq` applyWrapper aw_64 [kl_V3682]
                                                                                                                                                                  !kl_if_66 <- appl_65 `pseq` consP appl_65
                                                                                                                                                                  !kl_if_67 <- case kl_if_66 of
                                                                                                                                                                                   Atom (B (True)) -> do let !aw_68 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                         !appl_69 <- kl_V3682 `pseq` applyWrapper aw_68 [kl_V3682]
                                                                                                                                                                                                         !appl_70 <- appl_69 `pseq` hd appl_69
                                                                                                                                                                                                         !appl_71 <- kl_shen_exclamation
                                                                                                                                                                                                         !kl_if_72 <- appl_70 `pseq` (appl_71 `pseq` eq appl_70 appl_71)
                                                                                                                                                                                                         case kl_if_72 of
                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                  case kl_if_67 of
                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                           case kl_if_63 of
                                                                                                                               Atom (B (True)) -> do let !appl_73 = ApplC (Func "lambda" (Context (\(!kl_KeyP) -> do let !appl_74 = ApplC (Func "lambda" (Context (\(!kl_Find) -> do let !appl_75 = ApplC (Func "lambda" (Context (\(!kl_PastPrint) -> do return kl_Find)))
                                                                                                                                                                                                                                                                                     let !aw_76 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                                     !appl_77 <- kl_Find `pseq` applyWrapper aw_76 [kl_Find]
                                                                                                                                                                                                                                                                                     !appl_78 <- appl_77 `pseq` kl_shen_prbytes appl_77
                                                                                                                                                                                                                                                                                     appl_78 `pseq` applyWrapper appl_75 [appl_78])))
                                                                                                                                                                                                                     !appl_79 <- kl_KeyP `pseq` (kl_V3683 `pseq` kl_shen_find_past_inputs kl_KeyP kl_V3683)
                                                                                                                                                                                                                     let !aw_80 = Types.Atom (Types.UnboundSym "head")
                                                                                                                                                                                                                     !appl_81 <- appl_79 `pseq` applyWrapper aw_80 [appl_79]
                                                                                                                                                                                                                     appl_81 `pseq` applyWrapper appl_74 [appl_81])))
                                                                                                                                                     let !aw_82 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                     !appl_83 <- kl_V3682 `pseq` applyWrapper aw_82 [kl_V3682]
                                                                                                                                                     !appl_84 <- appl_83 `pseq` tl appl_83
                                                                                                                                                     !appl_85 <- appl_84 `pseq` (kl_V3683 `pseq` kl_shen_make_key appl_84 kl_V3683)
                                                                                                                                                     appl_85 `pseq` applyWrapper appl_73 [appl_85]
                                                                                                                               Atom (B (False)) -> do let !aw_86 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                      !kl_if_87 <- kl_V3682 `pseq` applyWrapper aw_86 [kl_V3682]
                                                                                                                                                      !kl_if_88 <- case kl_if_87 of
                                                                                                                                                                       Atom (B (True)) -> do let !aw_89 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                             !appl_90 <- kl_V3682 `pseq` applyWrapper aw_89 [kl_V3682]
                                                                                                                                                                                             !kl_if_91 <- appl_90 `pseq` consP appl_90
                                                                                                                                                                                             !kl_if_92 <- case kl_if_91 of
                                                                                                                                                                                                              Atom (B (True)) -> do let !aw_93 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                    !appl_94 <- kl_V3682 `pseq` applyWrapper aw_93 [kl_V3682]
                                                                                                                                                                                                                                    !appl_95 <- appl_94 `pseq` tl appl_94
                                                                                                                                                                                                                                    !kl_if_96 <- appl_95 `pseq` eq (Types.Atom Types.Nil) appl_95
                                                                                                                                                                                                                                    !kl_if_97 <- case kl_if_96 of
                                                                                                                                                                                                                                                     Atom (B (True)) -> do let !aw_98 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                           !appl_99 <- kl_V3682 `pseq` applyWrapper aw_98 [kl_V3682]
                                                                                                                                                                                                                                                                           !appl_100 <- appl_99 `pseq` hd appl_99
                                                                                                                                                                                                                                                                           !appl_101 <- kl_shen_percent
                                                                                                                                                                                                                                                                           !kl_if_102 <- appl_100 `pseq` (appl_101 `pseq` eq appl_100 appl_101)
                                                                                                                                                                                                                                                                           case kl_if_102 of
                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                    case kl_if_97 of
                                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                                                                             case kl_if_92 of
                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                      case kl_if_88 of
                                                                                                                                                          Atom (B (True)) -> do let !appl_103 = ApplC (Func "lambda" (Context (\(!kl_X) -> do return (Atom (B True)))))
                                                                                                                                                                                let !aw_104 = Types.Atom (Types.UnboundSym "reverse")
                                                                                                                                                                                !appl_105 <- kl_V3683 `pseq` applyWrapper aw_104 [kl_V3683]
                                                                                                                                                                                !appl_106 <- appl_103 `pseq` (appl_105 `pseq` kl_shen_print_past_inputs appl_103 appl_105 (Types.Atom (Types.N (Types.KI 0))))
                                                                                                                                                                                let !aw_107 = Types.Atom (Types.UnboundSym "abort")
                                                                                                                                                                                !appl_108 <- applyWrapper aw_107 []
                                                                                                                                                                                let !aw_109 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                                                appl_106 `pseq` (appl_108 `pseq` applyWrapper aw_109 [appl_106,
                                                                                                                                                                                                                                      appl_108])
                                                                                                                                                          Atom (B (False)) -> do let !aw_110 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                 !kl_if_111 <- kl_V3682 `pseq` applyWrapper aw_110 [kl_V3682]
                                                                                                                                                                                 !kl_if_112 <- case kl_if_111 of
                                                                                                                                                                                                   Atom (B (True)) -> do let !aw_113 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                         !appl_114 <- kl_V3682 `pseq` applyWrapper aw_113 [kl_V3682]
                                                                                                                                                                                                                         !kl_if_115 <- appl_114 `pseq` consP appl_114
                                                                                                                                                                                                                         !kl_if_116 <- case kl_if_115 of
                                                                                                                                                                                                                                           Atom (B (True)) -> do let !aw_117 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                                                                                 !appl_118 <- kl_V3682 `pseq` applyWrapper aw_117 [kl_V3682]
                                                                                                                                                                                                                                                                 !appl_119 <- appl_118 `pseq` hd appl_118
                                                                                                                                                                                                                                                                 !appl_120 <- kl_shen_percent
                                                                                                                                                                                                                                                                 !kl_if_121 <- appl_119 `pseq` (appl_120 `pseq` eq appl_119 appl_120)
                                                                                                                                                                                                                                                                 case kl_if_121 of
                                                                                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                         case kl_if_116 of
                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                 case kl_if_112 of
                                                                                                                                                                                     Atom (B (True)) -> do let !appl_122 = ApplC (Func "lambda" (Context (\(!kl_KeyP) -> do let !appl_123 = ApplC (Func "lambda" (Context (\(!kl_Pastprint) -> do let !aw_124 = Types.Atom (Types.UnboundSym "abort")
                                                                                                                                                                                                                                                                                                                                                  applyWrapper aw_124 [])))
                                                                                                                                                                                                                                                                            let !aw_125 = Types.Atom (Types.UnboundSym "reverse")
                                                                                                                                                                                                                                                                            !appl_126 <- kl_V3683 `pseq` applyWrapper aw_125 [kl_V3683]
                                                                                                                                                                                                                                                                            !appl_127 <- kl_KeyP `pseq` (appl_126 `pseq` kl_shen_print_past_inputs kl_KeyP appl_126 (Types.Atom (Types.N (Types.KI 0))))
                                                                                                                                                                                                                                                                            appl_127 `pseq` applyWrapper appl_123 [appl_127])))
                                                                                                                                                                                                           let !aw_128 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                           !appl_129 <- kl_V3682 `pseq` applyWrapper aw_128 [kl_V3682]
                                                                                                                                                                                                           !appl_130 <- appl_129 `pseq` tl appl_129
                                                                                                                                                                                                           !appl_131 <- appl_130 `pseq` (kl_V3683 `pseq` kl_shen_make_key appl_130 kl_V3683)
                                                                                                                                                                                                           appl_131 `pseq` applyWrapper appl_122 [appl_131]
                                                                                                                                                                                     Atom (B (False)) -> do do return kl_V3682
                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                    _ -> throwError "if: expected boolean"
                                                                         _ -> throwError "if: expected boolean"

kl_shen_percent :: Types.KLContext Types.Env Types.KLValue
kl_shen_percent = do return (Types.Atom (Types.N (Types.KI 37)))

kl_shen_exclamation :: Types.KLContext Types.Env Types.KLValue
kl_shen_exclamation = do return (Types.Atom (Types.N (Types.KI 33)))

kl_shen_prbytes :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_prbytes (!kl_V3685) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Byte) -> do !appl_1 <- kl_Byte `pseq` nToString kl_Byte
                                                                                                let !aw_2 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                !appl_3 <- applyWrapper aw_2 []
                                                                                                let !aw_4 = Types.Atom (Types.UnboundSym "pr")
                                                                                                appl_1 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_1,
                                                                                                                                                appl_3]))))
                                 let !aw_5 = Types.Atom (Types.UnboundSym "map")
                                 !appl_6 <- appl_0 `pseq` (kl_V3685 `pseq` applyWrapper aw_5 [appl_0,
                                                                                              kl_V3685])
                                 let !aw_7 = Types.Atom (Types.UnboundSym "nl")
                                 !appl_8 <- applyWrapper aw_7 [Types.Atom (Types.N (Types.KI 1))]
                                 let !aw_9 = Types.Atom (Types.UnboundSym "do")
                                 appl_6 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_6, appl_8])

kl_shen_update_history :: Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_update_history (!kl_V3688) (!kl_V3689) = do !appl_0 <- kl_V3688 `pseq` (kl_V3689 `pseq` klCons kl_V3688 kl_V3689)
                                                    appl_0 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*history*")) appl_0

kl_shen_toplineread :: Types.KLContext Types.Env Types.KLValue
kl_shen_toplineread = do let !aw_0 = Types.Atom (Types.UnboundSym "stinput")
                         !appl_1 <- applyWrapper aw_0 []
                         !appl_2 <- appl_1 `pseq` readByte appl_1
                         appl_2 `pseq` kl_shen_toplineread_loop appl_2 (Types.Atom Types.Nil)

kl_shen_toplineread_loop :: Types.KLValue ->
                            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_toplineread_loop (!kl_V3693) (!kl_V3694) = do !appl_0 <- kl_shen_hat
                                                      !kl_if_1 <- kl_V3693 `pseq` (appl_0 `pseq` eq kl_V3693 appl_0)
                                                      case kl_if_1 of
                                                          Atom (B (True)) -> do simpleError (Types.Atom (Types.Str "line read aborted"))
                                                          Atom (B (False)) -> do !appl_2 <- kl_shen_newline
                                                                                 !appl_3 <- kl_shen_carriage_return
                                                                                 !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                 !appl_5 <- appl_2 `pseq` (appl_4 `pseq` klCons appl_2 appl_4)
                                                                                 let !aw_6 = Types.Atom (Types.UnboundSym "element?")
                                                                                 !kl_if_7 <- kl_V3693 `pseq` (appl_5 `pseq` applyWrapper aw_6 [kl_V3693,
                                                                                                                                               appl_5])
                                                                                 case kl_if_7 of
                                                                                     Atom (B (True)) -> do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_Line) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_It) -> do !kl_if_10 <- let pat_cond_11 = do return (Atom (B True))
                                                                                                                                                                                                                                                        pat_cond_12 = do do let !aw_13 = Types.Atom (Types.UnboundSym "empty?")
                                                                                                                                                                                                                                                                            !kl_if_14 <- kl_Line `pseq` applyWrapper aw_13 [kl_Line]
                                                                                                                                                                                                                                                                            case kl_if_14 of
                                                                                                                                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                     in case kl_Line of
                                                                                                                                                                                                                                                            kl_Line@(Atom (UnboundSym "shen.nextline")) -> pat_cond_11
                                                                                                                                                                                                                                                            kl_Line@(ApplC (PL "shen.nextline"
                                                                                                                                                                                                                                                                               _)) -> pat_cond_11
                                                                                                                                                                                                                                                            kl_Line@(ApplC (Func "shen.nextline"
                                                                                                                                                                                                                                                                                 _)) -> pat_cond_11
                                                                                                                                                                                                                                                            _ -> pat_cond_12
                                                                                                                                                                                                                                       case kl_if_10 of
                                                                                                                                                                                                                                           Atom (B (True)) -> do let !aw_15 = Types.Atom (Types.UnboundSym "stinput")
                                                                                                                                                                                                                                                                 !appl_16 <- applyWrapper aw_15 []
                                                                                                                                                                                                                                                                 !appl_17 <- appl_16 `pseq` readByte appl_16
                                                                                                                                                                                                                                                                 !appl_18 <- kl_V3693 `pseq` klCons kl_V3693 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                 let !aw_19 = Types.Atom (Types.UnboundSym "append")
                                                                                                                                                                                                                                                                 !appl_20 <- kl_V3694 `pseq` (appl_18 `pseq` applyWrapper aw_19 [kl_V3694,
                                                                                                                                                                                                                                                                                                                                 appl_18])
                                                                                                                                                                                                                                                                 appl_17 `pseq` (appl_20 `pseq` kl_shen_toplineread_loop appl_17 appl_20)
                                                                                                                                                                                                                                           Atom (B (False)) -> do do let !aw_21 = Types.Atom (Types.UnboundSym "@p")
                                                                                                                                                                                                                                                                     kl_Line `pseq` (kl_V3694 `pseq` applyWrapper aw_21 [kl_Line,
                                                                                                                                                                                                                                                                                                                         kl_V3694])
                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean")))
                                                                                                                                                                          let !aw_22 = Types.Atom (Types.UnboundSym "shen.record-it")
                                                                                                                                                                          !appl_23 <- kl_V3694 `pseq` applyWrapper aw_22 [kl_V3694]
                                                                                                                                                                          appl_23 `pseq` applyWrapper appl_9 [appl_23])))
                                                                                                           let !appl_24 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_25 = Types.Atom (Types.UnboundSym "shen.<st_input>")
                                                                                                                                                                        kl_X `pseq` applyWrapper aw_25 [kl_X])))
                                                                                                           let !appl_26 = ApplC (Func "lambda" (Context (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.nextline")))))
                                                                                                           let !aw_27 = Types.Atom (Types.UnboundSym "compile")
                                                                                                           !appl_28 <- appl_24 `pseq` (kl_V3694 `pseq` (appl_26 `pseq` applyWrapper aw_27 [appl_24,
                                                                                                                                                                                           kl_V3694,
                                                                                                                                                                                           appl_26]))
                                                                                                           appl_28 `pseq` applyWrapper appl_8 [appl_28]
                                                                                     Atom (B (False)) -> do do let !aw_29 = Types.Atom (Types.UnboundSym "stinput")
                                                                                                               !appl_30 <- applyWrapper aw_29 []
                                                                                                               !appl_31 <- appl_30 `pseq` readByte appl_30
                                                                                                               !appl_32 <- kl_V3693 `pseq` klCons kl_V3693 (Types.Atom Types.Nil)
                                                                                                               let !aw_33 = Types.Atom (Types.UnboundSym "append")
                                                                                                               !appl_34 <- kl_V3694 `pseq` (appl_32 `pseq` applyWrapper aw_33 [kl_V3694,
                                                                                                                                                                               appl_32])
                                                                                                               appl_31 `pseq` (appl_34 `pseq` kl_shen_toplineread_loop appl_31 appl_34)
                                                                                     _ -> throwError "if: expected boolean"
                                                          _ -> throwError "if: expected boolean"

kl_shen_hat :: Types.KLContext Types.Env Types.KLValue
kl_shen_hat = do return (Types.Atom (Types.N (Types.KI 94)))

kl_shen_newline :: Types.KLContext Types.Env Types.KLValue
kl_shen_newline = do return (Types.Atom (Types.N (Types.KI 10)))

kl_shen_carriage_return :: Types.KLContext Types.Env Types.KLValue
kl_shen_carriage_return = do return (Types.Atom (Types.N (Types.KI 13)))

kl_tc :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_tc (!kl_V3700) = do let pat_cond_0 = do klSet (Types.Atom (Types.UnboundSym "shen.*tc*")) (Atom (B True))
                           pat_cond_1 = do klSet (Types.Atom (Types.UnboundSym "shen.*tc*")) (Atom (B False))
                           pat_cond_2 = do do simpleError (Types.Atom (Types.Str "tc expects a + or -"))
                        in case kl_V3700 of
                               kl_V3700@(Atom (UnboundSym "+")) -> pat_cond_0
                               kl_V3700@(ApplC (PL "+" _)) -> pat_cond_0
                               kl_V3700@(ApplC (Func "+" _)) -> pat_cond_0
                               kl_V3700@(Atom (UnboundSym "-")) -> pat_cond_1
                               kl_V3700@(ApplC (PL "-" _)) -> pat_cond_1
                               kl_V3700@(ApplC (Func "-" _)) -> pat_cond_1
                               _ -> pat_cond_2

kl_shen_prompt :: Types.KLContext Types.Env Types.KLValue
kl_shen_prompt = do !kl_if_0 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                    case kl_if_0 of
                        Atom (B (True)) -> do !appl_1 <- value (Types.Atom (Types.UnboundSym "shen.*history*"))
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
                                                                                              appl_8])
                        Atom (B (False)) -> do do !appl_10 <- value (Types.Atom (Types.UnboundSym "shen.*history*"))
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
                                                                                                     appl_17])
                        _ -> throwError "if: expected boolean"

kl_shen_toplevel :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_toplevel (!kl_V3702) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                                  kl_V3702 `pseq` (appl_0 `pseq` kl_shen_toplevel_evaluate kl_V3702 appl_0)

kl_shen_find_past_inputs :: Types.KLValue ->
                            Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_find_past_inputs (!kl_V3705) (!kl_V3706) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_F) -> do let !aw_1 = Types.Atom (Types.UnboundSym "empty?")
                                                                                                                  !kl_if_2 <- kl_F `pseq` applyWrapper aw_1 [kl_F]
                                                                                                                  case kl_if_2 of
                                                                                                                      Atom (B (True)) -> do simpleError (Types.Atom (Types.Str "input not found\n"))
                                                                                                                      Atom (B (False)) -> do do return kl_F
                                                                                                                      _ -> throwError "if: expected boolean")))
                                                      !appl_3 <- kl_V3705 `pseq` (kl_V3706 `pseq` kl_shen_find kl_V3705 kl_V3706)
                                                      appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_make_key :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_make_key (!kl_V3709) (!kl_V3710) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Atom) -> do let !aw_1 = Types.Atom (Types.UnboundSym "integer?")
                                                                                                             !kl_if_2 <- kl_Atom `pseq` applyWrapper aw_1 [kl_Atom]
                                                                                                             case kl_if_2 of
                                                                                                                 Atom (B (True)) -> do return (ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_3 <- kl_Atom `pseq` add kl_Atom (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                             let !aw_4 = Types.Atom (Types.UnboundSym "reverse")
                                                                                                                                                                                             !appl_5 <- kl_V3710 `pseq` applyWrapper aw_4 [kl_V3710]
                                                                                                                                                                                             let !aw_6 = Types.Atom (Types.UnboundSym "nth")
                                                                                                                                                                                             !appl_7 <- appl_3 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_3,
                                                                                                                                                                                                                                                        appl_5])
                                                                                                                                                                                             kl_X `pseq` (appl_7 `pseq` eq kl_X appl_7)))))
                                                                                                                 Atom (B (False)) -> do do return (ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_8 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                                                                                 !appl_9 <- kl_X `pseq` applyWrapper aw_8 [kl_X]
                                                                                                                                                                                                 !appl_10 <- appl_9 `pseq` kl_shen_trim_gubbins appl_9
                                                                                                                                                                                                 kl_V3709 `pseq` (appl_10 `pseq` kl_shen_prefixP kl_V3709 appl_10)))))
                                                                                                                 _ -> throwError "if: expected boolean")))
                                              let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_12 = Types.Atom (Types.UnboundSym "shen.<st_input>")
                                                                                                           kl_X `pseq` applyWrapper aw_12 [kl_X])))
                                              let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_E) -> do let pat_cond_14 kl_E kl_Eh kl_Et = do let !aw_15 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                 !appl_16 <- kl_E `pseq` applyWrapper aw_15 [kl_E,
                                                                                                                                                                                             Types.Atom (Types.Str "\n"),
                                                                                                                                                                                             Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                                                 !appl_17 <- appl_16 `pseq` cn (Types.Atom (Types.Str "parse error here: ")) appl_16
                                                                                                                                                 appl_17 `pseq` simpleError appl_17
                                                                                                               pat_cond_18 = do do simpleError (Types.Atom (Types.Str "parse error\n"))
                                                                                                            in case kl_E of
                                                                                                                   !(kl_E@(Cons (!kl_Eh)
                                                                                                                                (!kl_Et))) -> pat_cond_14 kl_E kl_Eh kl_Et
                                                                                                                   _ -> pat_cond_18)))
                                              let !aw_19 = Types.Atom (Types.UnboundSym "compile")
                                              !appl_20 <- appl_11 `pseq` (kl_V3709 `pseq` (appl_13 `pseq` applyWrapper aw_19 [appl_11,
                                                                                                                              kl_V3709,
                                                                                                                              appl_13]))
                                              !appl_21 <- appl_20 `pseq` hd appl_20
                                              appl_21 `pseq` applyWrapper appl_0 [appl_21]

kl_shen_trim_gubbins :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_trim_gubbins (!kl_V3712) = do !kl_if_0 <- let pat_cond_1 kl_V3712 kl_V3712h kl_V3712t = do !appl_2 <- kl_shen_space
                                                                                                   !kl_if_3 <- kl_V3712h `pseq` (appl_2 `pseq` eq kl_V3712h appl_2)
                                                                                                   case kl_if_3 of
                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                       _ -> throwError "if: expected boolean"
                                                      pat_cond_4 = do do return (Atom (B False))
                                                   in case kl_V3712 of
                                                          !(kl_V3712@(Cons (!kl_V3712h)
                                                                           (!kl_V3712t))) -> pat_cond_1 kl_V3712 kl_V3712h kl_V3712t
                                                          _ -> pat_cond_4
                                      case kl_if_0 of
                                          Atom (B (True)) -> do !appl_5 <- kl_V3712 `pseq` tl kl_V3712
                                                                appl_5 `pseq` kl_shen_trim_gubbins appl_5
                                          Atom (B (False)) -> do !kl_if_6 <- let pat_cond_7 kl_V3712 kl_V3712h kl_V3712t = do !appl_8 <- kl_shen_newline
                                                                                                                              !kl_if_9 <- kl_V3712h `pseq` (appl_8 `pseq` eq kl_V3712h appl_8)
                                                                                                                              case kl_if_9 of
                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                 pat_cond_10 = do do return (Atom (B False))
                                                                              in case kl_V3712 of
                                                                                     !(kl_V3712@(Cons (!kl_V3712h)
                                                                                                      (!kl_V3712t))) -> pat_cond_7 kl_V3712 kl_V3712h kl_V3712t
                                                                                     _ -> pat_cond_10
                                                                 case kl_if_6 of
                                                                     Atom (B (True)) -> do !appl_11 <- kl_V3712 `pseq` tl kl_V3712
                                                                                           appl_11 `pseq` kl_shen_trim_gubbins appl_11
                                                                     Atom (B (False)) -> do !kl_if_12 <- let pat_cond_13 kl_V3712 kl_V3712h kl_V3712t = do !appl_14 <- kl_shen_carriage_return
                                                                                                                                                           !kl_if_15 <- kl_V3712h `pseq` (appl_14 `pseq` eq kl_V3712h appl_14)
                                                                                                                                                           case kl_if_15 of
                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                             pat_cond_16 = do do return (Atom (B False))
                                                                                                          in case kl_V3712 of
                                                                                                                 !(kl_V3712@(Cons (!kl_V3712h)
                                                                                                                                  (!kl_V3712t))) -> pat_cond_13 kl_V3712 kl_V3712h kl_V3712t
                                                                                                                 _ -> pat_cond_16
                                                                                            case kl_if_12 of
                                                                                                Atom (B (True)) -> do !appl_17 <- kl_V3712 `pseq` tl kl_V3712
                                                                                                                      appl_17 `pseq` kl_shen_trim_gubbins appl_17
                                                                                                Atom (B (False)) -> do !kl_if_18 <- let pat_cond_19 kl_V3712 kl_V3712h kl_V3712t = do !appl_20 <- kl_shen_tab
                                                                                                                                                                                      !kl_if_21 <- kl_V3712h `pseq` (appl_20 `pseq` eq kl_V3712h appl_20)
                                                                                                                                                                                      case kl_if_21 of
                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                        pat_cond_22 = do do return (Atom (B False))
                                                                                                                                     in case kl_V3712 of
                                                                                                                                            !(kl_V3712@(Cons (!kl_V3712h)
                                                                                                                                                             (!kl_V3712t))) -> pat_cond_19 kl_V3712 kl_V3712h kl_V3712t
                                                                                                                                            _ -> pat_cond_22
                                                                                                                       case kl_if_18 of
                                                                                                                           Atom (B (True)) -> do !appl_23 <- kl_V3712 `pseq` tl kl_V3712
                                                                                                                                                 appl_23 `pseq` kl_shen_trim_gubbins appl_23
                                                                                                                           Atom (B (False)) -> do !kl_if_24 <- let pat_cond_25 kl_V3712 kl_V3712h kl_V3712t = do !appl_26 <- kl_shen_left_round
                                                                                                                                                                                                                 !kl_if_27 <- kl_V3712h `pseq` (appl_26 `pseq` eq kl_V3712h appl_26)
                                                                                                                                                                                                                 case kl_if_27 of
                                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                   pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                in case kl_V3712 of
                                                                                                                                                                       !(kl_V3712@(Cons (!kl_V3712h)
                                                                                                                                                                                        (!kl_V3712t))) -> pat_cond_25 kl_V3712 kl_V3712h kl_V3712t
                                                                                                                                                                       _ -> pat_cond_28
                                                                                                                                                  case kl_if_24 of
                                                                                                                                                      Atom (B (True)) -> do !appl_29 <- kl_V3712 `pseq` tl kl_V3712
                                                                                                                                                                            appl_29 `pseq` kl_shen_trim_gubbins appl_29
                                                                                                                                                      Atom (B (False)) -> do do return kl_V3712
                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                _ -> throwError "if: expected boolean"
                                                                     _ -> throwError "if: expected boolean"
                                          _ -> throwError "if: expected boolean"

kl_shen_space :: Types.KLContext Types.Env Types.KLValue
kl_shen_space = do return (Types.Atom (Types.N (Types.KI 32)))

kl_shen_tab :: Types.KLContext Types.Env Types.KLValue
kl_shen_tab = do return (Types.Atom (Types.N (Types.KI 9)))

kl_shen_left_round :: Types.KLContext Types.Env Types.KLValue
kl_shen_left_round = do return (Types.Atom (Types.N (Types.KI 40)))

kl_shen_find :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_find (!kl_V3721) (!kl_V3722) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                              pat_cond_1 = do !kl_if_2 <- let pat_cond_3 kl_V3722 kl_V3722h kl_V3722t = do !kl_if_4 <- kl_V3722h `pseq` applyWrapper kl_V3721 [kl_V3722h]
                                                                                                                           case kl_if_4 of
                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                               _ -> throwError "if: expected boolean"
                                                                              pat_cond_5 = do do return (Atom (B False))
                                                                           in case kl_V3722 of
                                                                                  !(kl_V3722@(Cons (!kl_V3722h)
                                                                                                   (!kl_V3722t))) -> pat_cond_3 kl_V3722 kl_V3722h kl_V3722t
                                                                                  _ -> pat_cond_5
                                                              case kl_if_2 of
                                                                  Atom (B (True)) -> do !appl_6 <- kl_V3722 `pseq` hd kl_V3722
                                                                                        !appl_7 <- kl_V3722 `pseq` tl kl_V3722
                                                                                        !appl_8 <- kl_V3721 `pseq` (appl_7 `pseq` kl_shen_find kl_V3721 appl_7)
                                                                                        appl_6 `pseq` (appl_8 `pseq` klCons appl_6 appl_8)
                                                                  Atom (B (False)) -> do let pat_cond_9 kl_V3722 kl_V3722h kl_V3722t = do kl_V3721 `pseq` (kl_V3722t `pseq` kl_shen_find kl_V3721 kl_V3722t)
                                                                                             pat_cond_10 = do do let !aw_11 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                 applyWrapper aw_11 [ApplC (wrapNamed "shen.find" kl_shen_find)]
                                                                                          in case kl_V3722 of
                                                                                                 !(kl_V3722@(Cons (!kl_V3722h)
                                                                                                                  (!kl_V3722t))) -> pat_cond_9 kl_V3722 kl_V3722h kl_V3722t
                                                                                                 _ -> pat_cond_10
                                                                  _ -> throwError "if: expected boolean"
                                           in case kl_V3722 of
                                                  kl_V3722@(Atom (Nil)) -> pat_cond_0
                                                  _ -> pat_cond_1

kl_shen_prefixP :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_prefixP (!kl_V3736) (!kl_V3737) = do let pat_cond_0 = do return (Atom (B True))
                                                 pat_cond_1 = do !kl_if_2 <- let pat_cond_3 kl_V3736 kl_V3736h kl_V3736t = do let pat_cond_4 kl_V3737 kl_V3737h kl_V3737t = do return (Atom (B True))
                                                                                                                                  pat_cond_5 = do do return (Atom (B False))
                                                                                                                               in case kl_V3737 of
                                                                                                                                      !(kl_V3737@(Cons (!kl_V3737h)
                                                                                                                                                       (!kl_V3737t))) | eqCore kl_V3737h kl_V3736h -> pat_cond_4 kl_V3737 kl_V3737h kl_V3737t
                                                                                                                                      _ -> pat_cond_5
                                                                                 pat_cond_6 = do do return (Atom (B False))
                                                                              in case kl_V3736 of
                                                                                     !(kl_V3736@(Cons (!kl_V3736h)
                                                                                                      (!kl_V3736t))) -> pat_cond_3 kl_V3736 kl_V3736h kl_V3736t
                                                                                     _ -> pat_cond_6
                                                                 case kl_if_2 of
                                                                     Atom (B (True)) -> do !appl_7 <- kl_V3736 `pseq` tl kl_V3736
                                                                                           !appl_8 <- kl_V3737 `pseq` tl kl_V3737
                                                                                           appl_7 `pseq` (appl_8 `pseq` kl_shen_prefixP appl_7 appl_8)
                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                     _ -> throwError "if: expected boolean"
                                              in case kl_V3736 of
                                                     kl_V3736@(Atom (Nil)) -> pat_cond_0
                                                     _ -> pat_cond_1

kl_shen_print_past_inputs :: Types.KLValue ->
                             Types.KLValue ->
                             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_print_past_inputs (!kl_V3749) (!kl_V3750) (!kl_V3751) = do let pat_cond_0 = do return (Types.Atom (Types.UnboundSym "_"))
                                                                       pat_cond_1 = do !kl_if_2 <- let pat_cond_3 kl_V3750 kl_V3750h kl_V3750t = do !appl_4 <- kl_V3750h `pseq` applyWrapper kl_V3749 [kl_V3750h]
                                                                                                                                                    let !aw_5 = Types.Atom (Types.UnboundSym "not")
                                                                                                                                                    !kl_if_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4]
                                                                                                                                                    case kl_if_6 of
                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                       pat_cond_7 = do do return (Atom (B False))
                                                                                                    in case kl_V3750 of
                                                                                                           !(kl_V3750@(Cons (!kl_V3750h)
                                                                                                                            (!kl_V3750t))) -> pat_cond_3 kl_V3750 kl_V3750h kl_V3750t
                                                                                                           _ -> pat_cond_7
                                                                                       case kl_if_2 of
                                                                                           Atom (B (True)) -> do !appl_8 <- kl_V3750 `pseq` tl kl_V3750
                                                                                                                 !appl_9 <- kl_V3751 `pseq` add kl_V3751 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                 kl_V3749 `pseq` (appl_8 `pseq` (appl_9 `pseq` kl_shen_print_past_inputs kl_V3749 appl_8 appl_9))
                                                                                           Atom (B (False)) -> do !kl_if_10 <- let pat_cond_11 kl_V3750 kl_V3750h kl_V3750t = do let !aw_12 = Types.Atom (Types.UnboundSym "tuple?")
                                                                                                                                                                                 !kl_if_13 <- kl_V3750h `pseq` applyWrapper aw_12 [kl_V3750h]
                                                                                                                                                                                 case kl_if_13 of
                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                   pat_cond_14 = do do return (Atom (B False))
                                                                                                                                in case kl_V3750 of
                                                                                                                                       !(kl_V3750@(Cons (!kl_V3750h)
                                                                                                                                                        (!kl_V3750t))) -> pat_cond_11 kl_V3750 kl_V3750h kl_V3750t
                                                                                                                                       _ -> pat_cond_14
                                                                                                                  case kl_if_10 of
                                                                                                                      Atom (B (True)) -> do let !aw_15 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                            !appl_16 <- kl_V3751 `pseq` applyWrapper aw_15 [kl_V3751,
                                                                                                                                                                                            Types.Atom (Types.Str ". "),
                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                            let !aw_17 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                                                            !appl_18 <- applyWrapper aw_17 []
                                                                                                                                            let !aw_19 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                            !appl_20 <- appl_16 `pseq` (appl_18 `pseq` applyWrapper aw_19 [appl_16,
                                                                                                                                                                                                           appl_18])
                                                                                                                                            !appl_21 <- kl_V3750 `pseq` hd kl_V3750
                                                                                                                                            let !aw_22 = Types.Atom (Types.UnboundSym "snd")
                                                                                                                                            !appl_23 <- appl_21 `pseq` applyWrapper aw_22 [appl_21]
                                                                                                                                            !appl_24 <- appl_23 `pseq` kl_shen_prbytes appl_23
                                                                                                                                            !appl_25 <- kl_V3750 `pseq` tl kl_V3750
                                                                                                                                            !appl_26 <- kl_V3751 `pseq` add kl_V3751 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                            !appl_27 <- kl_V3749 `pseq` (appl_25 `pseq` (appl_26 `pseq` kl_shen_print_past_inputs kl_V3749 appl_25 appl_26))
                                                                                                                                            let !aw_28 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                            !appl_29 <- appl_24 `pseq` (appl_27 `pseq` applyWrapper aw_28 [appl_24,
                                                                                                                                                                                                           appl_27])
                                                                                                                                            let !aw_30 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                            appl_20 `pseq` (appl_29 `pseq` applyWrapper aw_30 [appl_20,
                                                                                                                                                                                               appl_29])
                                                                                                                      Atom (B (False)) -> do do let !aw_31 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                applyWrapper aw_31 [ApplC (wrapNamed "shen.print-past-inputs" kl_shen_print_past_inputs)]
                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                           _ -> throwError "if: expected boolean"
                                                                    in case kl_V3750 of
                                                                           kl_V3750@(Atom (Nil)) -> pat_cond_0
                                                                           _ -> pat_cond_1

kl_shen_toplevel_evaluate :: Types.KLValue ->
                             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_toplevel_evaluate (!kl_V3754) (!kl_V3755) = do !kl_if_0 <- let pat_cond_1 kl_V3754 kl_V3754h kl_V3754t = do !kl_if_2 <- let pat_cond_3 kl_V3754t kl_V3754th kl_V3754tt = do !kl_if_4 <- let pat_cond_5 = do !kl_if_6 <- let pat_cond_7 kl_V3754tt kl_V3754tth kl_V3754ttt = do !kl_if_8 <- let pat_cond_9 = do let pat_cond_10 = do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                           pat_cond_11 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                        in case kl_V3755 of
                                                                                                                                                                                                                                                                                                                               kl_V3755@(Atom (UnboundSym "true")) -> pat_cond_10
                                                                                                                                                                                                                                                                                                                               kl_V3755@(Atom (B (True))) -> pat_cond_10
                                                                                                                                                                                                                                                                                                                               _ -> pat_cond_11
                                                                                                                                                                                                                                                                                                       pat_cond_12 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                    in case kl_V3754ttt of
                                                                                                                                                                                                                                                                                                           kl_V3754ttt@(Atom (Nil)) -> pat_cond_9
                                                                                                                                                                                                                                                                                                           _ -> pat_cond_12
                                                                                                                                                                                                                                                                                       case kl_if_8 of
                                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                    pat_cond_13 = do do return (Atom (B False))
                                                                                                                                                                                                                                 in case kl_V3754tt of
                                                                                                                                                                                                                                        !(kl_V3754tt@(Cons (!kl_V3754tth)
                                                                                                                                                                                                                                                           (!kl_V3754ttt))) -> pat_cond_7 kl_V3754tt kl_V3754tth kl_V3754ttt
                                                                                                                                                                                                                                        _ -> pat_cond_13
                                                                                                                                                                                                                    case kl_if_6 of
                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                    pat_cond_14 = do do return (Atom (B False))
                                                                                                                                                                                                 in case kl_V3754th of
                                                                                                                                                                                                        kl_V3754th@(Atom (UnboundSym ":")) -> pat_cond_5
                                                                                                                                                                                                        kl_V3754th@(ApplC (PL ":"
                                                                                                                                                                                                                              _)) -> pat_cond_5
                                                                                                                                                                                                        kl_V3754th@(ApplC (Func ":"
                                                                                                                                                                                                                                _)) -> pat_cond_5
                                                                                                                                                                                                        _ -> pat_cond_14
                                                                                                                                                                                    case kl_if_4 of
                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                    pat_cond_15 = do do return (Atom (B False))
                                                                                                                                 in case kl_V3754t of
                                                                                                                                        !(kl_V3754t@(Cons (!kl_V3754th)
                                                                                                                                                          (!kl_V3754tt))) -> pat_cond_3 kl_V3754t kl_V3754th kl_V3754tt
                                                                                                                                        _ -> pat_cond_15
                                                                                                                    case kl_if_2 of
                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                        _ -> throwError "if: expected boolean"
                                                                       pat_cond_16 = do do return (Atom (B False))
                                                                    in case kl_V3754 of
                                                                           !(kl_V3754@(Cons (!kl_V3754h)
                                                                                            (!kl_V3754t))) -> pat_cond_1 kl_V3754 kl_V3754h kl_V3754t
                                                                           _ -> pat_cond_16
                                                       case kl_if_0 of
                                                           Atom (B (True)) -> do !appl_17 <- kl_V3754 `pseq` hd kl_V3754
                                                                                 !appl_18 <- kl_V3754 `pseq` tl kl_V3754
                                                                                 !appl_19 <- appl_18 `pseq` tl appl_18
                                                                                 !appl_20 <- appl_19 `pseq` hd appl_19
                                                                                 appl_17 `pseq` (appl_20 `pseq` kl_shen_typecheck_and_evaluate appl_17 appl_20)
                                                           Atom (B (False)) -> do let pat_cond_21 kl_V3754 kl_V3754h kl_V3754t kl_V3754th kl_V3754tt = do !appl_22 <- kl_V3754h `pseq` klCons kl_V3754h (Types.Atom Types.Nil)
                                                                                                                                                          !appl_23 <- appl_22 `pseq` (kl_V3755 `pseq` kl_shen_toplevel_evaluate appl_22 kl_V3755)
                                                                                                                                                          let !aw_24 = Types.Atom (Types.UnboundSym "nl")
                                                                                                                                                          !appl_25 <- applyWrapper aw_24 [Types.Atom (Types.N (Types.KI 1))]
                                                                                                                                                          !appl_26 <- kl_V3754t `pseq` (kl_V3755 `pseq` kl_shen_toplevel_evaluate kl_V3754t kl_V3755)
                                                                                                                                                          let !aw_27 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                          !appl_28 <- appl_25 `pseq` (appl_26 `pseq` applyWrapper aw_27 [appl_25,
                                                                                                                                                                                                                         appl_26])
                                                                                                                                                          let !aw_29 = Types.Atom (Types.UnboundSym "do")
                                                                                                                                                          appl_23 `pseq` (appl_28 `pseq` applyWrapper aw_29 [appl_23,
                                                                                                                                                                                                             appl_28])
                                                                                      pat_cond_30 = do !kl_if_31 <- let pat_cond_32 kl_V3754 kl_V3754h kl_V3754t = do !kl_if_33 <- let pat_cond_34 = do let pat_cond_35 = do return (Atom (B True))
                                                                                                                                                                                                            pat_cond_36 = do do return (Atom (B False))
                                                                                                                                                                                                         in case kl_V3755 of
                                                                                                                                                                                                                kl_V3755@(Atom (UnboundSym "true")) -> pat_cond_35
                                                                                                                                                                                                                kl_V3755@(Atom (B (True))) -> pat_cond_35
                                                                                                                                                                                                                _ -> pat_cond_36
                                                                                                                                                                                       pat_cond_37 = do do return (Atom (B False))
                                                                                                                                                                                    in case kl_V3754t of
                                                                                                                                                                                           kl_V3754t@(Atom (Nil)) -> pat_cond_34
                                                                                                                                                                                           _ -> pat_cond_37
                                                                                                                                                                      case kl_if_33 of
                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                        pat_cond_38 = do do return (Atom (B False))
                                                                                                                     in case kl_V3754 of
                                                                                                                            !(kl_V3754@(Cons (!kl_V3754h)
                                                                                                                                             (!kl_V3754t))) -> pat_cond_32 kl_V3754 kl_V3754h kl_V3754t
                                                                                                                            _ -> pat_cond_38
                                                                                                       case kl_if_31 of
                                                                                                           Atom (B (True)) -> do !appl_39 <- kl_V3754 `pseq` hd kl_V3754
                                                                                                                                 let !aw_40 = Types.Atom (Types.UnboundSym "gensym")
                                                                                                                                 !appl_41 <- applyWrapper aw_40 [Types.Atom (Types.UnboundSym "A")]
                                                                                                                                 appl_39 `pseq` (appl_41 `pseq` kl_shen_typecheck_and_evaluate appl_39 appl_41)
                                                                                                           Atom (B (False)) -> do !kl_if_42 <- let pat_cond_43 kl_V3754 kl_V3754h kl_V3754t = do !kl_if_44 <- let pat_cond_45 = do let pat_cond_46 = do return (Atom (B True))
                                                                                                                                                                                                                                       pat_cond_47 = do do return (Atom (B False))
                                                                                                                                                                                                                                    in case kl_V3755 of
                                                                                                                                                                                                                                           kl_V3755@(Atom (UnboundSym "false")) -> pat_cond_46
                                                                                                                                                                                                                                           kl_V3755@(Atom (B (False))) -> pat_cond_46
                                                                                                                                                                                                                                           _ -> pat_cond_47
                                                                                                                                                                                                                  pat_cond_48 = do do return (Atom (B False))
                                                                                                                                                                                                               in case kl_V3754t of
                                                                                                                                                                                                                      kl_V3754t@(Atom (Nil)) -> pat_cond_45
                                                                                                                                                                                                                      _ -> pat_cond_48
                                                                                                                                                                                                 case kl_if_44 of
                                                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                   pat_cond_49 = do do return (Atom (B False))
                                                                                                                                                in case kl_V3754 of
                                                                                                                                                       !(kl_V3754@(Cons (!kl_V3754h)
                                                                                                                                                                        (!kl_V3754t))) -> pat_cond_43 kl_V3754 kl_V3754h kl_V3754t
                                                                                                                                                       _ -> pat_cond_49
                                                                                                                                  case kl_if_42 of
                                                                                                                                      Atom (B (True)) -> do let !appl_50 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do let !aw_51 = Types.Atom (Types.UnboundSym "print")
                                                                                                                                                                                                                            kl_Eval `pseq` applyWrapper aw_51 [kl_Eval])))
                                                                                                                                                            !appl_52 <- kl_V3754 `pseq` hd kl_V3754
                                                                                                                                                            let !aw_53 = Types.Atom (Types.UnboundSym "shen.eval-without-macros")
                                                                                                                                                            !appl_54 <- appl_52 `pseq` applyWrapper aw_53 [appl_52]
                                                                                                                                                            appl_54 `pseq` applyWrapper appl_50 [appl_54]
                                                                                                                                      Atom (B (False)) -> do do let !aw_55 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                                                applyWrapper aw_55 [ApplC (wrapNamed "shen.toplevel_evaluate" kl_shen_toplevel_evaluate)]
                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                           _ -> throwError "if: expected boolean"
                                                                                   in case kl_V3754 of
                                                                                          !(kl_V3754@(Cons (!kl_V3754h)
                                                                                                           (!(kl_V3754t@(Cons (!kl_V3754th)
                                                                                                                              (!kl_V3754tt)))))) -> pat_cond_21 kl_V3754 kl_V3754h kl_V3754t kl_V3754th kl_V3754tt
                                                                                          _ -> pat_cond_30
                                                           _ -> throwError "if: expected boolean"

kl_shen_typecheck_and_evaluate :: Types.KLValue ->
                                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_typecheck_and_evaluate (!kl_V3758) (!kl_V3759) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Typecheck) -> do let pat_cond_1 = do simpleError (Types.Atom (Types.Str "type error\n"))
                                                                                                                                    pat_cond_2 = do do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Type) -> do let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                     !appl_6 <- kl_Type `pseq` applyWrapper aw_5 [kl_Type,
                                                                                                                                                                                                                                                                                                                                  Types.Atom (Types.Str ""),
                                                                                                                                                                                                                                                                                                                                  Types.Atom (Types.UnboundSym "shen.r")]
                                                                                                                                                                                                                                                                                     !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str " : ")) appl_6
                                                                                                                                                                                                                                                                                     let !aw_8 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                     !appl_9 <- kl_Eval `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_Eval,
                                                                                                                                                                                                                                                                                                                                                 appl_7,
                                                                                                                                                                                                                                                                                                                                                 Types.Atom (Types.UnboundSym "shen.s")])
                                                                                                                                                                                                                                                                                     let !aw_10 = Types.Atom (Types.UnboundSym "stoutput")
                                                                                                                                                                                                                                                                                     !appl_11 <- applyWrapper aw_10 []
                                                                                                                                                                                                                                                                                     let !aw_12 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                                     appl_9 `pseq` (appl_11 `pseq` applyWrapper aw_12 [appl_9,
                                                                                                                                                                                                                                                                                                                                       appl_11]))))
                                                                                                                                                                                                                      !appl_13 <- kl_Typecheck `pseq` kl_shen_pretty_type kl_Typecheck
                                                                                                                                                                                                                      appl_13 `pseq` applyWrapper appl_4 [appl_13])))
                                                                                                                                                       let !aw_14 = Types.Atom (Types.UnboundSym "shen.eval-without-macros")
                                                                                                                                                       !appl_15 <- kl_V3758 `pseq` applyWrapper aw_14 [kl_V3758]
                                                                                                                                                       appl_15 `pseq` applyWrapper appl_3 [appl_15]
                                                                                                                                 in case kl_Typecheck of
                                                                                                                                        kl_Typecheck@(Atom (UnboundSym "false")) -> pat_cond_1
                                                                                                                                        kl_Typecheck@(Atom (B (False))) -> pat_cond_1
                                                                                                                                        _ -> pat_cond_2)))
                                                            let !aw_16 = Types.Atom (Types.UnboundSym "shen.typecheck")
                                                            !appl_17 <- kl_V3758 `pseq` (kl_V3759 `pseq` applyWrapper aw_16 [kl_V3758,
                                                                                                                             kl_V3759])
                                                            appl_17 `pseq` applyWrapper appl_0 [appl_17]

kl_shen_pretty_type :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_pretty_type (!kl_V3761) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*alphabet*"))
                                     !appl_1 <- kl_V3761 `pseq` kl_shen_extract_pvars kl_V3761
                                     appl_0 `pseq` (appl_1 `pseq` (kl_V3761 `pseq` kl_shen_mult_subst appl_0 appl_1 kl_V3761))

kl_shen_extract_pvars :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_extract_pvars (!kl_V3767) = do let !aw_0 = Types.Atom (Types.UnboundSym "shen.pvar?")
                                       !kl_if_1 <- kl_V3767 `pseq` applyWrapper aw_0 [kl_V3767]
                                       case kl_if_1 of
                                           Atom (B (True)) -> do kl_V3767 `pseq` klCons kl_V3767 (Types.Atom Types.Nil)
                                           Atom (B (False)) -> do let pat_cond_2 kl_V3767 kl_V3767h kl_V3767t = do !appl_3 <- kl_V3767h `pseq` kl_shen_extract_pvars kl_V3767h
                                                                                                                   !appl_4 <- kl_V3767t `pseq` kl_shen_extract_pvars kl_V3767t
                                                                                                                   let !aw_5 = Types.Atom (Types.UnboundSym "union")
                                                                                                                   appl_3 `pseq` (appl_4 `pseq` applyWrapper aw_5 [appl_3,
                                                                                                                                                                   appl_4])
                                                                      pat_cond_6 = do do return (Types.Atom Types.Nil)
                                                                   in case kl_V3767 of
                                                                          !(kl_V3767@(Cons (!kl_V3767h)
                                                                                           (!kl_V3767t))) -> pat_cond_2 kl_V3767 kl_V3767h kl_V3767t
                                                                          _ -> pat_cond_6
                                           _ -> throwError "if: expected boolean"

kl_shen_mult_subst :: Types.KLValue ->
                      Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mult_subst (!kl_V3775) (!kl_V3776) (!kl_V3777) = do let pat_cond_0 = do return kl_V3777
                                                                pat_cond_1 = do let pat_cond_2 = do return kl_V3777
                                                                                    pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V3775 kl_V3775h kl_V3775t = do let pat_cond_6 kl_V3776 kl_V3776h kl_V3776t = do return (Atom (B True))
                                                                                                                                                                     pat_cond_7 = do do return (Atom (B False))
                                                                                                                                                                  in case kl_V3776 of
                                                                                                                                                                         !(kl_V3776@(Cons (!kl_V3776h)
                                                                                                                                                                                          (!kl_V3776t))) -> pat_cond_6 kl_V3776 kl_V3776h kl_V3776t
                                                                                                                                                                         _ -> pat_cond_7
                                                                                                                    pat_cond_8 = do do return (Atom (B False))
                                                                                                                 in case kl_V3775 of
                                                                                                                        !(kl_V3775@(Cons (!kl_V3775h)
                                                                                                                                         (!kl_V3775t))) -> pat_cond_5 kl_V3775 kl_V3775h kl_V3775t
                                                                                                                        _ -> pat_cond_8
                                                                                                    case kl_if_4 of
                                                                                                        Atom (B (True)) -> do !appl_9 <- kl_V3775 `pseq` tl kl_V3775
                                                                                                                              !appl_10 <- kl_V3776 `pseq` tl kl_V3776
                                                                                                                              !appl_11 <- kl_V3775 `pseq` hd kl_V3775
                                                                                                                              !appl_12 <- kl_V3776 `pseq` hd kl_V3776
                                                                                                                              let !aw_13 = Types.Atom (Types.UnboundSym "subst")
                                                                                                                              !appl_14 <- appl_11 `pseq` (appl_12 `pseq` (kl_V3777 `pseq` applyWrapper aw_13 [appl_11,
                                                                                                                                                                                                              appl_12,
                                                                                                                                                                                                              kl_V3777]))
                                                                                                                              appl_9 `pseq` (appl_10 `pseq` (appl_14 `pseq` kl_shen_mult_subst appl_9 appl_10 appl_14))
                                                                                                        Atom (B (False)) -> do do let !aw_15 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                  applyWrapper aw_15 [ApplC (wrapNamed "shen.mult_subst" kl_shen_mult_subst)]
                                                                                                        _ -> throwError "if: expected boolean"
                                                                                 in case kl_V3776 of
                                                                                        kl_V3776@(Atom (Nil)) -> pat_cond_2
                                                                                        _ -> pat_cond_3
                                                             in case kl_V3775 of
                                                                    kl_V3775@(Atom (Nil)) -> pat_cond_0
                                                                    _ -> pat_cond_1

expr0 :: Types.KLContext Types.Env Types.KLValue
expr0 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
           (do klSet (Types.Atom (Types.UnboundSym "shen.*history*")) (Types.Atom Types.Nil)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
