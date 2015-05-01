{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Backend.Types where

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

kl_declare :: Types.KLValue ->
              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_declare (!kl_V3854) (!kl_V3855) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Record) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Variancy) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Type) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_FMult) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parameters) -> do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_Clause) -> do let !appl_6 = ApplC (Func "lambda" (Context (\(!kl_AUM_instruction) -> do let !appl_7 = ApplC (Func "lambda" (Context (\(!kl_Code) -> do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_ShenDef) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do return kl_V3854)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            !appl_10 <- kl_ShenDef `pseq` kl_shen_eval_without_macros kl_ShenDef
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            appl_10 `pseq` applyWrapper appl_9 [appl_10])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_11 <- klCons (Types.Atom (Types.UnboundSym "Continuation")) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "ProcessN")) appl_11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_13 <- kl_Code `pseq` klCons kl_Code (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_13
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_15 <- appl_12 `pseq` (appl_14 `pseq` kl_append appl_12 appl_14)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_16 <- kl_Parameters `pseq` (appl_15 `pseq` kl_append kl_Parameters appl_15)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_17 <- kl_FMult `pseq` (appl_16 `pseq` klCons kl_FMult appl_16)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_17
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          appl_18 `pseq` applyWrapper appl_8 [appl_18])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !appl_19 <- kl_AUM_instruction `pseq` kl_shen_aum_to_shen kl_AUM_instruction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           appl_19 `pseq` applyWrapper appl_7 [appl_19])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                 !appl_20 <- kl_Clause `pseq` (kl_Parameters `pseq` kl_shen_aum kl_Clause kl_Parameters)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 appl_20 `pseq` applyWrapper appl_6 [appl_20])))
                                                                                                                                                                                                                                                                                                                                                                                !appl_21 <- klCons (Types.Atom (Types.UnboundSym "X")) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                                                                !appl_22 <- kl_FMult `pseq` (appl_21 `pseq` klCons kl_FMult appl_21)
                                                                                                                                                                                                                                                                                                                                                                                !appl_23 <- kl_Type `pseq` klCons kl_Type (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                                                                !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_23
                                                                                                                                                                                                                                                                                                                                                                                !appl_25 <- appl_24 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_24
                                                                                                                                                                                                                                                                                                                                                                                !appl_26 <- appl_25 `pseq` klCons appl_25 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                                                                !appl_27 <- appl_26 `pseq` klCons appl_26 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                                                                !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.UnboundSym ":-")) appl_27
                                                                                                                                                                                                                                                                                                                                                                                !appl_29 <- appl_22 `pseq` (appl_28 `pseq` klCons appl_22 appl_28)
                                                                                                                                                                                                                                                                                                                                                                                appl_29 `pseq` applyWrapper appl_5 [appl_29])))
                                                                                                                                                                                                                                                                                                           !appl_30 <- kl_shen_parameters (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                                                           appl_30 `pseq` applyWrapper appl_4 [appl_30])))
                                                                                                                                                                                                                                           !appl_31 <- kl_V3854 `pseq` kl_concat (Types.Atom (Types.UnboundSym "shen.type-signature-of-")) kl_V3854
                                                                                                                                                                                                                                           appl_31 `pseq` applyWrapper appl_3 [appl_31])))
                                                                                                                                                                            !appl_32 <- kl_V3855 `pseq` kl_shen_demodulate kl_V3855
                                                                                                                                                                            !appl_33 <- appl_32 `pseq` kl_shen_rcons_form appl_32
                                                                                                                                                                            appl_33 `pseq` applyWrapper appl_2 [appl_33])))
                                                                                                         !appl_34 <- (do kl_V3854 `pseq` (kl_V3855 `pseq` kl_shen_variancy_test kl_V3854 kl_V3855)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.skip")))
                                                                                                         appl_34 `pseq` applyWrapper appl_1 [appl_34])))
                                        !appl_35 <- kl_V3854 `pseq` (kl_V3855 `pseq` klCons kl_V3854 kl_V3855)
                                        !appl_36 <- value (Types.Atom (Types.UnboundSym "shen.*signedfuncs*"))
                                        !appl_37 <- appl_35 `pseq` (appl_36 `pseq` klCons appl_35 appl_36)
                                        !appl_38 <- appl_37 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*signedfuncs*")) appl_37
                                        appl_38 `pseq` applyWrapper appl_0 [appl_38]

kl_shen_demodulate :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_demodulate (!kl_V3857) = do (do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Demod) -> do !kl_if_1 <- kl_Demod `pseq` (kl_V3857 `pseq` eq kl_Demod kl_V3857)
                                                                                                        case kl_if_1 of
                                                                                                            Atom (B (True)) -> do return kl_V3857
                                                                                                            Atom (B (False)) -> do do kl_Demod `pseq` kl_shen_demodulate kl_Demod
                                                                                                            _ -> throwError "if: expected boolean")))
                                        let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do let !aw_3 = Types.Atom (Types.UnboundSym "shen.demod")
                                                                                                    kl_Y `pseq` applyWrapper aw_3 [kl_Y])))
                                        !appl_4 <- appl_2 `pseq` (kl_V3857 `pseq` kl_shen_walk appl_2 kl_V3857)
                                        appl_4 `pseq` applyWrapper appl_0 [appl_4]) `catchError` (\(!kl_E) -> do return kl_V3857)

kl_shen_variancy_test :: Types.KLValue ->
                         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_variancy_test (!kl_V3860) (!kl_V3861) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_TypeF) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Check) -> do return (Types.Atom (Types.UnboundSym "shen.skip")))))
                                                                                                                   !appl_2 <- let pat_cond_3 = do return (Types.Atom (Types.UnboundSym "shen.skip"))
                                                                                                                                  pat_cond_4 = do do !kl_if_5 <- kl_TypeF `pseq` (kl_V3861 `pseq` kl_shen_variantP kl_TypeF kl_V3861)
                                                                                                                                                     case kl_if_5 of
                                                                                                                                                         Atom (B (True)) -> do return (Types.Atom (Types.UnboundSym "shen.skip"))
                                                                                                                                                         Atom (B (False)) -> do do !appl_6 <- kl_V3860 `pseq` kl_shen_app kl_V3860 (Types.Atom (Types.Str " may create errors\n")) (Types.Atom (Types.UnboundSym "shen.a"))
                                                                                                                                                                                   !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str "warning: changing the type of ")) appl_6
                                                                                                                                                                                   !appl_8 <- kl_stoutput
                                                                                                                                                                                   appl_7 `pseq` (appl_8 `pseq` kl_shen_prhush appl_7 appl_8)
                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                               in case kl_TypeF of
                                                                                                                                      kl_TypeF@(Atom (UnboundSym "symbol")) -> pat_cond_3
                                                                                                                                      kl_TypeF@(ApplC (PL "symbol"
                                                                                                                                                          _)) -> pat_cond_3
                                                                                                                                      kl_TypeF@(ApplC (Func "symbol"
                                                                                                                                                            _)) -> pat_cond_3
                                                                                                                                      _ -> pat_cond_4
                                                                                                                   appl_2 `pseq` applyWrapper appl_1 [appl_2])))
                                                   let !aw_9 = Types.Atom (Types.UnboundSym "shen.typecheck")
                                                   !appl_10 <- kl_V3860 `pseq` applyWrapper aw_9 [kl_V3860,
                                                                                                  Types.Atom (Types.UnboundSym "B")]
                                                   appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_variantP :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_variantP (!kl_V3874) (!kl_V3875) = do !kl_if_0 <- kl_V3875 `pseq` (kl_V3874 `pseq` eq kl_V3875 kl_V3874)
                                              case kl_if_0 of
                                                  Atom (B (True)) -> do return (Atom (B True))
                                                  Atom (B (False)) -> do !kl_if_1 <- let pat_cond_2 kl_V3874 kl_V3874h kl_V3874t = do let pat_cond_3 kl_V3875 kl_V3875h kl_V3875t = do return (Atom (B True))
                                                                                                                                          pat_cond_4 = do do return (Atom (B False))
                                                                                                                                       in case kl_V3875 of
                                                                                                                                              !(kl_V3875@(Cons (!kl_V3875h)
                                                                                                                                                               (!kl_V3875t))) | eqCore kl_V3875h kl_V3874h -> pat_cond_3 kl_V3875 kl_V3875h kl_V3875t
                                                                                                                                              _ -> pat_cond_4
                                                                                         pat_cond_5 = do do return (Atom (B False))
                                                                                      in case kl_V3874 of
                                                                                             !(kl_V3874@(Cons (!kl_V3874h)
                                                                                                              (!kl_V3874t))) -> pat_cond_2 kl_V3874 kl_V3874h kl_V3874t
                                                                                             _ -> pat_cond_5
                                                                         case kl_if_1 of
                                                                             Atom (B (True)) -> do !appl_6 <- kl_V3874 `pseq` tl kl_V3874
                                                                                                   !appl_7 <- kl_V3875 `pseq` tl kl_V3875
                                                                                                   appl_6 `pseq` (appl_7 `pseq` kl_shen_variantP appl_6 appl_7)
                                                                             Atom (B (False)) -> do !kl_if_8 <- let pat_cond_9 kl_V3874 kl_V3874h kl_V3874t = do !kl_if_10 <- let pat_cond_11 kl_V3875 kl_V3875h kl_V3875t = do !kl_if_12 <- kl_V3874h `pseq` kl_shen_pvarP kl_V3874h
                                                                                                                                                                                                                                !kl_if_13 <- case kl_if_12 of
                                                                                                                                                                                                                                                 Atom (B (True)) -> do !kl_if_14 <- kl_V3875h `pseq` kl_variableP kl_V3875h
                                                                                                                                                                                                                                                                       case kl_if_14 of
                                                                                                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                case kl_if_13 of
                                                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                                  pat_cond_15 = do do return (Atom (B False))
                                                                                                                                                                               in case kl_V3875 of
                                                                                                                                                                                      !(kl_V3875@(Cons (!kl_V3875h)
                                                                                                                                                                                                       (!kl_V3875t))) -> pat_cond_11 kl_V3875 kl_V3875h kl_V3875t
                                                                                                                                                                                      _ -> pat_cond_15
                                                                                                                                                                 case kl_if_10 of
                                                                                                                                                                     Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                    pat_cond_16 = do do return (Atom (B False))
                                                                                                                 in case kl_V3874 of
                                                                                                                        !(kl_V3874@(Cons (!kl_V3874h)
                                                                                                                                         (!kl_V3874t))) -> pat_cond_9 kl_V3874 kl_V3874h kl_V3874t
                                                                                                                        _ -> pat_cond_16
                                                                                                    case kl_if_8 of
                                                                                                        Atom (B (True)) -> do !appl_17 <- kl_V3874 `pseq` hd kl_V3874
                                                                                                                              !appl_18 <- kl_V3874 `pseq` tl kl_V3874
                                                                                                                              !appl_19 <- appl_17 `pseq` (appl_18 `pseq` kl_subst (Types.Atom (Types.UnboundSym "shen.a")) appl_17 appl_18)
                                                                                                                              !appl_20 <- kl_V3875 `pseq` hd kl_V3875
                                                                                                                              !appl_21 <- kl_V3875 `pseq` tl kl_V3875
                                                                                                                              !appl_22 <- appl_20 `pseq` (appl_21 `pseq` kl_subst (Types.Atom (Types.UnboundSym "shen.a")) appl_20 appl_21)
                                                                                                                              appl_19 `pseq` (appl_22 `pseq` kl_shen_variantP appl_19 appl_22)
                                                                                                        Atom (B (False)) -> do !kl_if_23 <- let pat_cond_24 kl_V3874 kl_V3874h kl_V3874t = do !kl_if_25 <- let pat_cond_26 kl_V3874h kl_V3874hh kl_V3874ht = do let pat_cond_27 kl_V3875 kl_V3875h kl_V3875hh kl_V3875ht kl_V3875t = do return (Atom (B True))
                                                                                                                                                                                                                                                                    pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                 in case kl_V3875 of
                                                                                                                                                                                                                                                                        !(kl_V3875@(Cons (!(kl_V3875h@(Cons (!kl_V3875hh)
                                                                                                                                                                                                                                                                                                            (!kl_V3875ht))))
                                                                                                                                                                                                                                                                                         (!kl_V3875t))) -> pat_cond_27 kl_V3875 kl_V3875h kl_V3875hh kl_V3875ht kl_V3875t
                                                                                                                                                                                                                                                                        _ -> pat_cond_28
                                                                                                                                                                                                               pat_cond_29 = do do return (Atom (B False))
                                                                                                                                                                                                            in case kl_V3874h of
                                                                                                                                                                                                                   !(kl_V3874h@(Cons (!kl_V3874hh)
                                                                                                                                                                                                                                     (!kl_V3874ht))) -> pat_cond_26 kl_V3874h kl_V3874hh kl_V3874ht
                                                                                                                                                                                                                   _ -> pat_cond_29
                                                                                                                                                                                              case kl_if_25 of
                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                pat_cond_30 = do do return (Atom (B False))
                                                                                                                                             in case kl_V3874 of
                                                                                                                                                    !(kl_V3874@(Cons (!kl_V3874h)
                                                                                                                                                                     (!kl_V3874t))) -> pat_cond_24 kl_V3874 kl_V3874h kl_V3874t
                                                                                                                                                    _ -> pat_cond_30
                                                                                                                               case kl_if_23 of
                                                                                                                                   Atom (B (True)) -> do !appl_31 <- kl_V3874 `pseq` hd kl_V3874
                                                                                                                                                         !appl_32 <- kl_V3874 `pseq` tl kl_V3874
                                                                                                                                                         !appl_33 <- appl_31 `pseq` (appl_32 `pseq` kl_append appl_31 appl_32)
                                                                                                                                                         !appl_34 <- kl_V3875 `pseq` hd kl_V3875
                                                                                                                                                         !appl_35 <- kl_V3875 `pseq` tl kl_V3875
                                                                                                                                                         !appl_36 <- appl_34 `pseq` (appl_35 `pseq` kl_append appl_34 appl_35)
                                                                                                                                                         appl_33 `pseq` (appl_36 `pseq` kl_shen_variantP appl_33 appl_36)
                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                        _ -> throwError "if: expected boolean"
                                                                             _ -> throwError "if: expected boolean"
                                                  _ -> throwError "if: expected boolean"

expr12 :: Types.KLContext Types.Env Types.KLValue
expr12 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_0 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_0
                !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_1
                appl_2 `pseq` kl_declare (ApplC (wrapNamed "absvector?" absvectorP)) appl_2) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_3 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_3
                !appl_5 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_5
                !appl_7 <- appl_6 `pseq` klCons appl_6 (Types.Atom Types.Nil)
                !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_7
                !appl_9 <- appl_4 `pseq` (appl_8 `pseq` klCons appl_4 appl_8)
                !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_10
                !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_11
                appl_12 `pseq` kl_declare (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_12) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_13 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_13
                !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_14
                !appl_16 <- appl_15 `pseq` klCons appl_15 (Types.Atom Types.Nil)
                !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_16
                !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_17
                appl_18 `pseq` kl_declare (Types.Atom (Types.UnboundSym "and")) appl_18) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_19 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_19
                !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_20
                !appl_22 <- appl_21 `pseq` klCons appl_21 (Types.Atom Types.Nil)
                !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_22
                !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_23
                !appl_25 <- appl_24 `pseq` klCons appl_24 (Types.Atom Types.Nil)
                !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_25
                !appl_27 <- appl_26 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_26
                appl_27 `pseq` kl_declare (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_27) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_28 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_28
                !appl_30 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_30
                !appl_32 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_33 <- appl_32 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_32
                !appl_34 <- appl_33 `pseq` klCons appl_33 (Types.Atom Types.Nil)
                !appl_35 <- appl_34 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_34
                !appl_36 <- appl_31 `pseq` (appl_35 `pseq` klCons appl_31 appl_35)
                !appl_37 <- appl_36 `pseq` klCons appl_36 (Types.Atom Types.Nil)
                !appl_38 <- appl_37 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_37
                !appl_39 <- appl_29 `pseq` (appl_38 `pseq` klCons appl_29 appl_38)
                appl_39 `pseq` kl_declare (ApplC (wrapNamed "append" kl_append)) appl_39) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_40 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_41 <- appl_40 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_40
                !appl_42 <- appl_41 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_41
                appl_42 `pseq` kl_declare (ApplC (wrapNamed "arity" kl_arity)) appl_42) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_43 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_44 <- appl_43 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_43
                !appl_45 <- appl_44 `pseq` klCons appl_44 (Types.Atom Types.Nil)
                !appl_46 <- appl_45 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_45
                !appl_47 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_48 <- appl_47 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_47
                !appl_49 <- appl_48 `pseq` klCons appl_48 (Types.Atom Types.Nil)
                !appl_50 <- appl_49 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_49
                !appl_51 <- appl_46 `pseq` (appl_50 `pseq` klCons appl_46 appl_50)
                !appl_52 <- appl_51 `pseq` klCons appl_51 (Types.Atom Types.Nil)
                !appl_53 <- appl_52 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_52
                !appl_54 <- appl_53 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_53
                appl_54 `pseq` kl_declare (ApplC (wrapNamed "assoc" kl_assoc)) appl_54) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_55 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_56 <- appl_55 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_55
                !appl_57 <- appl_56 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_56
                appl_57 `pseq` kl_declare (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_57) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_58 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_59 <- appl_58 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_58
                !appl_60 <- appl_59 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_59
                appl_60 `pseq` kl_declare (ApplC (wrapNamed "bound?" kl_boundP)) appl_60) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_61 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_62 <- appl_61 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_61
                !appl_63 <- appl_62 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_62
                appl_63 `pseq` kl_declare (ApplC (wrapNamed "cd" kl_cd)) appl_63) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_64 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_65 <- appl_64 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_64
                !appl_66 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_67 <- appl_66 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_66
                !appl_68 <- appl_67 `pseq` klCons appl_67 (Types.Atom Types.Nil)
                !appl_69 <- appl_68 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_68
                !appl_70 <- appl_65 `pseq` (appl_69 `pseq` klCons appl_65 appl_69)
                appl_70 `pseq` kl_declare (ApplC (wrapNamed "close" closeStream)) appl_70) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_71 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_72 <- appl_71 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_71
                !appl_73 <- appl_72 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_72
                !appl_74 <- appl_73 `pseq` klCons appl_73 (Types.Atom Types.Nil)
                !appl_75 <- appl_74 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_74
                !appl_76 <- appl_75 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_75
                appl_76 `pseq` kl_declare (ApplC (wrapNamed "cn" cn)) appl_76) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_77 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_78 <- appl_77 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.==>")) appl_77
                !appl_79 <- appl_78 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_78
                !appl_80 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_81 <- appl_80 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_80
                !appl_82 <- appl_81 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_81
                !appl_83 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_84 <- appl_83 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_83
                !appl_85 <- appl_82 `pseq` (appl_84 `pseq` klCons appl_82 appl_84)
                !appl_86 <- appl_85 `pseq` klCons appl_85 (Types.Atom Types.Nil)
                !appl_87 <- appl_86 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_86
                !appl_88 <- appl_87 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_87
                !appl_89 <- appl_88 `pseq` klCons appl_88 (Types.Atom Types.Nil)
                !appl_90 <- appl_89 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_89
                !appl_91 <- appl_79 `pseq` (appl_90 `pseq` klCons appl_79 appl_90)
                appl_91 `pseq` kl_declare (ApplC (wrapNamed "compile" kl_compile)) appl_91) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_92 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_93 <- appl_92 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_92
                !appl_94 <- appl_93 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_93
                appl_94 `pseq` kl_declare (ApplC (wrapNamed "cons?" consP)) appl_94) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_95 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_96 <- appl_95 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_95
                !appl_97 <- appl_96 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_96
                !appl_98 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_99 <- appl_98 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_98
                !appl_100 <- appl_97 `pseq` (appl_99 `pseq` klCons appl_97 appl_99)
                appl_100 `pseq` kl_declare (ApplC (wrapNamed "destroy" kl_destroy)) appl_100) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_101 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_102 <- appl_101 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_101
                !appl_103 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_104 <- appl_103 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_103
                !appl_105 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_106 <- appl_105 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_105
                !appl_107 <- appl_106 `pseq` klCons appl_106 (Types.Atom Types.Nil)
                !appl_108 <- appl_107 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_107
                !appl_109 <- appl_104 `pseq` (appl_108 `pseq` klCons appl_104 appl_108)
                !appl_110 <- appl_109 `pseq` klCons appl_109 (Types.Atom Types.Nil)
                !appl_111 <- appl_110 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_110
                !appl_112 <- appl_102 `pseq` (appl_111 `pseq` klCons appl_102 appl_111)
                appl_112 `pseq` kl_declare (ApplC (wrapNamed "difference" kl_difference)) appl_112) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_113 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_114 <- appl_113 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_113
                !appl_115 <- appl_114 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_114
                !appl_116 <- appl_115 `pseq` klCons appl_115 (Types.Atom Types.Nil)
                !appl_117 <- appl_116 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_116
                !appl_118 <- appl_117 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_117
                appl_118 `pseq` kl_declare (ApplC (wrapNamed "do" kl_do)) appl_118) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_119 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_120 <- appl_119 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_119
                !appl_121 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_122 <- appl_121 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_121
                !appl_123 <- appl_122 `pseq` klCons appl_122 (Types.Atom Types.Nil)
                !appl_124 <- appl_123 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.==>")) appl_123
                !appl_125 <- appl_120 `pseq` (appl_124 `pseq` klCons appl_120 appl_124)
                appl_125 `pseq` kl_declare (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_125) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_126 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_127 <- appl_126 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_126
                !appl_128 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_129 <- appl_128 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_128
                !appl_130 <- appl_129 `pseq` klCons appl_129 (Types.Atom Types.Nil)
                !appl_131 <- appl_130 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.==>")) appl_130
                !appl_132 <- appl_127 `pseq` (appl_131 `pseq` klCons appl_127 appl_131)
                appl_132 `pseq` kl_declare (ApplC (wrapNamed "shen.<!>" kl_shen_LBExclRB)) appl_132) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_133 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_134 <- appl_133 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_133
                !appl_135 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_136 <- appl_135 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_135
                !appl_137 <- appl_134 `pseq` (appl_136 `pseq` klCons appl_134 appl_136)
                !appl_138 <- appl_137 `pseq` klCons appl_137 (Types.Atom Types.Nil)
                !appl_139 <- appl_138 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_138
                !appl_140 <- appl_139 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_139
                appl_140 `pseq` kl_declare (ApplC (wrapNamed "element?" kl_elementP)) appl_140) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_141 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_142 <- appl_141 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_141
                !appl_143 <- appl_142 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_142
                appl_143 `pseq` kl_declare (ApplC (wrapNamed "empty?" kl_emptyP)) appl_143) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_144 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_145 <- appl_144 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_144
                !appl_146 <- appl_145 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_145
                appl_146 `pseq` kl_declare (Types.Atom (Types.UnboundSym "enable-type-theory")) appl_146) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_147 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_148 <- appl_147 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_147
                !appl_149 <- appl_148 `pseq` klCons appl_148 (Types.Atom Types.Nil)
                !appl_150 <- appl_149 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_149
                !appl_151 <- appl_150 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_150
                appl_151 `pseq` kl_declare (ApplC (wrapNamed "external" kl_external)) appl_151) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_152 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_153 <- appl_152 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_152
                !appl_154 <- appl_153 `pseq` klCons (Types.Atom (Types.UnboundSym "exception")) appl_153
                appl_154 `pseq` kl_declare (ApplC (wrapNamed "error-to-string" errorToString)) appl_154) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_155 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_156 <- appl_155 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_155
                !appl_157 <- appl_156 `pseq` klCons appl_156 (Types.Atom Types.Nil)
                !appl_158 <- appl_157 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_157
                !appl_159 <- appl_158 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_158
                appl_159 `pseq` kl_declare (ApplC (wrapNamed "explode" kl_explode)) appl_159) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_160 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_161 <- appl_160 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_160
                appl_161 `pseq` kl_declare (ApplC (PL "fail" kl_fail)) appl_161) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_162 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_163 <- appl_162 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_162
                !appl_164 <- appl_163 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_163
                !appl_165 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_166 <- appl_165 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_165
                !appl_167 <- appl_166 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_166
                !appl_168 <- appl_167 `pseq` klCons appl_167 (Types.Atom Types.Nil)
                !appl_169 <- appl_168 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_168
                !appl_170 <- appl_164 `pseq` (appl_169 `pseq` klCons appl_164 appl_169)
                appl_170 `pseq` kl_declare (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_170) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_171 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_172 <- appl_171 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_171
                !appl_173 <- appl_172 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_172
                !appl_174 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_175 <- appl_174 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_174
                !appl_176 <- appl_175 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_175
                !appl_177 <- appl_176 `pseq` klCons appl_176 (Types.Atom Types.Nil)
                !appl_178 <- appl_177 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_177
                !appl_179 <- appl_173 `pseq` (appl_178 `pseq` klCons appl_173 appl_178)
                appl_179 `pseq` kl_declare (ApplC (wrapNamed "fix" kl_fix)) appl_179) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_180 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_181 <- appl_180 `pseq` klCons (Types.Atom (Types.UnboundSym "lazy")) appl_180
                !appl_182 <- appl_181 `pseq` klCons appl_181 (Types.Atom Types.Nil)
                !appl_183 <- appl_182 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_182
                !appl_184 <- appl_183 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_183
                appl_184 `pseq` kl_declare (Types.Atom (Types.UnboundSym "freeze")) appl_184) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_185 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_186 <- appl_185 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_185
                !appl_187 <- appl_186 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_186
                !appl_188 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_189 <- appl_188 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_188
                !appl_190 <- appl_187 `pseq` (appl_189 `pseq` klCons appl_187 appl_189)
                appl_190 `pseq` kl_declare (ApplC (wrapNamed "fst" kl_fst)) appl_190) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_191 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_192 <- appl_191 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_191
                !appl_193 <- appl_192 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_192
                !appl_194 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_195 <- appl_194 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_194
                !appl_196 <- appl_195 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_195
                !appl_197 <- appl_196 `pseq` klCons appl_196 (Types.Atom Types.Nil)
                !appl_198 <- appl_197 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_197
                !appl_199 <- appl_193 `pseq` (appl_198 `pseq` klCons appl_193 appl_198)
                appl_199 `pseq` kl_declare (ApplC (wrapNamed "function" kl_function)) appl_199) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_200 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_201 <- appl_200 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_200
                !appl_202 <- appl_201 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_201
                appl_202 `pseq` kl_declare (ApplC (wrapNamed "gensym" kl_gensym)) appl_202) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_203 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_204 <- appl_203 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_203
                !appl_205 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_206 <- appl_205 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_205
                !appl_207 <- appl_206 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_206
                !appl_208 <- appl_207 `pseq` klCons appl_207 (Types.Atom Types.Nil)
                !appl_209 <- appl_208 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_208
                !appl_210 <- appl_204 `pseq` (appl_209 `pseq` klCons appl_204 appl_209)
                appl_210 `pseq` kl_declare (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_210) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_211 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_212 <- appl_211 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_211
                !appl_213 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_214 <- appl_213 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_213
                !appl_215 <- appl_214 `pseq` klCons appl_214 (Types.Atom Types.Nil)
                !appl_216 <- appl_215 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_215
                !appl_217 <- appl_216 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_216
                !appl_218 <- appl_217 `pseq` klCons appl_217 (Types.Atom Types.Nil)
                !appl_219 <- appl_218 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_218
                !appl_220 <- appl_219 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_219
                !appl_221 <- appl_220 `pseq` klCons appl_220 (Types.Atom Types.Nil)
                !appl_222 <- appl_221 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_221
                !appl_223 <- appl_212 `pseq` (appl_222 `pseq` klCons appl_212 appl_222)
                appl_223 `pseq` kl_declare (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_223) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_224 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_225 <- appl_224 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_224
                !appl_226 <- appl_225 `pseq` klCons appl_225 (Types.Atom Types.Nil)
                !appl_227 <- appl_226 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_226
                !appl_228 <- appl_227 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_227
                appl_228 `pseq` kl_declare (ApplC (wrapNamed "vector" kl_vector)) appl_228) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_229 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_230 <- appl_229 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_229
                !appl_231 <- appl_230 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_230
                appl_231 `pseq` kl_declare (ApplC (wrapNamed "get-time" getTime)) appl_231) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_232 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_233 <- appl_232 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_232
                !appl_234 <- appl_233 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_233
                !appl_235 <- appl_234 `pseq` klCons appl_234 (Types.Atom Types.Nil)
                !appl_236 <- appl_235 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_235
                !appl_237 <- appl_236 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_236
                appl_237 `pseq` kl_declare (ApplC (wrapNamed "hash" kl_hash)) appl_237) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_238 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_239 <- appl_238 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_238
                !appl_240 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_241 <- appl_240 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_240
                !appl_242 <- appl_239 `pseq` (appl_241 `pseq` klCons appl_239 appl_241)
                appl_242 `pseq` kl_declare (ApplC (wrapNamed "head" kl_head)) appl_242) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_243 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_244 <- appl_243 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_243
                !appl_245 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_246 <- appl_245 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_245
                !appl_247 <- appl_244 `pseq` (appl_246 `pseq` klCons appl_244 appl_246)
                appl_247 `pseq` kl_declare (ApplC (wrapNamed "hdv" kl_hdv)) appl_247) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_248 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_249 <- appl_248 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_248
                !appl_250 <- appl_249 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_249
                appl_250 `pseq` kl_declare (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_250) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_251 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_252 <- appl_251 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_251
                !appl_253 <- appl_252 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_252
                !appl_254 <- appl_253 `pseq` klCons appl_253 (Types.Atom Types.Nil)
                !appl_255 <- appl_254 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_254
                !appl_256 <- appl_255 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_255
                !appl_257 <- appl_256 `pseq` klCons appl_256 (Types.Atom Types.Nil)
                !appl_258 <- appl_257 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_257
                !appl_259 <- appl_258 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_258
                appl_259 `pseq` kl_declare (Types.Atom (Types.UnboundSym "if")) appl_259) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_260 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_261 <- appl_260 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_260
                appl_261 `pseq` kl_declare (ApplC (PL "it" kl_it)) appl_261) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_262 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_263 <- appl_262 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_262
                appl_263 `pseq` kl_declare (ApplC (PL "implementation" kl_implementation)) appl_263) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_264 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_265 <- appl_264 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_264
                !appl_266 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_267 <- appl_266 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_266
                !appl_268 <- appl_267 `pseq` klCons appl_267 (Types.Atom Types.Nil)
                !appl_269 <- appl_268 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_268
                !appl_270 <- appl_265 `pseq` (appl_269 `pseq` klCons appl_265 appl_269)
                appl_270 `pseq` kl_declare (ApplC (wrapNamed "include" kl_include)) appl_270) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_271 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_272 <- appl_271 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_271
                !appl_273 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_274 <- appl_273 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_273
                !appl_275 <- appl_274 `pseq` klCons appl_274 (Types.Atom Types.Nil)
                !appl_276 <- appl_275 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_275
                !appl_277 <- appl_272 `pseq` (appl_276 `pseq` klCons appl_272 appl_276)
                appl_277 `pseq` kl_declare (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_277) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_278 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_279 <- appl_278 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_278
                appl_279 `pseq` kl_declare (ApplC (PL "inferences" kl_inferences)) appl_279) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_280 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_281 <- appl_280 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_280
                !appl_282 <- appl_281 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_281
                !appl_283 <- appl_282 `pseq` klCons appl_282 (Types.Atom Types.Nil)
                !appl_284 <- appl_283 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_283
                !appl_285 <- appl_284 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_284
                appl_285 `pseq` kl_declare (ApplC (wrapNamed "shen.insert" kl_shen_insert)) appl_285) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_286 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_287 <- appl_286 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_286
                !appl_288 <- appl_287 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_287
                appl_288 `pseq` kl_declare (ApplC (wrapNamed "integer?" kl_integerP)) appl_288) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_289 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_290 <- appl_289 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_289
                !appl_291 <- appl_290 `pseq` klCons appl_290 (Types.Atom Types.Nil)
                !appl_292 <- appl_291 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_291
                !appl_293 <- appl_292 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_292
                appl_293 `pseq` kl_declare (ApplC (wrapNamed "internal" kl_internal)) appl_293) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_294 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_295 <- appl_294 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_294
                !appl_296 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_297 <- appl_296 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_296
                !appl_298 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_299 <- appl_298 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_298
                !appl_300 <- appl_299 `pseq` klCons appl_299 (Types.Atom Types.Nil)
                !appl_301 <- appl_300 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_300
                !appl_302 <- appl_297 `pseq` (appl_301 `pseq` klCons appl_297 appl_301)
                !appl_303 <- appl_302 `pseq` klCons appl_302 (Types.Atom Types.Nil)
                !appl_304 <- appl_303 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_303
                !appl_305 <- appl_295 `pseq` (appl_304 `pseq` klCons appl_295 appl_304)
                appl_305 `pseq` kl_declare (ApplC (wrapNamed "intersection" kl_intersection)) appl_305) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_306 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_307 <- appl_306 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_306
                appl_307 `pseq` kl_declare (ApplC (PL "kill" kl_kill)) appl_307) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_308 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_309 <- appl_308 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_308
                appl_309 `pseq` kl_declare (ApplC (PL "language" kl_language)) appl_309) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_310 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_311 <- appl_310 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_310
                !appl_312 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_313 <- appl_312 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_312
                !appl_314 <- appl_311 `pseq` (appl_313 `pseq` klCons appl_311 appl_313)
                appl_314 `pseq` kl_declare (ApplC (wrapNamed "length" kl_length)) appl_314) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_315 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_316 <- appl_315 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_315
                !appl_317 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_318 <- appl_317 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_317
                !appl_319 <- appl_316 `pseq` (appl_318 `pseq` klCons appl_316 appl_318)
                appl_319 `pseq` kl_declare (ApplC (wrapNamed "limit" kl_limit)) appl_319) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_320 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_321 <- appl_320 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_320
                !appl_322 <- appl_321 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_321
                appl_322 `pseq` kl_declare (ApplC (wrapNamed "load" kl_load)) appl_322) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_323 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_324 <- appl_323 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_323
                !appl_325 <- appl_324 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_324
                !appl_326 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_327 <- appl_326 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_326
                !appl_328 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_329 <- appl_328 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_328
                !appl_330 <- appl_329 `pseq` klCons appl_329 (Types.Atom Types.Nil)
                !appl_331 <- appl_330 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_330
                !appl_332 <- appl_327 `pseq` (appl_331 `pseq` klCons appl_327 appl_331)
                !appl_333 <- appl_332 `pseq` klCons appl_332 (Types.Atom Types.Nil)
                !appl_334 <- appl_333 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_333
                !appl_335 <- appl_325 `pseq` (appl_334 `pseq` klCons appl_325 appl_334)
                appl_335 `pseq` kl_declare (ApplC (wrapNamed "map" kl_map)) appl_335) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_336 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_337 <- appl_336 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_336
                !appl_338 <- appl_337 `pseq` klCons appl_337 (Types.Atom Types.Nil)
                !appl_339 <- appl_338 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_338
                !appl_340 <- appl_339 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_339
                !appl_341 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_342 <- appl_341 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_341
                !appl_343 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_344 <- appl_343 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_343
                !appl_345 <- appl_344 `pseq` klCons appl_344 (Types.Atom Types.Nil)
                !appl_346 <- appl_345 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_345
                !appl_347 <- appl_342 `pseq` (appl_346 `pseq` klCons appl_342 appl_346)
                !appl_348 <- appl_347 `pseq` klCons appl_347 (Types.Atom Types.Nil)
                !appl_349 <- appl_348 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_348
                !appl_350 <- appl_340 `pseq` (appl_349 `pseq` klCons appl_340 appl_349)
                appl_350 `pseq` kl_declare (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_350) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_351 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_352 <- appl_351 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_351
                !appl_353 <- appl_352 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_352
                appl_353 `pseq` kl_declare (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_353) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_354 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_355 <- appl_354 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_354
                !appl_356 <- appl_355 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_355
                appl_356 `pseq` kl_declare (ApplC (wrapNamed "n->string" nToString)) appl_356) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_357 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_358 <- appl_357 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_357
                !appl_359 <- appl_358 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_358
                appl_359 `pseq` kl_declare (ApplC (wrapNamed "nl" kl_nl)) appl_359) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_360 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_361 <- appl_360 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_360
                !appl_362 <- appl_361 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_361
                appl_362 `pseq` kl_declare (ApplC (wrapNamed "not" kl_not)) appl_362) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_363 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_364 <- appl_363 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_363
                !appl_365 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_366 <- appl_365 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_365
                !appl_367 <- appl_364 `pseq` (appl_366 `pseq` klCons appl_364 appl_366)
                !appl_368 <- appl_367 `pseq` klCons appl_367 (Types.Atom Types.Nil)
                !appl_369 <- appl_368 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_368
                !appl_370 <- appl_369 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_369
                appl_370 `pseq` kl_declare (ApplC (wrapNamed "nth" kl_nth)) appl_370) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_371 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_372 <- appl_371 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_371
                !appl_373 <- appl_372 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_372
                appl_373 `pseq` kl_declare (ApplC (wrapNamed "number?" numberP)) appl_373) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_374 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_375 <- appl_374 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_374
                !appl_376 <- appl_375 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_375
                !appl_377 <- appl_376 `pseq` klCons appl_376 (Types.Atom Types.Nil)
                !appl_378 <- appl_377 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_377
                !appl_379 <- appl_378 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_378
                appl_379 `pseq` kl_declare (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_379) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_380 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_381 <- appl_380 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_380
                !appl_382 <- appl_381 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_381
                appl_382 `pseq` kl_declare (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_382) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_383 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_384 <- appl_383 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_383
                !appl_385 <- appl_384 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_384
                appl_385 `pseq` kl_declare (ApplC (wrapNamed "optimise" kl_optimise)) appl_385) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_386 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_387 <- appl_386 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_386
                !appl_388 <- appl_387 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_387
                !appl_389 <- appl_388 `pseq` klCons appl_388 (Types.Atom Types.Nil)
                !appl_390 <- appl_389 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_389
                !appl_391 <- appl_390 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_390
                appl_391 `pseq` kl_declare (Types.Atom (Types.UnboundSym "or")) appl_391) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_392 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_393 <- appl_392 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_392
                appl_393 `pseq` kl_declare (ApplC (PL "os" kl_os)) appl_393) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_394 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_395 <- appl_394 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_394
                !appl_396 <- appl_395 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_395
                appl_396 `pseq` kl_declare (ApplC (wrapNamed "package?" kl_packageP)) appl_396) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_397 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_398 <- appl_397 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_397
                appl_398 `pseq` kl_declare (ApplC (PL "port" kl_port)) appl_398) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_399 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_400 <- appl_399 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_399
                appl_400 `pseq` kl_declare (ApplC (PL "porters" kl_porters)) appl_400) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_401 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_402 <- appl_401 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_401
                !appl_403 <- appl_402 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_402
                !appl_404 <- appl_403 `pseq` klCons appl_403 (Types.Atom Types.Nil)
                !appl_405 <- appl_404 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_404
                !appl_406 <- appl_405 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_405
                appl_406 `pseq` kl_declare (ApplC (wrapNamed "pos" pos)) appl_406) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_407 <- klCons (Types.Atom (Types.UnboundSym "out")) (Types.Atom Types.Nil)
                !appl_408 <- appl_407 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_407
                !appl_409 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_410 <- appl_409 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_409
                !appl_411 <- appl_408 `pseq` (appl_410 `pseq` klCons appl_408 appl_410)
                !appl_412 <- appl_411 `pseq` klCons appl_411 (Types.Atom Types.Nil)
                !appl_413 <- appl_412 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_412
                !appl_414 <- appl_413 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_413
                appl_414 `pseq` kl_declare (ApplC (wrapNamed "pr" kl_pr)) appl_414) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_415 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_416 <- appl_415 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_415
                !appl_417 <- appl_416 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_416
                appl_417 `pseq` kl_declare (ApplC (wrapNamed "print" kl_print)) appl_417) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_418 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_419 <- appl_418 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_418
                !appl_420 <- appl_419 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_419
                !appl_421 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_422 <- appl_421 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_421
                !appl_423 <- appl_422 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_422
                !appl_424 <- appl_423 `pseq` klCons appl_423 (Types.Atom Types.Nil)
                !appl_425 <- appl_424 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_424
                !appl_426 <- appl_420 `pseq` (appl_425 `pseq` klCons appl_420 appl_425)
                appl_426 `pseq` kl_declare (ApplC (wrapNamed "profile" kl_profile)) appl_426) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_427 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_428 <- appl_427 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_427
                !appl_429 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_430 <- appl_429 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_429
                !appl_431 <- appl_430 `pseq` klCons appl_430 (Types.Atom Types.Nil)
                !appl_432 <- appl_431 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_431
                !appl_433 <- appl_428 `pseq` (appl_432 `pseq` klCons appl_428 appl_432)
                appl_433 `pseq` kl_declare (ApplC (wrapNamed "preclude" kl_preclude)) appl_433) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_434 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_435 <- appl_434 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_434
                !appl_436 <- appl_435 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_435
                appl_436 `pseq` kl_declare (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl)) appl_436) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_437 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_438 <- appl_437 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_437
                !appl_439 <- appl_438 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_438
                !appl_440 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_441 <- appl_440 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_440
                !appl_442 <- appl_441 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_441
                !appl_443 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_444 <- appl_443 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_443
                !appl_445 <- appl_442 `pseq` (appl_444 `pseq` klCons appl_442 appl_444)
                !appl_446 <- appl_445 `pseq` klCons appl_445 (Types.Atom Types.Nil)
                !appl_447 <- appl_446 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_446
                !appl_448 <- appl_439 `pseq` (appl_447 `pseq` klCons appl_439 appl_447)
                appl_448 `pseq` kl_declare (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_448) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_449 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_450 <- appl_449 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_449
                !appl_451 <- appl_450 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_450
                appl_451 `pseq` kl_declare (ApplC (wrapNamed "protect" kl_protect)) appl_451) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_452 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_453 <- appl_452 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_452
                !appl_454 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_455 <- appl_454 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_454
                !appl_456 <- appl_455 `pseq` klCons appl_455 (Types.Atom Types.Nil)
                !appl_457 <- appl_456 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_456
                !appl_458 <- appl_453 `pseq` (appl_457 `pseq` klCons appl_453 appl_457)
                appl_458 `pseq` kl_declare (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_458) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_459 <- klCons (Types.Atom (Types.UnboundSym "out")) (Types.Atom Types.Nil)
                !appl_460 <- appl_459 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_459
                !appl_461 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_462 <- appl_461 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_461
                !appl_463 <- appl_460 `pseq` (appl_462 `pseq` klCons appl_460 appl_462)
                !appl_464 <- appl_463 `pseq` klCons appl_463 (Types.Atom Types.Nil)
                !appl_465 <- appl_464 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_464
                !appl_466 <- appl_465 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_465
                appl_466 `pseq` kl_declare (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_466) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_467 <- klCons (Types.Atom (Types.UnboundSym "unit")) (Types.Atom Types.Nil)
                !appl_468 <- appl_467 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_467
                !appl_469 <- appl_468 `pseq` klCons appl_468 (Types.Atom Types.Nil)
                !appl_470 <- appl_469 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_469
                !appl_471 <- appl_470 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_470
                appl_471 `pseq` kl_declare (ApplC (wrapNamed "ps" kl_ps)) appl_471) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_472 <- klCons (Types.Atom (Types.UnboundSym "in")) (Types.Atom Types.Nil)
                !appl_473 <- appl_472 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_472
                !appl_474 <- klCons (Types.Atom (Types.UnboundSym "unit")) (Types.Atom Types.Nil)
                !appl_475 <- appl_474 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_474
                !appl_476 <- appl_473 `pseq` (appl_475 `pseq` klCons appl_473 appl_475)
                appl_476 `pseq` kl_declare (ApplC (wrapNamed "read" kl_read)) appl_476) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_477 <- klCons (Types.Atom (Types.UnboundSym "in")) (Types.Atom Types.Nil)
                !appl_478 <- appl_477 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_477
                !appl_479 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_480 <- appl_479 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_479
                !appl_481 <- appl_478 `pseq` (appl_480 `pseq` klCons appl_478 appl_480)
                appl_481 `pseq` kl_declare (ApplC (wrapNamed "read-byte" readByte)) appl_481) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_482 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_483 <- appl_482 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_482
                !appl_484 <- appl_483 `pseq` klCons appl_483 (Types.Atom Types.Nil)
                !appl_485 <- appl_484 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_484
                !appl_486 <- appl_485 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_485
                appl_486 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-bytelist" kl_read_file_as_bytelist)) appl_486) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_487 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_488 <- appl_487 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_487
                !appl_489 <- appl_488 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_488
                appl_489 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_489) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_490 <- klCons (Types.Atom (Types.UnboundSym "unit")) (Types.Atom Types.Nil)
                !appl_491 <- appl_490 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_490
                !appl_492 <- appl_491 `pseq` klCons appl_491 (Types.Atom Types.Nil)
                !appl_493 <- appl_492 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_492
                !appl_494 <- appl_493 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_493
                appl_494 `pseq` kl_declare (ApplC (wrapNamed "read-file" kl_read_file)) appl_494) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_495 <- klCons (Types.Atom (Types.UnboundSym "unit")) (Types.Atom Types.Nil)
                !appl_496 <- appl_495 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_495
                !appl_497 <- appl_496 `pseq` klCons appl_496 (Types.Atom Types.Nil)
                !appl_498 <- appl_497 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_497
                !appl_499 <- appl_498 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_498
                appl_499 `pseq` kl_declare (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_499) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_500 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_501 <- appl_500 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_500
                appl_501 `pseq` kl_declare (ApplC (PL "release" kl_release)) appl_501) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_502 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_503 <- appl_502 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_502
                !appl_504 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_505 <- appl_504 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_504
                !appl_506 <- appl_505 `pseq` klCons appl_505 (Types.Atom Types.Nil)
                !appl_507 <- appl_506 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_506
                !appl_508 <- appl_503 `pseq` (appl_507 `pseq` klCons appl_503 appl_507)
                !appl_509 <- appl_508 `pseq` klCons appl_508 (Types.Atom Types.Nil)
                !appl_510 <- appl_509 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_509
                !appl_511 <- appl_510 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_510
                appl_511 `pseq` kl_declare (ApplC (wrapNamed "remove" kl_remove)) appl_511) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_512 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_513 <- appl_512 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_512
                !appl_514 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_515 <- appl_514 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_514
                !appl_516 <- appl_515 `pseq` klCons appl_515 (Types.Atom Types.Nil)
                !appl_517 <- appl_516 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_516
                !appl_518 <- appl_513 `pseq` (appl_517 `pseq` klCons appl_513 appl_517)
                appl_518 `pseq` kl_declare (ApplC (wrapNamed "reverse" kl_reverse)) appl_518) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_519 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_520 <- appl_519 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_519
                !appl_521 <- appl_520 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_520
                appl_521 `pseq` kl_declare (ApplC (wrapNamed "simple-error" simpleError)) appl_521) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_522 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_523 <- appl_522 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_522
                !appl_524 <- appl_523 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_523
                !appl_525 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_526 <- appl_525 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_525
                !appl_527 <- appl_524 `pseq` (appl_526 `pseq` klCons appl_524 appl_526)
                appl_527 `pseq` kl_declare (ApplC (wrapNamed "snd" kl_snd)) appl_527) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_528 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_529 <- appl_528 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_528
                !appl_530 <- appl_529 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_529
                appl_530 `pseq` kl_declare (ApplC (wrapNamed "specialise" kl_specialise)) appl_530) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_531 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_532 <- appl_531 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_531
                !appl_533 <- appl_532 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_532
                appl_533 `pseq` kl_declare (ApplC (wrapNamed "spy" kl_spy)) appl_533) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_534 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_535 <- appl_534 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_534
                !appl_536 <- appl_535 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_535
                appl_536 `pseq` kl_declare (ApplC (wrapNamed "step" kl_step)) appl_536) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_537 <- klCons (Types.Atom (Types.UnboundSym "in")) (Types.Atom Types.Nil)
                !appl_538 <- appl_537 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_537
                !appl_539 <- appl_538 `pseq` klCons appl_538 (Types.Atom Types.Nil)
                !appl_540 <- appl_539 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_539
                appl_540 `pseq` kl_declare (ApplC (PL "stinput" kl_stinput)) appl_540) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_541 <- klCons (Types.Atom (Types.UnboundSym "out")) (Types.Atom Types.Nil)
                !appl_542 <- appl_541 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_541
                !appl_543 <- appl_542 `pseq` klCons appl_542 (Types.Atom Types.Nil)
                !appl_544 <- appl_543 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_543
                appl_544 `pseq` kl_declare (ApplC (PL "stoutput" kl_stoutput)) appl_544) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_545 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_546 <- appl_545 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_545
                !appl_547 <- appl_546 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_546
                appl_547 `pseq` kl_declare (ApplC (wrapNamed "string?" stringP)) appl_547) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_548 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_549 <- appl_548 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_548
                !appl_550 <- appl_549 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_549
                appl_550 `pseq` kl_declare (ApplC (wrapNamed "str" str)) appl_550) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_551 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_552 <- appl_551 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_551
                !appl_553 <- appl_552 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_552
                appl_553 `pseq` kl_declare (ApplC (wrapNamed "string->n" stringToN)) appl_553) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_554 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_555 <- appl_554 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_554
                !appl_556 <- appl_555 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_555
                appl_556 `pseq` kl_declare (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_556) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_557 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_558 <- appl_557 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_557
                !appl_559 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_560 <- appl_559 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_559
                !appl_561 <- appl_558 `pseq` (appl_560 `pseq` klCons appl_558 appl_560)
                appl_561 `pseq` kl_declare (ApplC (wrapNamed "sum" kl_sum)) appl_561) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_562 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_563 <- appl_562 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_562
                !appl_564 <- appl_563 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_563
                appl_564 `pseq` kl_declare (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_564) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_565 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_566 <- appl_565 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_565
                !appl_567 <- appl_566 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_566
                appl_567 `pseq` kl_declare (ApplC (wrapNamed "systemf" kl_systemf)) appl_567) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_568 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_569 <- appl_568 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_568
                !appl_570 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_571 <- appl_570 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_570
                !appl_572 <- appl_571 `pseq` klCons appl_571 (Types.Atom Types.Nil)
                !appl_573 <- appl_572 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_572
                !appl_574 <- appl_569 `pseq` (appl_573 `pseq` klCons appl_569 appl_573)
                appl_574 `pseq` kl_declare (ApplC (wrapNamed "tail" kl_tail)) appl_574) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_575 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_576 <- appl_575 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_575
                !appl_577 <- appl_576 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_576
                appl_577 `pseq` kl_declare (ApplC (wrapNamed "tlstr" tlstr)) appl_577) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_578 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_579 <- appl_578 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_578
                !appl_580 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_581 <- appl_580 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_580
                !appl_582 <- appl_581 `pseq` klCons appl_581 (Types.Atom Types.Nil)
                !appl_583 <- appl_582 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_582
                !appl_584 <- appl_579 `pseq` (appl_583 `pseq` klCons appl_579 appl_583)
                appl_584 `pseq` kl_declare (ApplC (wrapNamed "tlv" kl_tlv)) appl_584) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_585 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_586 <- appl_585 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_585
                !appl_587 <- appl_586 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_586
                appl_587 `pseq` kl_declare (ApplC (wrapNamed "tc" kl_tc)) appl_587) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_588 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_589 <- appl_588 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_588
                appl_589 `pseq` kl_declare (ApplC (PL "tc?" kl_tcP)) appl_589) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_590 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_591 <- appl_590 `pseq` klCons (Types.Atom (Types.UnboundSym "lazy")) appl_590
                !appl_592 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_593 <- appl_592 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_592
                !appl_594 <- appl_591 `pseq` (appl_593 `pseq` klCons appl_591 appl_593)
                appl_594 `pseq` kl_declare (ApplC (wrapNamed "thaw" kl_thaw)) appl_594) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_595 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_596 <- appl_595 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_595
                !appl_597 <- appl_596 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_596
                appl_597 `pseq` kl_declare (ApplC (wrapNamed "track" kl_track)) appl_597) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_598 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_599 <- appl_598 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_598
                !appl_600 <- appl_599 `pseq` klCons (Types.Atom (Types.UnboundSym "exception")) appl_599
                !appl_601 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_602 <- appl_601 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_601
                !appl_603 <- appl_600 `pseq` (appl_602 `pseq` klCons appl_600 appl_602)
                !appl_604 <- appl_603 `pseq` klCons appl_603 (Types.Atom Types.Nil)
                !appl_605 <- appl_604 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_604
                !appl_606 <- appl_605 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_605
                appl_606 `pseq` kl_declare (Types.Atom (Types.UnboundSym "trap-error")) appl_606) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_607 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_608 <- appl_607 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_607
                !appl_609 <- appl_608 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_608
                appl_609 `pseq` kl_declare (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_609) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_610 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_611 <- appl_610 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_610
                !appl_612 <- appl_611 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_611
                appl_612 `pseq` kl_declare (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_612) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_613 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_614 <- appl_613 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_613
                !appl_615 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_616 <- appl_615 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_615
                !appl_617 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_618 <- appl_617 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_617
                !appl_619 <- appl_618 `pseq` klCons appl_618 (Types.Atom Types.Nil)
                !appl_620 <- appl_619 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_619
                !appl_621 <- appl_616 `pseq` (appl_620 `pseq` klCons appl_616 appl_620)
                !appl_622 <- appl_621 `pseq` klCons appl_621 (Types.Atom Types.Nil)
                !appl_623 <- appl_622 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_622
                !appl_624 <- appl_614 `pseq` (appl_623 `pseq` klCons appl_614 appl_623)
                appl_624 `pseq` kl_declare (ApplC (wrapNamed "union" kl_union)) appl_624) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_625 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_626 <- appl_625 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_625
                !appl_627 <- appl_626 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_626
                !appl_628 <- klCons (Types.Atom (Types.UnboundSym "B")) (Types.Atom Types.Nil)
                !appl_629 <- appl_628 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_628
                !appl_630 <- appl_629 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_629
                !appl_631 <- appl_630 `pseq` klCons appl_630 (Types.Atom Types.Nil)
                !appl_632 <- appl_631 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_631
                !appl_633 <- appl_627 `pseq` (appl_632 `pseq` klCons appl_627 appl_632)
                appl_633 `pseq` kl_declare (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_633) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_634 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_635 <- appl_634 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_634
                !appl_636 <- appl_635 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_635
                appl_636 `pseq` kl_declare (ApplC (wrapNamed "untrack" kl_untrack)) appl_636) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_637 <- klCons (Types.Atom (Types.UnboundSym "symbol")) (Types.Atom Types.Nil)
                !appl_638 <- appl_637 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_637
                !appl_639 <- appl_638 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_638
                appl_639 `pseq` kl_declare (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_639) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_640 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_641 <- appl_640 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_640
                !appl_642 <- appl_641 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_641
                appl_642 `pseq` kl_declare (ApplC (wrapNamed "variable?" kl_variableP)) appl_642) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_643 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_644 <- appl_643 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_643
                !appl_645 <- appl_644 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_644
                appl_645 `pseq` kl_declare (ApplC (wrapNamed "vector?" kl_vectorP)) appl_645) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_646 <- klCons (Types.Atom (Types.UnboundSym "string")) (Types.Atom Types.Nil)
                !appl_647 <- appl_646 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_646
                appl_647 `pseq` kl_declare (ApplC (PL "version" kl_version)) appl_647) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_648 <- klCons (Types.Atom (Types.UnboundSym "A")) (Types.Atom Types.Nil)
                !appl_649 <- appl_648 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_648
                !appl_650 <- appl_649 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_649
                !appl_651 <- appl_650 `pseq` klCons appl_650 (Types.Atom Types.Nil)
                !appl_652 <- appl_651 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_651
                !appl_653 <- appl_652 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_652
                appl_653 `pseq` kl_declare (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_653) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_654 <- klCons (Types.Atom (Types.UnboundSym "out")) (Types.Atom Types.Nil)
                !appl_655 <- appl_654 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_654
                !appl_656 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_657 <- appl_656 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_656
                !appl_658 <- appl_655 `pseq` (appl_657 `pseq` klCons appl_655 appl_657)
                !appl_659 <- appl_658 `pseq` klCons appl_658 (Types.Atom Types.Nil)
                !appl_660 <- appl_659 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_659
                !appl_661 <- appl_660 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_660
                appl_661 `pseq` kl_declare (ApplC (wrapNamed "write-byte" writeByte)) appl_661) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_662 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_663 <- appl_662 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_662
                !appl_664 <- appl_663 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_663
                appl_664 `pseq` kl_declare (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_664) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_665 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_666 <- appl_665 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_665
                !appl_667 <- appl_666 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_666
                !appl_668 <- appl_667 `pseq` klCons appl_667 (Types.Atom Types.Nil)
                !appl_669 <- appl_668 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_668
                !appl_670 <- appl_669 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_669
                appl_670 `pseq` kl_declare (ApplC (wrapNamed ">" greaterThan)) appl_670) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_671 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_672 <- appl_671 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_671
                !appl_673 <- appl_672 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_672
                !appl_674 <- appl_673 `pseq` klCons appl_673 (Types.Atom Types.Nil)
                !appl_675 <- appl_674 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_674
                !appl_676 <- appl_675 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_675
                appl_676 `pseq` kl_declare (ApplC (wrapNamed "<" lessThan)) appl_676) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_677 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_678 <- appl_677 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_677
                !appl_679 <- appl_678 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_678
                !appl_680 <- appl_679 `pseq` klCons appl_679 (Types.Atom Types.Nil)
                !appl_681 <- appl_680 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_680
                !appl_682 <- appl_681 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_681
                appl_682 `pseq` kl_declare (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_682) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_683 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_684 <- appl_683 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_683
                !appl_685 <- appl_684 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_684
                !appl_686 <- appl_685 `pseq` klCons appl_685 (Types.Atom Types.Nil)
                !appl_687 <- appl_686 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_686
                !appl_688 <- appl_687 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_687
                appl_688 `pseq` kl_declare (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_688) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_689 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_690 <- appl_689 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_689
                !appl_691 <- appl_690 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_690
                !appl_692 <- appl_691 `pseq` klCons appl_691 (Types.Atom Types.Nil)
                !appl_693 <- appl_692 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_692
                !appl_694 <- appl_693 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_693
                appl_694 `pseq` kl_declare (ApplC (wrapNamed "=" eq)) appl_694) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_695 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_696 <- appl_695 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_695
                !appl_697 <- appl_696 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_696
                !appl_698 <- appl_697 `pseq` klCons appl_697 (Types.Atom Types.Nil)
                !appl_699 <- appl_698 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_698
                !appl_700 <- appl_699 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_699
                appl_700 `pseq` kl_declare (ApplC (wrapNamed "+" add)) appl_700) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_701 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_702 <- appl_701 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_701
                !appl_703 <- appl_702 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_702
                !appl_704 <- appl_703 `pseq` klCons appl_703 (Types.Atom Types.Nil)
                !appl_705 <- appl_704 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_704
                !appl_706 <- appl_705 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_705
                appl_706 `pseq` kl_declare (ApplC (wrapNamed "/" divide)) appl_706) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_707 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_708 <- appl_707 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_707
                !appl_709 <- appl_708 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_708
                !appl_710 <- appl_709 `pseq` klCons appl_709 (Types.Atom Types.Nil)
                !appl_711 <- appl_710 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_710
                !appl_712 <- appl_711 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_711
                appl_712 `pseq` kl_declare (ApplC (wrapNamed "-" Primitives.subtract)) appl_712) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_713 <- klCons (Types.Atom (Types.UnboundSym "number")) (Types.Atom Types.Nil)
                !appl_714 <- appl_713 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_713
                !appl_715 <- appl_714 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_714
                !appl_716 <- appl_715 `pseq` klCons appl_715 (Types.Atom Types.Nil)
                !appl_717 <- appl_716 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_716
                !appl_718 <- appl_717 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_717
                appl_718 `pseq` kl_declare (ApplC (wrapNamed "*" multiply)) appl_718) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_719 <- klCons (Types.Atom (Types.UnboundSym "boolean")) (Types.Atom Types.Nil)
                !appl_720 <- appl_719 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_719
                !appl_721 <- appl_720 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_720
                !appl_722 <- appl_721 `pseq` klCons appl_721 (Types.Atom Types.Nil)
                !appl_723 <- appl_722 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_722
                !appl_724 <- appl_723 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_723
                appl_724 `pseq` kl_declare (ApplC (wrapNamed "==" kl_EqEq)) appl_724) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
