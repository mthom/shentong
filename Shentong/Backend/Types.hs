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

kl_declare :: Types.KLValue ->
              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_declare (!kl_V2373) (!kl_V2374) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Record) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Variancy) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Type) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_FMult) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parameters) -> do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_Clause) -> do let !appl_6 = ApplC (Func "lambda" (Context (\(!kl_AUM_instruction) -> do let !appl_7 = ApplC (Func "lambda" (Context (\(!kl_Code) -> do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_ShenDef) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Eval) -> do return kl_V2373)))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            !appl_10 <- kl_ShenDef `pseq` kl_shen_eval_without_macros kl_ShenDef
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            appl_10 `pseq` applyWrapper appl_9 [appl_10])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          let !appl_11 = List []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "Continuation")) appl_11
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.UnboundSym "ProcessN")) appl_12
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          let !appl_14 = List []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_15 <- kl_Code `pseq` (appl_14 `pseq` klCons kl_Code appl_14)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_15
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_17 <- appl_13 `pseq` (appl_16 `pseq` kl_append appl_13 appl_16)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_18 <- kl_Parameters `pseq` (appl_17 `pseq` kl_append kl_Parameters appl_17)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_19 <- kl_FMult `pseq` (appl_18 `pseq` klCons kl_FMult appl_18)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_19
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          appl_20 `pseq` applyWrapper appl_8 [appl_20])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !appl_21 <- kl_AUM_instruction `pseq` kl_shen_aum_to_shen kl_AUM_instruction
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           appl_21 `pseq` applyWrapper appl_7 [appl_21])))
                                                                                                                                                                                                                                                                                                                                                                                                                                                 !appl_22 <- kl_Clause `pseq` (kl_Parameters `pseq` kl_shen_aum kl_Clause kl_Parameters)
                                                                                                                                                                                                                                                                                                                                                                                                                                                 appl_22 `pseq` applyWrapper appl_6 [appl_22])))
                                                                                                                                                                                                                                                                                                                                                                                let !appl_23 = List []
                                                                                                                                                                                                                                                                                                                                                                                !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_23
                                                                                                                                                                                                                                                                                                                                                                                !appl_25 <- kl_FMult `pseq` (appl_24 `pseq` klCons kl_FMult appl_24)
                                                                                                                                                                                                                                                                                                                                                                                let !appl_26 = List []
                                                                                                                                                                                                                                                                                                                                                                                !appl_27 <- kl_Type `pseq` (appl_26 `pseq` klCons kl_Type appl_26)
                                                                                                                                                                                                                                                                                                                                                                                !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_27
                                                                                                                                                                                                                                                                                                                                                                                !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_28
                                                                                                                                                                                                                                                                                                                                                                                let !appl_30 = List []
                                                                                                                                                                                                                                                                                                                                                                                !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                                                                                                                                                                                                                                                                                                                                                                                let !appl_32 = List []
                                                                                                                                                                                                                                                                                                                                                                                !appl_33 <- appl_31 `pseq` (appl_32 `pseq` klCons appl_31 appl_32)
                                                                                                                                                                                                                                                                                                                                                                                !appl_34 <- appl_33 `pseq` klCons (Types.Atom (Types.UnboundSym ":-")) appl_33
                                                                                                                                                                                                                                                                                                                                                                                !appl_35 <- appl_25 `pseq` (appl_34 `pseq` klCons appl_25 appl_34)
                                                                                                                                                                                                                                                                                                                                                                                appl_35 `pseq` applyWrapper appl_5 [appl_35])))
                                                                                                                                                                                                                                                                                                           !appl_36 <- kl_shen_parameters (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                                                           appl_36 `pseq` applyWrapper appl_4 [appl_36])))
                                                                                                                                                                                                                                           !appl_37 <- kl_V2373 `pseq` kl_concat (Types.Atom (Types.UnboundSym "shen.type-signature-of-")) kl_V2373
                                                                                                                                                                                                                                           appl_37 `pseq` applyWrapper appl_3 [appl_37])))
                                                                                                                                                                            !appl_38 <- kl_V2374 `pseq` kl_shen_demodulate kl_V2374
                                                                                                                                                                            !appl_39 <- appl_38 `pseq` kl_shen_rcons_form appl_38
                                                                                                                                                                            appl_39 `pseq` applyWrapper appl_2 [appl_39])))
                                                                                                         !appl_40 <- (do kl_V2373 `pseq` (kl_V2374 `pseq` kl_shen_variancy_test kl_V2373 kl_V2374)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.skip")))
                                                                                                         appl_40 `pseq` applyWrapper appl_1 [appl_40])))
                                        !appl_41 <- kl_V2373 `pseq` (kl_V2374 `pseq` klCons kl_V2373 kl_V2374)
                                        !appl_42 <- value (Types.Atom (Types.UnboundSym "shen.*signedfuncs*"))
                                        !appl_43 <- appl_41 `pseq` (appl_42 `pseq` klCons appl_41 appl_42)
                                        !appl_44 <- appl_43 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*signedfuncs*")) appl_43
                                        appl_44 `pseq` applyWrapper appl_0 [appl_44]

kl_shen_demodulate :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_demodulate (!kl_V2375) = do (do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Demod) -> do !kl_if_1 <- kl_Demod `pseq` (kl_V2375 `pseq` eq kl_Demod kl_V2375)
                                                                                                        klIf kl_if_1 (do return kl_V2375) (do kl_Demod `pseq` kl_shen_demodulate kl_Demod))))
                                        let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_V2372) -> do let !aw_3 = Types.Atom (Types.UnboundSym "shen.demod")
                                                                                                        kl_V2372 `pseq` applyWrapper aw_3 [kl_V2372])))
                                        !appl_4 <- appl_2 `pseq` (kl_V2375 `pseq` kl_shen_walk appl_2 kl_V2375)
                                        appl_4 `pseq` applyWrapper appl_0 [appl_4]) `catchError` (\(!kl_E) -> do return kl_V2375)

kl_shen_variancy_test :: Types.KLValue ->
                         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_variancy_test (!kl_V2376) (!kl_V2377) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_TypeF) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Check) -> do return (Types.Atom (Types.UnboundSym "shen.skip")))))
                                                                                                                   !kl_if_2 <- kl_TypeF `pseq` eq (Types.Atom (Types.UnboundSym "symbol")) kl_TypeF
                                                                                                                   !appl_3 <- klIf kl_if_2 (do return (Types.Atom (Types.UnboundSym "shen.skip"))) (do !kl_if_4 <- kl_TypeF `pseq` (kl_V2377 `pseq` kl_shen_variantP kl_TypeF kl_V2377)
                                                                                                                                                                                                       klIf kl_if_4 (do return (Types.Atom (Types.UnboundSym "shen.skip"))) (do !appl_5 <- kl_V2376 `pseq` kl_shen_app kl_V2376 (Types.Atom (Types.Str " may create errors\n")) (Types.Atom (Types.UnboundSym "shen.a"))
                                                                                                                                                                                                                                                                                !appl_6 <- appl_5 `pseq` cn (Types.Atom (Types.Str "warning: changing the type of ")) appl_5
                                                                                                                                                                                                                                                                                !appl_7 <- kl_stoutput
                                                                                                                                                                                                                                                                                appl_6 `pseq` (appl_7 `pseq` kl_shen_prhush appl_6 appl_7)))
                                                                                                                   appl_3 `pseq` applyWrapper appl_1 [appl_3])))
                                                   let !aw_8 = Types.Atom (Types.UnboundSym "shen.typecheck")
                                                   !appl_9 <- kl_V2376 `pseq` applyWrapper aw_8 [kl_V2376,
                                                                                                 Types.Atom (Types.UnboundSym "B")]
                                                   appl_9 `pseq` applyWrapper appl_0 [appl_9]

kl_shen_variantP :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_variantP (!kl_V2388) (!kl_V2389) = do !kl_if_0 <- kl_V2389 `pseq` (kl_V2388 `pseq` eq kl_V2389 kl_V2388)
                                              klIf kl_if_0 (do return (Atom (B True))) (do !kl_if_1 <- kl_V2388 `pseq` consP kl_V2388
                                                                                           !kl_if_2 <- klIf kl_if_1 (do !kl_if_3 <- kl_V2389 `pseq` consP kl_V2389
                                                                                                                        klIf kl_if_3 (do !appl_4 <- kl_V2389 `pseq` hd kl_V2389
                                                                                                                                         !appl_5 <- kl_V2388 `pseq` hd kl_V2388
                                                                                                                                         appl_4 `pseq` (appl_5 `pseq` eq appl_4 appl_5)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                           klIf kl_if_2 (do !appl_6 <- kl_V2388 `pseq` tl kl_V2388
                                                                                                            !appl_7 <- kl_V2389 `pseq` tl kl_V2389
                                                                                                            appl_6 `pseq` (appl_7 `pseq` kl_shen_variantP appl_6 appl_7)) (do !kl_if_8 <- kl_V2388 `pseq` consP kl_V2388
                                                                                                                                                                              !kl_if_9 <- klIf kl_if_8 (do !kl_if_10 <- kl_V2389 `pseq` consP kl_V2389
                                                                                                                                                                                                           klIf kl_if_10 (do !appl_11 <- kl_V2388 `pseq` hd kl_V2388
                                                                                                                                                                                                                             !kl_if_12 <- appl_11 `pseq` kl_shen_pvarP appl_11
                                                                                                                                                                                                                             klIf kl_if_12 (do !appl_13 <- kl_V2389 `pseq` hd kl_V2389
                                                                                                                                                                                                                                               appl_13 `pseq` kl_variableP appl_13) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                              klIf kl_if_9 (do !appl_14 <- kl_V2388 `pseq` hd kl_V2388
                                                                                                                                                                                               !appl_15 <- kl_V2388 `pseq` tl kl_V2388
                                                                                                                                                                                               !appl_16 <- appl_14 `pseq` (appl_15 `pseq` kl_subst (Types.Atom (Types.UnboundSym "shen.a")) appl_14 appl_15)
                                                                                                                                                                                               !appl_17 <- kl_V2389 `pseq` hd kl_V2389
                                                                                                                                                                                               !appl_18 <- kl_V2389 `pseq` tl kl_V2389
                                                                                                                                                                                               !appl_19 <- appl_17 `pseq` (appl_18 `pseq` kl_subst (Types.Atom (Types.UnboundSym "shen.a")) appl_17 appl_18)
                                                                                                                                                                                               appl_16 `pseq` (appl_19 `pseq` kl_shen_variantP appl_16 appl_19)) (do !kl_if_20 <- kl_V2388 `pseq` consP kl_V2388
                                                                                                                                                                                                                                                                     !kl_if_21 <- klIf kl_if_20 (do !appl_22 <- kl_V2388 `pseq` hd kl_V2388
                                                                                                                                                                                                                                                                                                    !kl_if_23 <- appl_22 `pseq` consP appl_22
                                                                                                                                                                                                                                                                                                    klIf kl_if_23 (do !kl_if_24 <- kl_V2389 `pseq` consP kl_V2389
                                                                                                                                                                                                                                                                                                                      klIf kl_if_24 (do !appl_25 <- kl_V2389 `pseq` hd kl_V2389
                                                                                                                                                                                                                                                                                                                                        appl_25 `pseq` consP appl_25) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                     klIf kl_if_21 (do !appl_26 <- kl_V2388 `pseq` hd kl_V2388
                                                                                                                                                                                                                                                                                       !appl_27 <- kl_V2388 `pseq` tl kl_V2388
                                                                                                                                                                                                                                                                                       !appl_28 <- appl_26 `pseq` (appl_27 `pseq` kl_append appl_26 appl_27)
                                                                                                                                                                                                                                                                                       !appl_29 <- kl_V2389 `pseq` hd kl_V2389
                                                                                                                                                                                                                                                                                       !appl_30 <- kl_V2389 `pseq` tl kl_V2389
                                                                                                                                                                                                                                                                                       !appl_31 <- appl_29 `pseq` (appl_30 `pseq` kl_append appl_29 appl_30)
                                                                                                                                                                                                                                                                                       appl_28 `pseq` (appl_31 `pseq` kl_shen_variantP appl_28 appl_31)) (do klIf (Atom (B True)) (do return (Atom (B False))) (do return (List []))))))

expr12 :: Types.KLContext Types.Env Types.KLValue
expr12 = do (do let !appl_0 = List []
                !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_0
                !appl_2 <- appl_1 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_1
                !appl_3 <- appl_2 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_2
                appl_3 `pseq` kl_declare (ApplC (wrapNamed "absvector?" absvectorP)) appl_3) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_4 = List []
                !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_4
                !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_5
                let !appl_7 = List []
                !appl_8 <- appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_7
                !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_8
                let !appl_10 = List []
                !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_11
                !appl_13 <- appl_6 `pseq` (appl_12 `pseq` klCons appl_6 appl_12)
                let !appl_14 = List []
                !appl_15 <- appl_13 `pseq` (appl_14 `pseq` klCons appl_13 appl_14)
                !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_15
                !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_16
                appl_17 `pseq` kl_declare (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_17) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_18 = List []
                !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_18
                !appl_20 <- appl_19 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_19
                !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_20
                let !appl_22 = List []
                !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_23
                !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_24
                appl_25 `pseq` kl_declare (Types.Atom (Types.UnboundSym "and")) appl_25) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_26 = List []
                !appl_27 <- appl_26 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_26
                !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_27
                !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_28
                let !appl_30 = List []
                !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                !appl_32 <- appl_31 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_31
                !appl_33 <- appl_32 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_32
                let !appl_34 = List []
                !appl_35 <- appl_33 `pseq` (appl_34 `pseq` klCons appl_33 appl_34)
                !appl_36 <- appl_35 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_35
                !appl_37 <- appl_36 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_36
                appl_37 `pseq` kl_declare (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_37) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_38 = List []
                !appl_39 <- appl_38 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_38
                !appl_40 <- appl_39 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_39
                let !appl_41 = List []
                !appl_42 <- appl_41 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_41
                !appl_43 <- appl_42 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_42
                let !appl_44 = List []
                !appl_45 <- appl_44 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_44
                !appl_46 <- appl_45 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_45
                let !appl_47 = List []
                !appl_48 <- appl_46 `pseq` (appl_47 `pseq` klCons appl_46 appl_47)
                !appl_49 <- appl_48 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_48
                !appl_50 <- appl_43 `pseq` (appl_49 `pseq` klCons appl_43 appl_49)
                let !appl_51 = List []
                !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                !appl_53 <- appl_52 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_52
                !appl_54 <- appl_40 `pseq` (appl_53 `pseq` klCons appl_40 appl_53)
                appl_54 `pseq` kl_declare (ApplC (wrapNamed "append" kl_append)) appl_54) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_55 = List []
                !appl_56 <- appl_55 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_55
                !appl_57 <- appl_56 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_56
                !appl_58 <- appl_57 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_57
                appl_58 `pseq` kl_declare (ApplC (wrapNamed "arity" kl_arity)) appl_58) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_59 = List []
                !appl_60 <- appl_59 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_59
                !appl_61 <- appl_60 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_60
                let !appl_62 = List []
                !appl_63 <- appl_61 `pseq` (appl_62 `pseq` klCons appl_61 appl_62)
                !appl_64 <- appl_63 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_63
                let !appl_65 = List []
                !appl_66 <- appl_65 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_65
                !appl_67 <- appl_66 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_66
                let !appl_68 = List []
                !appl_69 <- appl_67 `pseq` (appl_68 `pseq` klCons appl_67 appl_68)
                !appl_70 <- appl_69 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_69
                !appl_71 <- appl_64 `pseq` (appl_70 `pseq` klCons appl_64 appl_70)
                let !appl_72 = List []
                !appl_73 <- appl_71 `pseq` (appl_72 `pseq` klCons appl_71 appl_72)
                !appl_74 <- appl_73 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_73
                !appl_75 <- appl_74 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_74
                appl_75 `pseq` kl_declare (ApplC (wrapNamed "assoc" kl_assoc)) appl_75) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_76 = List []
                !appl_77 <- appl_76 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_76
                !appl_78 <- appl_77 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_77
                !appl_79 <- appl_78 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_78
                appl_79 `pseq` kl_declare (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_79) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_80 = List []
                !appl_81 <- appl_80 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_80
                !appl_82 <- appl_81 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_81
                !appl_83 <- appl_82 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_82
                appl_83 `pseq` kl_declare (ApplC (wrapNamed "bound?" kl_boundP)) appl_83) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_84 = List []
                !appl_85 <- appl_84 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_84
                !appl_86 <- appl_85 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_85
                !appl_87 <- appl_86 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_86
                appl_87 `pseq` kl_declare (ApplC (wrapNamed "cd" kl_cd)) appl_87) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_88 = List []
                !appl_89 <- appl_88 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_88
                !appl_90 <- appl_89 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_89
                let !appl_91 = List []
                !appl_92 <- appl_91 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_91
                !appl_93 <- appl_92 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_92
                let !appl_94 = List []
                !appl_95 <- appl_93 `pseq` (appl_94 `pseq` klCons appl_93 appl_94)
                !appl_96 <- appl_95 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_95
                !appl_97 <- appl_90 `pseq` (appl_96 `pseq` klCons appl_90 appl_96)
                appl_97 `pseq` kl_declare (ApplC (wrapNamed "close" closeStream)) appl_97) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_98 = List []
                !appl_99 <- appl_98 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_98
                !appl_100 <- appl_99 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_99
                !appl_101 <- appl_100 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_100
                let !appl_102 = List []
                !appl_103 <- appl_101 `pseq` (appl_102 `pseq` klCons appl_101 appl_102)
                !appl_104 <- appl_103 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_103
                !appl_105 <- appl_104 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_104
                appl_105 `pseq` kl_declare (ApplC (wrapNamed "cn" cn)) appl_105) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_106 = List []
                !appl_107 <- appl_106 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_106
                !appl_108 <- appl_107 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.==>")) appl_107
                !appl_109 <- appl_108 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_108
                let !appl_110 = List []
                !appl_111 <- appl_110 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_110
                !appl_112 <- appl_111 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_111
                !appl_113 <- appl_112 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_112
                let !appl_114 = List []
                !appl_115 <- appl_114 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_114
                !appl_116 <- appl_115 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_115
                !appl_117 <- appl_113 `pseq` (appl_116 `pseq` klCons appl_113 appl_116)
                let !appl_118 = List []
                !appl_119 <- appl_117 `pseq` (appl_118 `pseq` klCons appl_117 appl_118)
                !appl_120 <- appl_119 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_119
                !appl_121 <- appl_120 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_120
                let !appl_122 = List []
                !appl_123 <- appl_121 `pseq` (appl_122 `pseq` klCons appl_121 appl_122)
                !appl_124 <- appl_123 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_123
                !appl_125 <- appl_109 `pseq` (appl_124 `pseq` klCons appl_109 appl_124)
                appl_125 `pseq` kl_declare (ApplC (wrapNamed "compile" kl_compile)) appl_125) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_126 = List []
                !appl_127 <- appl_126 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_126
                !appl_128 <- appl_127 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_127
                !appl_129 <- appl_128 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_128
                appl_129 `pseq` kl_declare (ApplC (wrapNamed "cons?" consP)) appl_129) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_130 = List []
                !appl_131 <- appl_130 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_130
                !appl_132 <- appl_131 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_131
                !appl_133 <- appl_132 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_132
                let !appl_134 = List []
                !appl_135 <- appl_134 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_134
                !appl_136 <- appl_135 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_135
                !appl_137 <- appl_133 `pseq` (appl_136 `pseq` klCons appl_133 appl_136)
                appl_137 `pseq` kl_declare (ApplC (wrapNamed "destroy" kl_destroy)) appl_137) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_138 = List []
                !appl_139 <- appl_138 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_138
                !appl_140 <- appl_139 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_139
                let !appl_141 = List []
                !appl_142 <- appl_141 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_141
                !appl_143 <- appl_142 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_142
                let !appl_144 = List []
                !appl_145 <- appl_144 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_144
                !appl_146 <- appl_145 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_145
                let !appl_147 = List []
                !appl_148 <- appl_146 `pseq` (appl_147 `pseq` klCons appl_146 appl_147)
                !appl_149 <- appl_148 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_148
                !appl_150 <- appl_143 `pseq` (appl_149 `pseq` klCons appl_143 appl_149)
                let !appl_151 = List []
                !appl_152 <- appl_150 `pseq` (appl_151 `pseq` klCons appl_150 appl_151)
                !appl_153 <- appl_152 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_152
                !appl_154 <- appl_140 `pseq` (appl_153 `pseq` klCons appl_140 appl_153)
                appl_154 `pseq` kl_declare (ApplC (wrapNamed "difference" kl_difference)) appl_154) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_155 = List []
                !appl_156 <- appl_155 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_155
                !appl_157 <- appl_156 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_156
                !appl_158 <- appl_157 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_157
                let !appl_159 = List []
                !appl_160 <- appl_158 `pseq` (appl_159 `pseq` klCons appl_158 appl_159)
                !appl_161 <- appl_160 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_160
                !appl_162 <- appl_161 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_161
                appl_162 `pseq` kl_declare (ApplC (wrapNamed "do" kl_do)) appl_162) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_163 = List []
                !appl_164 <- appl_163 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_163
                !appl_165 <- appl_164 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_164
                let !appl_166 = List []
                !appl_167 <- appl_166 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_166
                !appl_168 <- appl_167 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_167
                let !appl_169 = List []
                !appl_170 <- appl_168 `pseq` (appl_169 `pseq` klCons appl_168 appl_169)
                !appl_171 <- appl_170 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.==>")) appl_170
                !appl_172 <- appl_165 `pseq` (appl_171 `pseq` klCons appl_165 appl_171)
                appl_172 `pseq` kl_declare (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_172) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_173 = List []
                !appl_174 <- appl_173 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_173
                !appl_175 <- appl_174 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_174
                let !appl_176 = List []
                !appl_177 <- appl_176 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_176
                !appl_178 <- appl_177 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_177
                let !appl_179 = List []
                !appl_180 <- appl_178 `pseq` (appl_179 `pseq` klCons appl_178 appl_179)
                !appl_181 <- appl_180 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.==>")) appl_180
                !appl_182 <- appl_175 `pseq` (appl_181 `pseq` klCons appl_175 appl_181)
                appl_182 `pseq` kl_declare (ApplC (wrapNamed "shen.<!>" kl_shen_LBExclRB)) appl_182) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_183 = List []
                !appl_184 <- appl_183 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_183
                !appl_185 <- appl_184 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_184
                let !appl_186 = List []
                !appl_187 <- appl_186 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_186
                !appl_188 <- appl_187 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_187
                !appl_189 <- appl_185 `pseq` (appl_188 `pseq` klCons appl_185 appl_188)
                let !appl_190 = List []
                !appl_191 <- appl_189 `pseq` (appl_190 `pseq` klCons appl_189 appl_190)
                !appl_192 <- appl_191 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_191
                !appl_193 <- appl_192 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_192
                appl_193 `pseq` kl_declare (ApplC (wrapNamed "element?" kl_elementP)) appl_193) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_194 = List []
                !appl_195 <- appl_194 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_194
                !appl_196 <- appl_195 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_195
                !appl_197 <- appl_196 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_196
                appl_197 `pseq` kl_declare (ApplC (wrapNamed "empty?" kl_emptyP)) appl_197) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_198 = List []
                !appl_199 <- appl_198 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_198
                !appl_200 <- appl_199 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_199
                !appl_201 <- appl_200 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_200
                appl_201 `pseq` kl_declare (Types.Atom (Types.UnboundSym "enable-type-theory")) appl_201) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_202 = List []
                !appl_203 <- appl_202 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_202
                !appl_204 <- appl_203 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_203
                let !appl_205 = List []
                !appl_206 <- appl_204 `pseq` (appl_205 `pseq` klCons appl_204 appl_205)
                !appl_207 <- appl_206 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_206
                !appl_208 <- appl_207 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_207
                appl_208 `pseq` kl_declare (ApplC (wrapNamed "external" kl_external)) appl_208) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_209 = List []
                !appl_210 <- appl_209 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_209
                !appl_211 <- appl_210 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_210
                !appl_212 <- appl_211 `pseq` klCons (Types.Atom (Types.UnboundSym "exception")) appl_211
                appl_212 `pseq` kl_declare (ApplC (wrapNamed "error-to-string" errorToString)) appl_212) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_213 = List []
                !appl_214 <- appl_213 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_213
                !appl_215 <- appl_214 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_214
                let !appl_216 = List []
                !appl_217 <- appl_215 `pseq` (appl_216 `pseq` klCons appl_215 appl_216)
                !appl_218 <- appl_217 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_217
                !appl_219 <- appl_218 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_218
                appl_219 `pseq` kl_declare (ApplC (wrapNamed "explode" kl_explode)) appl_219) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_220 = List []
                !appl_221 <- appl_220 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_220
                !appl_222 <- appl_221 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_221
                appl_222 `pseq` kl_declare (ApplC (PL "fail" kl_fail)) appl_222) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_223 = List []
                !appl_224 <- appl_223 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_223
                !appl_225 <- appl_224 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_224
                !appl_226 <- appl_225 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_225
                let !appl_227 = List []
                !appl_228 <- appl_227 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_227
                !appl_229 <- appl_228 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_228
                !appl_230 <- appl_229 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_229
                let !appl_231 = List []
                !appl_232 <- appl_230 `pseq` (appl_231 `pseq` klCons appl_230 appl_231)
                !appl_233 <- appl_232 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_232
                !appl_234 <- appl_226 `pseq` (appl_233 `pseq` klCons appl_226 appl_233)
                appl_234 `pseq` kl_declare (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_234) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_235 = List []
                !appl_236 <- appl_235 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_235
                !appl_237 <- appl_236 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_236
                !appl_238 <- appl_237 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_237
                let !appl_239 = List []
                !appl_240 <- appl_239 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_239
                !appl_241 <- appl_240 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_240
                !appl_242 <- appl_241 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_241
                let !appl_243 = List []
                !appl_244 <- appl_242 `pseq` (appl_243 `pseq` klCons appl_242 appl_243)
                !appl_245 <- appl_244 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_244
                !appl_246 <- appl_238 `pseq` (appl_245 `pseq` klCons appl_238 appl_245)
                appl_246 `pseq` kl_declare (ApplC (wrapNamed "fix" kl_fix)) appl_246) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_247 = List []
                !appl_248 <- appl_247 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_247
                !appl_249 <- appl_248 `pseq` klCons (Types.Atom (Types.UnboundSym "lazy")) appl_248
                let !appl_250 = List []
                !appl_251 <- appl_249 `pseq` (appl_250 `pseq` klCons appl_249 appl_250)
                !appl_252 <- appl_251 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_251
                !appl_253 <- appl_252 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_252
                appl_253 `pseq` kl_declare (Types.Atom (Types.UnboundSym "freeze")) appl_253) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_254 = List []
                !appl_255 <- appl_254 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_254
                !appl_256 <- appl_255 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_255
                let !appl_257 = List []
                !appl_258 <- appl_257 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_257
                !appl_259 <- appl_258 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_258
                let !appl_260 = List []
                !appl_261 <- appl_259 `pseq` (appl_260 `pseq` klCons appl_259 appl_260)
                !appl_262 <- appl_261 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_261
                !appl_263 <- appl_256 `pseq` (appl_262 `pseq` klCons appl_256 appl_262)
                appl_263 `pseq` kl_declare (Types.Atom (Types.UnboundSym "shen.freezit")) appl_263) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_264 = List []
                !appl_265 <- appl_264 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_264
                !appl_266 <- appl_265 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_265
                !appl_267 <- appl_266 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_266
                let !appl_268 = List []
                !appl_269 <- appl_268 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_268
                !appl_270 <- appl_269 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_269
                !appl_271 <- appl_267 `pseq` (appl_270 `pseq` klCons appl_267 appl_270)
                appl_271 `pseq` kl_declare (ApplC (wrapNamed "fst" kl_fst)) appl_271) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_272 = List []
                !appl_273 <- appl_272 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_272
                !appl_274 <- appl_273 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_273
                !appl_275 <- appl_274 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_274
                appl_275 `pseq` kl_declare (ApplC (wrapNamed "gensym" kl_gensym)) appl_275) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_276 = List []
                !appl_277 <- appl_276 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_276
                !appl_278 <- appl_277 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_277
                let !appl_279 = List []
                !appl_280 <- appl_279 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_279
                !appl_281 <- appl_280 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_280
                !appl_282 <- appl_281 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_281
                let !appl_283 = List []
                !appl_284 <- appl_282 `pseq` (appl_283 `pseq` klCons appl_282 appl_283)
                !appl_285 <- appl_284 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_284
                !appl_286 <- appl_278 `pseq` (appl_285 `pseq` klCons appl_278 appl_285)
                appl_286 `pseq` kl_declare (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_286) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_287 = List []
                !appl_288 <- appl_287 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_287
                !appl_289 <- appl_288 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_288
                let !appl_290 = List []
                !appl_291 <- appl_290 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_290
                !appl_292 <- appl_291 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_291
                let !appl_293 = List []
                !appl_294 <- appl_292 `pseq` (appl_293 `pseq` klCons appl_292 appl_293)
                !appl_295 <- appl_294 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_294
                !appl_296 <- appl_295 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_295
                let !appl_297 = List []
                !appl_298 <- appl_296 `pseq` (appl_297 `pseq` klCons appl_296 appl_297)
                !appl_299 <- appl_298 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_298
                !appl_300 <- appl_299 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_299
                let !appl_301 = List []
                !appl_302 <- appl_300 `pseq` (appl_301 `pseq` klCons appl_300 appl_301)
                !appl_303 <- appl_302 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_302
                !appl_304 <- appl_289 `pseq` (appl_303 `pseq` klCons appl_289 appl_303)
                appl_304 `pseq` kl_declare (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_304) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_305 = List []
                !appl_306 <- appl_305 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_305
                !appl_307 <- appl_306 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_306
                let !appl_308 = List []
                !appl_309 <- appl_307 `pseq` (appl_308 `pseq` klCons appl_307 appl_308)
                !appl_310 <- appl_309 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_309
                !appl_311 <- appl_310 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_310
                appl_311 `pseq` kl_declare (ApplC (wrapNamed "vector" kl_vector)) appl_311) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_312 = List []
                !appl_313 <- appl_312 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_312
                !appl_314 <- appl_313 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_313
                !appl_315 <- appl_314 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_314
                appl_315 `pseq` kl_declare (ApplC (wrapNamed "get-time" getTime)) appl_315) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_316 = List []
                !appl_317 <- appl_316 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_316
                !appl_318 <- appl_317 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_317
                !appl_319 <- appl_318 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_318
                let !appl_320 = List []
                !appl_321 <- appl_319 `pseq` (appl_320 `pseq` klCons appl_319 appl_320)
                !appl_322 <- appl_321 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_321
                !appl_323 <- appl_322 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_322
                appl_323 `pseq` kl_declare (ApplC (wrapNamed "hash" kl_hash)) appl_323) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_324 = List []
                !appl_325 <- appl_324 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_324
                !appl_326 <- appl_325 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_325
                let !appl_327 = List []
                !appl_328 <- appl_327 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_327
                !appl_329 <- appl_328 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_328
                !appl_330 <- appl_326 `pseq` (appl_329 `pseq` klCons appl_326 appl_329)
                appl_330 `pseq` kl_declare (ApplC (wrapNamed "head" kl_head)) appl_330) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_331 = List []
                !appl_332 <- appl_331 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_331
                !appl_333 <- appl_332 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_332
                let !appl_334 = List []
                !appl_335 <- appl_334 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_334
                !appl_336 <- appl_335 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_335
                !appl_337 <- appl_333 `pseq` (appl_336 `pseq` klCons appl_333 appl_336)
                appl_337 `pseq` kl_declare (ApplC (wrapNamed "hdv" kl_hdv)) appl_337) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_338 = List []
                !appl_339 <- appl_338 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_338
                !appl_340 <- appl_339 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_339
                !appl_341 <- appl_340 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_340
                appl_341 `pseq` kl_declare (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_341) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_342 = List []
                !appl_343 <- appl_342 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_342
                !appl_344 <- appl_343 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_343
                !appl_345 <- appl_344 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_344
                let !appl_346 = List []
                !appl_347 <- appl_345 `pseq` (appl_346 `pseq` klCons appl_345 appl_346)
                !appl_348 <- appl_347 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_347
                !appl_349 <- appl_348 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_348
                let !appl_350 = List []
                !appl_351 <- appl_349 `pseq` (appl_350 `pseq` klCons appl_349 appl_350)
                !appl_352 <- appl_351 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_351
                !appl_353 <- appl_352 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_352
                appl_353 `pseq` kl_declare (Types.Atom (Types.UnboundSym "if")) appl_353) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_354 = List []
                !appl_355 <- appl_354 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_354
                !appl_356 <- appl_355 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_355
                appl_356 `pseq` kl_declare (ApplC (PL "it" kl_it)) appl_356) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_357 = List []
                !appl_358 <- appl_357 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_357
                !appl_359 <- appl_358 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_358
                appl_359 `pseq` kl_declare (ApplC (PL "implementation" kl_implementation)) appl_359) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_360 = List []
                !appl_361 <- appl_360 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_360
                !appl_362 <- appl_361 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_361
                let !appl_363 = List []
                !appl_364 <- appl_363 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_363
                !appl_365 <- appl_364 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_364
                let !appl_366 = List []
                !appl_367 <- appl_365 `pseq` (appl_366 `pseq` klCons appl_365 appl_366)
                !appl_368 <- appl_367 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_367
                !appl_369 <- appl_362 `pseq` (appl_368 `pseq` klCons appl_362 appl_368)
                appl_369 `pseq` kl_declare (ApplC (wrapNamed "include" kl_include)) appl_369) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_370 = List []
                !appl_371 <- appl_370 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_370
                !appl_372 <- appl_371 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_371
                let !appl_373 = List []
                !appl_374 <- appl_373 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_373
                !appl_375 <- appl_374 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_374
                let !appl_376 = List []
                !appl_377 <- appl_375 `pseq` (appl_376 `pseq` klCons appl_375 appl_376)
                !appl_378 <- appl_377 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_377
                !appl_379 <- appl_372 `pseq` (appl_378 `pseq` klCons appl_372 appl_378)
                appl_379 `pseq` kl_declare (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_379) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_380 = List []
                !appl_381 <- appl_380 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_380
                !appl_382 <- appl_381 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_381
                appl_382 `pseq` kl_declare (ApplC (PL "inferences" kl_inferences)) appl_382) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_383 = List []
                !appl_384 <- appl_383 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_383
                !appl_385 <- appl_384 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_384
                !appl_386 <- appl_385 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_385
                let !appl_387 = List []
                !appl_388 <- appl_386 `pseq` (appl_387 `pseq` klCons appl_386 appl_387)
                !appl_389 <- appl_388 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_388
                !appl_390 <- appl_389 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_389
                appl_390 `pseq` kl_declare (ApplC (wrapNamed "shen.insert" kl_shen_insert)) appl_390) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_391 = List []
                !appl_392 <- appl_391 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_391
                !appl_393 <- appl_392 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_392
                !appl_394 <- appl_393 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_393
                appl_394 `pseq` kl_declare (ApplC (wrapNamed "integer?" kl_integerP)) appl_394) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_395 = List []
                !appl_396 <- appl_395 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_395
                !appl_397 <- appl_396 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_396
                let !appl_398 = List []
                !appl_399 <- appl_398 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_398
                !appl_400 <- appl_399 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_399
                let !appl_401 = List []
                !appl_402 <- appl_401 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_401
                !appl_403 <- appl_402 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_402
                let !appl_404 = List []
                !appl_405 <- appl_403 `pseq` (appl_404 `pseq` klCons appl_403 appl_404)
                !appl_406 <- appl_405 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_405
                !appl_407 <- appl_400 `pseq` (appl_406 `pseq` klCons appl_400 appl_406)
                let !appl_408 = List []
                !appl_409 <- appl_407 `pseq` (appl_408 `pseq` klCons appl_407 appl_408)
                !appl_410 <- appl_409 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_409
                !appl_411 <- appl_397 `pseq` (appl_410 `pseq` klCons appl_397 appl_410)
                appl_411 `pseq` kl_declare (ApplC (wrapNamed "intersection" kl_intersection)) appl_411) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_412 = List []
                !appl_413 <- appl_412 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_412
                !appl_414 <- appl_413 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_413
                appl_414 `pseq` kl_declare (ApplC (PL "kill" kl_kill)) appl_414) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_415 = List []
                !appl_416 <- appl_415 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_415
                !appl_417 <- appl_416 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_416
                appl_417 `pseq` kl_declare (ApplC (PL "language" kl_language)) appl_417) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_418 = List []
                !appl_419 <- appl_418 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_418
                !appl_420 <- appl_419 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_419
                let !appl_421 = List []
                !appl_422 <- appl_421 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_421
                !appl_423 <- appl_422 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_422
                !appl_424 <- appl_420 `pseq` (appl_423 `pseq` klCons appl_420 appl_423)
                appl_424 `pseq` kl_declare (ApplC (wrapNamed "length" kl_length)) appl_424) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_425 = List []
                !appl_426 <- appl_425 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_425
                !appl_427 <- appl_426 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_426
                let !appl_428 = List []
                !appl_429 <- appl_428 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_428
                !appl_430 <- appl_429 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_429
                !appl_431 <- appl_427 `pseq` (appl_430 `pseq` klCons appl_427 appl_430)
                appl_431 `pseq` kl_declare (ApplC (wrapNamed "limit" kl_limit)) appl_431) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_432 = List []
                !appl_433 <- appl_432 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_432
                !appl_434 <- appl_433 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_433
                !appl_435 <- appl_434 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_434
                appl_435 `pseq` kl_declare (ApplC (wrapNamed "load" kl_load)) appl_435) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_436 = List []
                !appl_437 <- appl_436 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_436
                !appl_438 <- appl_437 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_437
                !appl_439 <- appl_438 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_438
                let !appl_440 = List []
                !appl_441 <- appl_440 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_440
                !appl_442 <- appl_441 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_441
                let !appl_443 = List []
                !appl_444 <- appl_443 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_443
                !appl_445 <- appl_444 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_444
                let !appl_446 = List []
                !appl_447 <- appl_445 `pseq` (appl_446 `pseq` klCons appl_445 appl_446)
                !appl_448 <- appl_447 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_447
                !appl_449 <- appl_442 `pseq` (appl_448 `pseq` klCons appl_442 appl_448)
                let !appl_450 = List []
                !appl_451 <- appl_449 `pseq` (appl_450 `pseq` klCons appl_449 appl_450)
                !appl_452 <- appl_451 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_451
                !appl_453 <- appl_439 `pseq` (appl_452 `pseq` klCons appl_439 appl_452)
                appl_453 `pseq` kl_declare (ApplC (wrapNamed "map" kl_map)) appl_453) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_454 = List []
                !appl_455 <- appl_454 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_454
                !appl_456 <- appl_455 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_455
                let !appl_457 = List []
                !appl_458 <- appl_456 `pseq` (appl_457 `pseq` klCons appl_456 appl_457)
                !appl_459 <- appl_458 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_458
                !appl_460 <- appl_459 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_459
                let !appl_461 = List []
                !appl_462 <- appl_461 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_461
                !appl_463 <- appl_462 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_462
                let !appl_464 = List []
                !appl_465 <- appl_464 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_464
                !appl_466 <- appl_465 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_465
                let !appl_467 = List []
                !appl_468 <- appl_466 `pseq` (appl_467 `pseq` klCons appl_466 appl_467)
                !appl_469 <- appl_468 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_468
                !appl_470 <- appl_463 `pseq` (appl_469 `pseq` klCons appl_463 appl_469)
                let !appl_471 = List []
                !appl_472 <- appl_470 `pseq` (appl_471 `pseq` klCons appl_470 appl_471)
                !appl_473 <- appl_472 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_472
                !appl_474 <- appl_460 `pseq` (appl_473 `pseq` klCons appl_460 appl_473)
                appl_474 `pseq` kl_declare (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_474) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_475 = List []
                !appl_476 <- appl_475 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_475
                !appl_477 <- appl_476 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_476
                !appl_478 <- appl_477 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_477
                appl_478 `pseq` kl_declare (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_478) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_479 = List []
                !appl_480 <- appl_479 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_479
                !appl_481 <- appl_480 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_480
                !appl_482 <- appl_481 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_481
                appl_482 `pseq` kl_declare (ApplC (wrapNamed "n->string" nToString)) appl_482) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_483 = List []
                !appl_484 <- appl_483 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_483
                !appl_485 <- appl_484 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_484
                !appl_486 <- appl_485 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_485
                appl_486 `pseq` kl_declare (ApplC (wrapNamed "nl" kl_nl)) appl_486) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_487 = List []
                !appl_488 <- appl_487 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_487
                !appl_489 <- appl_488 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_488
                !appl_490 <- appl_489 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_489
                appl_490 `pseq` kl_declare (ApplC (wrapNamed "not" kl_not)) appl_490) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_491 = List []
                !appl_492 <- appl_491 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_491
                !appl_493 <- appl_492 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_492
                let !appl_494 = List []
                !appl_495 <- appl_494 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_494
                !appl_496 <- appl_495 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_495
                !appl_497 <- appl_493 `pseq` (appl_496 `pseq` klCons appl_493 appl_496)
                let !appl_498 = List []
                !appl_499 <- appl_497 `pseq` (appl_498 `pseq` klCons appl_497 appl_498)
                !appl_500 <- appl_499 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_499
                !appl_501 <- appl_500 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_500
                appl_501 `pseq` kl_declare (ApplC (wrapNamed "nth" kl_nth)) appl_501) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_502 = List []
                !appl_503 <- appl_502 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_502
                !appl_504 <- appl_503 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_503
                !appl_505 <- appl_504 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_504
                appl_505 `pseq` kl_declare (ApplC (wrapNamed "number?" numberP)) appl_505) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_506 = List []
                !appl_507 <- appl_506 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_506
                !appl_508 <- appl_507 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_507
                !appl_509 <- appl_508 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_508
                let !appl_510 = List []
                !appl_511 <- appl_509 `pseq` (appl_510 `pseq` klCons appl_509 appl_510)
                !appl_512 <- appl_511 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_511
                !appl_513 <- appl_512 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_512
                appl_513 `pseq` kl_declare (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_513) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_514 = List []
                !appl_515 <- appl_514 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_514
                !appl_516 <- appl_515 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_515
                !appl_517 <- appl_516 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_516
                appl_517 `pseq` kl_declare (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_517) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_518 = List []
                !appl_519 <- appl_518 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_518
                !appl_520 <- appl_519 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_519
                !appl_521 <- appl_520 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_520
                appl_521 `pseq` kl_declare (ApplC (wrapNamed "optimise" kl_optimise)) appl_521) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_522 = List []
                !appl_523 <- appl_522 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_522
                !appl_524 <- appl_523 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_523
                !appl_525 <- appl_524 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_524
                let !appl_526 = List []
                !appl_527 <- appl_525 `pseq` (appl_526 `pseq` klCons appl_525 appl_526)
                !appl_528 <- appl_527 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_527
                !appl_529 <- appl_528 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_528
                appl_529 `pseq` kl_declare (Types.Atom (Types.UnboundSym "or")) appl_529) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_530 = List []
                !appl_531 <- appl_530 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_530
                !appl_532 <- appl_531 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_531
                appl_532 `pseq` kl_declare (ApplC (PL "os" kl_os)) appl_532) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_533 = List []
                !appl_534 <- appl_533 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_533
                !appl_535 <- appl_534 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_534
                !appl_536 <- appl_535 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_535
                appl_536 `pseq` kl_declare (ApplC (wrapNamed "package?" kl_packageP)) appl_536) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_537 = List []
                !appl_538 <- appl_537 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_537
                !appl_539 <- appl_538 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_538
                appl_539 `pseq` kl_declare (ApplC (PL "port" kl_port)) appl_539) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_540 = List []
                !appl_541 <- appl_540 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_540
                !appl_542 <- appl_541 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_541
                appl_542 `pseq` kl_declare (ApplC (PL "porters" kl_porters)) appl_542) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_543 = List []
                !appl_544 <- appl_543 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_543
                !appl_545 <- appl_544 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_544
                !appl_546 <- appl_545 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_545
                let !appl_547 = List []
                !appl_548 <- appl_546 `pseq` (appl_547 `pseq` klCons appl_546 appl_547)
                !appl_549 <- appl_548 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_548
                !appl_550 <- appl_549 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_549
                appl_550 `pseq` kl_declare (ApplC (wrapNamed "pos" pos)) appl_550) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_551 = List []
                !appl_552 <- appl_551 `pseq` klCons (Types.Atom (Types.UnboundSym "out")) appl_551
                !appl_553 <- appl_552 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_552
                let !appl_554 = List []
                !appl_555 <- appl_554 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_554
                !appl_556 <- appl_555 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_555
                !appl_557 <- appl_553 `pseq` (appl_556 `pseq` klCons appl_553 appl_556)
                let !appl_558 = List []
                !appl_559 <- appl_557 `pseq` (appl_558 `pseq` klCons appl_557 appl_558)
                !appl_560 <- appl_559 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_559
                !appl_561 <- appl_560 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_560
                appl_561 `pseq` kl_declare (ApplC (wrapNamed "pr" kl_pr)) appl_561) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_562 = List []
                !appl_563 <- appl_562 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_562
                !appl_564 <- appl_563 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_563
                !appl_565 <- appl_564 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_564
                appl_565 `pseq` kl_declare (ApplC (wrapNamed "print" kl_print)) appl_565) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_566 = List []
                !appl_567 <- appl_566 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_566
                !appl_568 <- appl_567 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_567
                !appl_569 <- appl_568 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_568
                let !appl_570 = List []
                !appl_571 <- appl_570 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_570
                !appl_572 <- appl_571 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_571
                !appl_573 <- appl_572 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_572
                let !appl_574 = List []
                !appl_575 <- appl_573 `pseq` (appl_574 `pseq` klCons appl_573 appl_574)
                !appl_576 <- appl_575 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_575
                !appl_577 <- appl_569 `pseq` (appl_576 `pseq` klCons appl_569 appl_576)
                appl_577 `pseq` kl_declare (ApplC (wrapNamed "profile" kl_profile)) appl_577) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_578 = List []
                !appl_579 <- appl_578 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_578
                !appl_580 <- appl_579 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_579
                let !appl_581 = List []
                !appl_582 <- appl_581 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_581
                !appl_583 <- appl_582 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_582
                let !appl_584 = List []
                !appl_585 <- appl_583 `pseq` (appl_584 `pseq` klCons appl_583 appl_584)
                !appl_586 <- appl_585 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_585
                !appl_587 <- appl_580 `pseq` (appl_586 `pseq` klCons appl_580 appl_586)
                appl_587 `pseq` kl_declare (ApplC (wrapNamed "preclude" kl_preclude)) appl_587) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_588 = List []
                !appl_589 <- appl_588 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_588
                !appl_590 <- appl_589 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_589
                !appl_591 <- appl_590 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_590
                appl_591 `pseq` kl_declare (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl)) appl_591) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_592 = List []
                !appl_593 <- appl_592 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_592
                !appl_594 <- appl_593 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_593
                !appl_595 <- appl_594 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_594
                let !appl_596 = List []
                !appl_597 <- appl_596 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_596
                !appl_598 <- appl_597 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_597
                !appl_599 <- appl_598 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_598
                let !appl_600 = List []
                !appl_601 <- appl_600 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_600
                !appl_602 <- appl_601 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_601
                !appl_603 <- appl_599 `pseq` (appl_602 `pseq` klCons appl_599 appl_602)
                let !appl_604 = List []
                !appl_605 <- appl_603 `pseq` (appl_604 `pseq` klCons appl_603 appl_604)
                !appl_606 <- appl_605 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_605
                !appl_607 <- appl_595 `pseq` (appl_606 `pseq` klCons appl_595 appl_606)
                appl_607 `pseq` kl_declare (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_607) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_608 = List []
                !appl_609 <- appl_608 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_608
                !appl_610 <- appl_609 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_609
                !appl_611 <- appl_610 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_610
                appl_611 `pseq` kl_declare (ApplC (wrapNamed "protect" kl_protect)) appl_611) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_612 = List []
                !appl_613 <- appl_612 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_612
                !appl_614 <- appl_613 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_613
                let !appl_615 = List []
                !appl_616 <- appl_615 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_615
                !appl_617 <- appl_616 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_616
                let !appl_618 = List []
                !appl_619 <- appl_617 `pseq` (appl_618 `pseq` klCons appl_617 appl_618)
                !appl_620 <- appl_619 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_619
                !appl_621 <- appl_614 `pseq` (appl_620 `pseq` klCons appl_614 appl_620)
                appl_621 `pseq` kl_declare (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_621) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_622 = List []
                !appl_623 <- appl_622 `pseq` klCons (Types.Atom (Types.UnboundSym "out")) appl_622
                !appl_624 <- appl_623 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_623
                let !appl_625 = List []
                !appl_626 <- appl_625 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_625
                !appl_627 <- appl_626 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_626
                !appl_628 <- appl_624 `pseq` (appl_627 `pseq` klCons appl_624 appl_627)
                let !appl_629 = List []
                !appl_630 <- appl_628 `pseq` (appl_629 `pseq` klCons appl_628 appl_629)
                !appl_631 <- appl_630 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_630
                !appl_632 <- appl_631 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_631
                appl_632 `pseq` kl_declare (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_632) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_633 = List []
                !appl_634 <- appl_633 `pseq` klCons (Types.Atom (Types.UnboundSym "unit")) appl_633
                !appl_635 <- appl_634 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_634
                let !appl_636 = List []
                !appl_637 <- appl_635 `pseq` (appl_636 `pseq` klCons appl_635 appl_636)
                !appl_638 <- appl_637 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_637
                !appl_639 <- appl_638 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_638
                appl_639 `pseq` kl_declare (ApplC (wrapNamed "ps" kl_ps)) appl_639) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_640 = List []
                !appl_641 <- appl_640 `pseq` klCons (Types.Atom (Types.UnboundSym "in")) appl_640
                !appl_642 <- appl_641 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_641
                let !appl_643 = List []
                !appl_644 <- appl_643 `pseq` klCons (Types.Atom (Types.UnboundSym "unit")) appl_643
                !appl_645 <- appl_644 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_644
                !appl_646 <- appl_642 `pseq` (appl_645 `pseq` klCons appl_642 appl_645)
                appl_646 `pseq` kl_declare (ApplC (wrapNamed "read" kl_read)) appl_646) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_647 = List []
                !appl_648 <- appl_647 `pseq` klCons (Types.Atom (Types.UnboundSym "in")) appl_647
                !appl_649 <- appl_648 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_648
                let !appl_650 = List []
                !appl_651 <- appl_650 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_650
                !appl_652 <- appl_651 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_651
                !appl_653 <- appl_649 `pseq` (appl_652 `pseq` klCons appl_649 appl_652)
                appl_653 `pseq` kl_declare (ApplC (wrapNamed "read-byte" readByte)) appl_653) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_654 = List []
                !appl_655 <- appl_654 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_654
                !appl_656 <- appl_655 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_655
                let !appl_657 = List []
                !appl_658 <- appl_656 `pseq` (appl_657 `pseq` klCons appl_656 appl_657)
                !appl_659 <- appl_658 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_658
                !appl_660 <- appl_659 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_659
                appl_660 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-bytelist" kl_read_file_as_bytelist)) appl_660) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_661 = List []
                !appl_662 <- appl_661 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_661
                !appl_663 <- appl_662 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_662
                !appl_664 <- appl_663 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_663
                appl_664 `pseq` kl_declare (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_664) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_665 = List []
                !appl_666 <- appl_665 `pseq` klCons (Types.Atom (Types.UnboundSym "unit")) appl_665
                !appl_667 <- appl_666 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_666
                let !appl_668 = List []
                !appl_669 <- appl_667 `pseq` (appl_668 `pseq` klCons appl_667 appl_668)
                !appl_670 <- appl_669 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_669
                !appl_671 <- appl_670 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_670
                appl_671 `pseq` kl_declare (ApplC (wrapNamed "read-file" kl_read_file)) appl_671) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_672 = List []
                !appl_673 <- appl_672 `pseq` klCons (Types.Atom (Types.UnboundSym "unit")) appl_672
                !appl_674 <- appl_673 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_673
                let !appl_675 = List []
                !appl_676 <- appl_674 `pseq` (appl_675 `pseq` klCons appl_674 appl_675)
                !appl_677 <- appl_676 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_676
                !appl_678 <- appl_677 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_677
                appl_678 `pseq` kl_declare (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_678) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_679 = List []
                !appl_680 <- appl_679 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_679
                !appl_681 <- appl_680 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_680
                appl_681 `pseq` kl_declare (ApplC (PL "release" kl_release)) appl_681) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_682 = List []
                !appl_683 <- appl_682 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_682
                !appl_684 <- appl_683 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_683
                let !appl_685 = List []
                !appl_686 <- appl_685 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_685
                !appl_687 <- appl_686 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_686
                let !appl_688 = List []
                !appl_689 <- appl_687 `pseq` (appl_688 `pseq` klCons appl_687 appl_688)
                !appl_690 <- appl_689 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_689
                !appl_691 <- appl_684 `pseq` (appl_690 `pseq` klCons appl_684 appl_690)
                let !appl_692 = List []
                !appl_693 <- appl_691 `pseq` (appl_692 `pseq` klCons appl_691 appl_692)
                !appl_694 <- appl_693 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_693
                !appl_695 <- appl_694 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_694
                appl_695 `pseq` kl_declare (ApplC (wrapNamed "remove" kl_remove)) appl_695) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_696 = List []
                !appl_697 <- appl_696 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_696
                !appl_698 <- appl_697 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_697
                let !appl_699 = List []
                !appl_700 <- appl_699 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_699
                !appl_701 <- appl_700 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_700
                let !appl_702 = List []
                !appl_703 <- appl_701 `pseq` (appl_702 `pseq` klCons appl_701 appl_702)
                !appl_704 <- appl_703 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_703
                !appl_705 <- appl_698 `pseq` (appl_704 `pseq` klCons appl_698 appl_704)
                appl_705 `pseq` kl_declare (ApplC (wrapNamed "reverse" kl_reverse)) appl_705) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_706 = List []
                !appl_707 <- appl_706 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_706
                !appl_708 <- appl_707 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_707
                !appl_709 <- appl_708 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_708
                appl_709 `pseq` kl_declare (ApplC (wrapNamed "simple-error" simpleError)) appl_709) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_710 = List []
                !appl_711 <- appl_710 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_710
                !appl_712 <- appl_711 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_711
                !appl_713 <- appl_712 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_712
                let !appl_714 = List []
                !appl_715 <- appl_714 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_714
                !appl_716 <- appl_715 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_715
                !appl_717 <- appl_713 `pseq` (appl_716 `pseq` klCons appl_713 appl_716)
                appl_717 `pseq` kl_declare (ApplC (wrapNamed "snd" kl_snd)) appl_717) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_718 = List []
                !appl_719 <- appl_718 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_718
                !appl_720 <- appl_719 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_719
                !appl_721 <- appl_720 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_720
                appl_721 `pseq` kl_declare (ApplC (wrapNamed "specialise" kl_specialise)) appl_721) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_722 = List []
                !appl_723 <- appl_722 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_722
                !appl_724 <- appl_723 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_723
                !appl_725 <- appl_724 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_724
                appl_725 `pseq` kl_declare (ApplC (wrapNamed "spy" kl_spy)) appl_725) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_726 = List []
                !appl_727 <- appl_726 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_726
                !appl_728 <- appl_727 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_727
                !appl_729 <- appl_728 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_728
                appl_729 `pseq` kl_declare (ApplC (wrapNamed "step" kl_step)) appl_729) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_730 = List []
                !appl_731 <- appl_730 `pseq` klCons (Types.Atom (Types.UnboundSym "in")) appl_730
                !appl_732 <- appl_731 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_731
                let !appl_733 = List []
                !appl_734 <- appl_732 `pseq` (appl_733 `pseq` klCons appl_732 appl_733)
                !appl_735 <- appl_734 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_734
                appl_735 `pseq` kl_declare (ApplC (PL "stinput" kl_stinput)) appl_735) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_736 = List []
                !appl_737 <- appl_736 `pseq` klCons (Types.Atom (Types.UnboundSym "out")) appl_736
                !appl_738 <- appl_737 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_737
                let !appl_739 = List []
                !appl_740 <- appl_738 `pseq` (appl_739 `pseq` klCons appl_738 appl_739)
                !appl_741 <- appl_740 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_740
                appl_741 `pseq` kl_declare (ApplC (PL "stoutput" kl_stoutput)) appl_741) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_742 = List []
                !appl_743 <- appl_742 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_742
                !appl_744 <- appl_743 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_743
                !appl_745 <- appl_744 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_744
                appl_745 `pseq` kl_declare (ApplC (wrapNamed "string?" stringP)) appl_745) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_746 = List []
                !appl_747 <- appl_746 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_746
                !appl_748 <- appl_747 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_747
                !appl_749 <- appl_748 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_748
                appl_749 `pseq` kl_declare (ApplC (wrapNamed "str" str)) appl_749) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_750 = List []
                !appl_751 <- appl_750 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_750
                !appl_752 <- appl_751 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_751
                !appl_753 <- appl_752 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_752
                appl_753 `pseq` kl_declare (ApplC (wrapNamed "string->n" stringToN)) appl_753) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_754 = List []
                !appl_755 <- appl_754 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_754
                !appl_756 <- appl_755 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_755
                !appl_757 <- appl_756 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_756
                appl_757 `pseq` kl_declare (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_757) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_758 = List []
                !appl_759 <- appl_758 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_758
                !appl_760 <- appl_759 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_759
                let !appl_761 = List []
                !appl_762 <- appl_761 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_761
                !appl_763 <- appl_762 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_762
                !appl_764 <- appl_760 `pseq` (appl_763 `pseq` klCons appl_760 appl_763)
                appl_764 `pseq` kl_declare (ApplC (wrapNamed "sum" kl_sum)) appl_764) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_765 = List []
                !appl_766 <- appl_765 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_765
                !appl_767 <- appl_766 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_766
                !appl_768 <- appl_767 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_767
                appl_768 `pseq` kl_declare (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_768) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_769 = List []
                !appl_770 <- appl_769 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_769
                !appl_771 <- appl_770 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_770
                !appl_772 <- appl_771 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_771
                appl_772 `pseq` kl_declare (ApplC (wrapNamed "systemf" kl_systemf)) appl_772) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_773 = List []
                !appl_774 <- appl_773 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_773
                !appl_775 <- appl_774 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_774
                let !appl_776 = List []
                !appl_777 <- appl_776 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_776
                !appl_778 <- appl_777 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_777
                let !appl_779 = List []
                !appl_780 <- appl_778 `pseq` (appl_779 `pseq` klCons appl_778 appl_779)
                !appl_781 <- appl_780 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_780
                !appl_782 <- appl_775 `pseq` (appl_781 `pseq` klCons appl_775 appl_781)
                appl_782 `pseq` kl_declare (ApplC (wrapNamed "tail" kl_tail)) appl_782) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_783 = List []
                !appl_784 <- appl_783 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_783
                !appl_785 <- appl_784 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_784
                !appl_786 <- appl_785 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_785
                appl_786 `pseq` kl_declare (ApplC (wrapNamed "tlstr" tlstr)) appl_786) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_787 = List []
                !appl_788 <- appl_787 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_787
                !appl_789 <- appl_788 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_788
                let !appl_790 = List []
                !appl_791 <- appl_790 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_790
                !appl_792 <- appl_791 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_791
                let !appl_793 = List []
                !appl_794 <- appl_792 `pseq` (appl_793 `pseq` klCons appl_792 appl_793)
                !appl_795 <- appl_794 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_794
                !appl_796 <- appl_789 `pseq` (appl_795 `pseq` klCons appl_789 appl_795)
                appl_796 `pseq` kl_declare (ApplC (wrapNamed "tlv" kl_tlv)) appl_796) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_797 = List []
                !appl_798 <- appl_797 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_797
                !appl_799 <- appl_798 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_798
                !appl_800 <- appl_799 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_799
                appl_800 `pseq` kl_declare (ApplC (wrapNamed "tc" kl_tc)) appl_800) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_801 = List []
                !appl_802 <- appl_801 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_801
                !appl_803 <- appl_802 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_802
                appl_803 `pseq` kl_declare (ApplC (PL "tc?" kl_tcP)) appl_803) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_804 = List []
                !appl_805 <- appl_804 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_804
                !appl_806 <- appl_805 `pseq` klCons (Types.Atom (Types.UnboundSym "lazy")) appl_805
                let !appl_807 = List []
                !appl_808 <- appl_807 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_807
                !appl_809 <- appl_808 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_808
                !appl_810 <- appl_806 `pseq` (appl_809 `pseq` klCons appl_806 appl_809)
                appl_810 `pseq` kl_declare (ApplC (wrapNamed "thaw" kl_thaw)) appl_810) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_811 = List []
                !appl_812 <- appl_811 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_811
                !appl_813 <- appl_812 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_812
                !appl_814 <- appl_813 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_813
                appl_814 `pseq` kl_declare (ApplC (wrapNamed "track" kl_track)) appl_814) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_815 = List []
                !appl_816 <- appl_815 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_815
                !appl_817 <- appl_816 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_816
                !appl_818 <- appl_817 `pseq` klCons (Types.Atom (Types.UnboundSym "exception")) appl_817
                let !appl_819 = List []
                !appl_820 <- appl_819 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_819
                !appl_821 <- appl_820 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_820
                !appl_822 <- appl_818 `pseq` (appl_821 `pseq` klCons appl_818 appl_821)
                let !appl_823 = List []
                !appl_824 <- appl_822 `pseq` (appl_823 `pseq` klCons appl_822 appl_823)
                !appl_825 <- appl_824 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_824
                !appl_826 <- appl_825 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_825
                appl_826 `pseq` kl_declare (Types.Atom (Types.UnboundSym "trap-error")) appl_826) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_827 = List []
                !appl_828 <- appl_827 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_827
                !appl_829 <- appl_828 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_828
                !appl_830 <- appl_829 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_829
                appl_830 `pseq` kl_declare (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_830) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_831 = List []
                !appl_832 <- appl_831 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_831
                !appl_833 <- appl_832 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_832
                !appl_834 <- appl_833 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_833
                appl_834 `pseq` kl_declare (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_834) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_835 = List []
                !appl_836 <- appl_835 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_835
                !appl_837 <- appl_836 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_836
                let !appl_838 = List []
                !appl_839 <- appl_838 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_838
                !appl_840 <- appl_839 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_839
                let !appl_841 = List []
                !appl_842 <- appl_841 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_841
                !appl_843 <- appl_842 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_842
                let !appl_844 = List []
                !appl_845 <- appl_843 `pseq` (appl_844 `pseq` klCons appl_843 appl_844)
                !appl_846 <- appl_845 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_845
                !appl_847 <- appl_840 `pseq` (appl_846 `pseq` klCons appl_840 appl_846)
                let !appl_848 = List []
                !appl_849 <- appl_847 `pseq` (appl_848 `pseq` klCons appl_847 appl_848)
                !appl_850 <- appl_849 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_849
                !appl_851 <- appl_837 `pseq` (appl_850 `pseq` klCons appl_837 appl_850)
                appl_851 `pseq` kl_declare (ApplC (wrapNamed "union" kl_union)) appl_851) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_852 = List []
                !appl_853 <- appl_852 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_852
                !appl_854 <- appl_853 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_853
                !appl_855 <- appl_854 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_854
                let !appl_856 = List []
                !appl_857 <- appl_856 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_856
                !appl_858 <- appl_857 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_857
                !appl_859 <- appl_858 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_858
                let !appl_860 = List []
                !appl_861 <- appl_859 `pseq` (appl_860 `pseq` klCons appl_859 appl_860)
                !appl_862 <- appl_861 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_861
                !appl_863 <- appl_855 `pseq` (appl_862 `pseq` klCons appl_855 appl_862)
                appl_863 `pseq` kl_declare (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_863) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_864 = List []
                !appl_865 <- appl_864 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_864
                !appl_866 <- appl_865 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_865
                !appl_867 <- appl_866 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_866
                appl_867 `pseq` kl_declare (ApplC (wrapNamed "untrack" kl_untrack)) appl_867) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_868 = List []
                !appl_869 <- appl_868 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_868
                !appl_870 <- appl_869 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_869
                !appl_871 <- appl_870 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_870
                appl_871 `pseq` kl_declare (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_871) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_872 = List []
                !appl_873 <- appl_872 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_872
                !appl_874 <- appl_873 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_873
                !appl_875 <- appl_874 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_874
                appl_875 `pseq` kl_declare (ApplC (wrapNamed "variable?" kl_variableP)) appl_875) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_876 = List []
                !appl_877 <- appl_876 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_876
                !appl_878 <- appl_877 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_877
                !appl_879 <- appl_878 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_878
                appl_879 `pseq` kl_declare (ApplC (wrapNamed "vector?" kl_vectorP)) appl_879) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_880 = List []
                !appl_881 <- appl_880 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_880
                !appl_882 <- appl_881 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_881
                appl_882 `pseq` kl_declare (ApplC (PL "version" kl_version)) appl_882) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_883 = List []
                !appl_884 <- appl_883 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_883
                !appl_885 <- appl_884 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_884
                !appl_886 <- appl_885 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_885
                let !appl_887 = List []
                !appl_888 <- appl_886 `pseq` (appl_887 `pseq` klCons appl_886 appl_887)
                !appl_889 <- appl_888 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_888
                !appl_890 <- appl_889 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_889
                appl_890 `pseq` kl_declare (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_890) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_891 = List []
                !appl_892 <- appl_891 `pseq` klCons (Types.Atom (Types.UnboundSym "out")) appl_891
                !appl_893 <- appl_892 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_892
                let !appl_894 = List []
                !appl_895 <- appl_894 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_894
                !appl_896 <- appl_895 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_895
                !appl_897 <- appl_893 `pseq` (appl_896 `pseq` klCons appl_893 appl_896)
                let !appl_898 = List []
                !appl_899 <- appl_897 `pseq` (appl_898 `pseq` klCons appl_897 appl_898)
                !appl_900 <- appl_899 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_899
                !appl_901 <- appl_900 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_900
                appl_901 `pseq` kl_declare (ApplC (wrapNamed "write-byte" writeByte)) appl_901) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_902 = List []
                !appl_903 <- appl_902 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_902
                !appl_904 <- appl_903 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_903
                !appl_905 <- appl_904 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_904
                appl_905 `pseq` kl_declare (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_905) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_906 = List []
                !appl_907 <- appl_906 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_906
                !appl_908 <- appl_907 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_907
                !appl_909 <- appl_908 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_908
                let !appl_910 = List []
                !appl_911 <- appl_909 `pseq` (appl_910 `pseq` klCons appl_909 appl_910)
                !appl_912 <- appl_911 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_911
                !appl_913 <- appl_912 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_912
                appl_913 `pseq` kl_declare (ApplC (wrapNamed ">" greaterThan)) appl_913) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_914 = List []
                !appl_915 <- appl_914 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_914
                !appl_916 <- appl_915 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_915
                !appl_917 <- appl_916 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_916
                let !appl_918 = List []
                !appl_919 <- appl_917 `pseq` (appl_918 `pseq` klCons appl_917 appl_918)
                !appl_920 <- appl_919 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_919
                !appl_921 <- appl_920 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_920
                appl_921 `pseq` kl_declare (ApplC (wrapNamed "<" lessThan)) appl_921) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_922 = List []
                !appl_923 <- appl_922 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_922
                !appl_924 <- appl_923 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_923
                !appl_925 <- appl_924 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_924
                let !appl_926 = List []
                !appl_927 <- appl_925 `pseq` (appl_926 `pseq` klCons appl_925 appl_926)
                !appl_928 <- appl_927 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_927
                !appl_929 <- appl_928 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_928
                appl_929 `pseq` kl_declare (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_929) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_930 = List []
                !appl_931 <- appl_930 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_930
                !appl_932 <- appl_931 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_931
                !appl_933 <- appl_932 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_932
                let !appl_934 = List []
                !appl_935 <- appl_933 `pseq` (appl_934 `pseq` klCons appl_933 appl_934)
                !appl_936 <- appl_935 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_935
                !appl_937 <- appl_936 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_936
                appl_937 `pseq` kl_declare (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_937) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_938 = List []
                !appl_939 <- appl_938 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_938
                !appl_940 <- appl_939 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_939
                !appl_941 <- appl_940 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_940
                let !appl_942 = List []
                !appl_943 <- appl_941 `pseq` (appl_942 `pseq` klCons appl_941 appl_942)
                !appl_944 <- appl_943 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_943
                !appl_945 <- appl_944 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_944
                appl_945 `pseq` kl_declare (ApplC (wrapNamed "=" eq)) appl_945) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_946 = List []
                !appl_947 <- appl_946 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_946
                !appl_948 <- appl_947 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_947
                !appl_949 <- appl_948 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_948
                let !appl_950 = List []
                !appl_951 <- appl_949 `pseq` (appl_950 `pseq` klCons appl_949 appl_950)
                !appl_952 <- appl_951 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_951
                !appl_953 <- appl_952 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_952
                appl_953 `pseq` kl_declare (ApplC (wrapNamed "+" add)) appl_953) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_954 = List []
                !appl_955 <- appl_954 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_954
                !appl_956 <- appl_955 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_955
                !appl_957 <- appl_956 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_956
                let !appl_958 = List []
                !appl_959 <- appl_957 `pseq` (appl_958 `pseq` klCons appl_957 appl_958)
                !appl_960 <- appl_959 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_959
                !appl_961 <- appl_960 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_960
                appl_961 `pseq` kl_declare (ApplC (wrapNamed "/" divide)) appl_961) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_962 = List []
                !appl_963 <- appl_962 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_962
                !appl_964 <- appl_963 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_963
                !appl_965 <- appl_964 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_964
                let !appl_966 = List []
                !appl_967 <- appl_965 `pseq` (appl_966 `pseq` klCons appl_965 appl_966)
                !appl_968 <- appl_967 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_967
                !appl_969 <- appl_968 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_968
                appl_969 `pseq` kl_declare (ApplC (wrapNamed "-" Primitives.subtract)) appl_969) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_970 = List []
                !appl_971 <- appl_970 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_970
                !appl_972 <- appl_971 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_971
                !appl_973 <- appl_972 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_972
                let !appl_974 = List []
                !appl_975 <- appl_973 `pseq` (appl_974 `pseq` klCons appl_973 appl_974)
                !appl_976 <- appl_975 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_975
                !appl_977 <- appl_976 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_976
                appl_977 `pseq` kl_declare (ApplC (wrapNamed "*" multiply)) appl_977) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_978 = List []
                !appl_979 <- appl_978 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_978
                !appl_980 <- appl_979 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_979
                !appl_981 <- appl_980 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_980
                let !appl_982 = List []
                !appl_983 <- appl_981 `pseq` (appl_982 `pseq` klCons appl_981 appl_982)
                !appl_984 <- appl_983 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_983
                !appl_985 <- appl_984 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_984
                appl_985 `pseq` kl_declare (ApplC (wrapNamed "==" kl_EqEq)) appl_985) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
