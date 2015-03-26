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

module Track where

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

kl_shen_f_error :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_f_error (!kl_V2327) = do let !aw_0 = Types.Atom (Types.UnboundSym "shen.app")
                                 !appl_1 <- kl_V2327 `pseq` applyWrapper aw_0 [kl_V2327,
                                                                               Types.Atom (Types.Str ";\n"),
                                                                               Types.Atom (Types.UnboundSym "shen.a")]
                                 !appl_2 <- appl_1 `pseq` cn (Types.Atom (Types.Str "partial function ")) appl_1
                                 !appl_3 <- kl_stoutput
                                 let !aw_4 = Types.Atom (Types.UnboundSym "shen.prhush")
                                 !appl_5 <- appl_2 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_2,
                                                                                            appl_3])
                                 !appl_6 <- kl_V2327 `pseq` kl_shen_trackedP kl_V2327
                                 !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                 !kl_if_8 <- klIf kl_if_7 (do let !aw_9 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_10 <- kl_V2327 `pseq` applyWrapper aw_9 [kl_V2327,
                                                                                                             Types.Atom (Types.Str "? "),
                                                                                                             Types.Atom (Types.UnboundSym "shen.a")]
                                                              !appl_11 <- appl_10 `pseq` cn (Types.Atom (Types.Str "track ")) appl_10
                                                              appl_11 `pseq` kl_y_or_nP appl_11) (do return (Atom (B False)))
                                 !appl_12 <- klIf kl_if_8 (do !appl_13 <- kl_V2327 `pseq` kl_ps kl_V2327
                                                              appl_13 `pseq` kl_shen_track_function appl_13) (do return (Types.Atom (Types.UnboundSym "shen.ok")))
                                 !appl_14 <- simpleError (Types.Atom (Types.Str "aborted"))
                                 !appl_15 <- appl_12 `pseq` (appl_14 `pseq` kl_do appl_12 appl_14)
                                 appl_5 `pseq` (appl_15 `pseq` kl_do appl_5 appl_15)

kl_shen_trackedP :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_trackedP (!kl_V2328) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*tracking*"))
                                  kl_V2328 `pseq` (appl_0 `pseq` kl_elementP kl_V2328 appl_0)

kl_track :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_track (!kl_V2329) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Source) -> do kl_Source `pseq` kl_shen_track_function kl_Source)))
                          !appl_1 <- kl_V2329 `pseq` kl_ps kl_V2329
                          appl_1 `pseq` applyWrapper appl_0 [appl_1]

kl_shen_track_function :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_track_function (!kl_V2330) = do !kl_if_0 <- kl_V2330 `pseq` consP kl_V2330
                                        !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2330 `pseq` hd kl_V2330
                                                                     !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "defun")) appl_2
                                                                     klIf kl_if_3 (do !appl_4 <- kl_V2330 `pseq` tl kl_V2330
                                                                                      !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                      klIf kl_if_5 (do !appl_6 <- kl_V2330 `pseq` tl kl_V2330
                                                                                                       !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                       !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                       klIf kl_if_8 (do !appl_9 <- kl_V2330 `pseq` tl kl_V2330
                                                                                                                        !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                        !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                        !kl_if_12 <- appl_11 `pseq` consP appl_11
                                                                                                                        klIf kl_if_12 (do let !appl_13 = List []
                                                                                                                                          !appl_14 <- kl_V2330 `pseq` tl kl_V2330
                                                                                                                                          !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                          !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                          !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                                                                          appl_13 `pseq` (appl_17 `pseq` eq appl_13 appl_17)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                        klIf kl_if_1 (do let !appl_18 = ApplC (Func "lambda" (Context (\(!kl_KL) -> do let !appl_19 = ApplC (Func "lambda" (Context (\(!kl_Ob) -> do let !appl_20 = ApplC (Func "lambda" (Context (\(!kl_Tr) -> do return kl_Ob)))
                                                                                                                                                                                     !appl_21 <- value (Types.Atom (Types.UnboundSym "shen.*tracking*"))
                                                                                                                                                                                     !appl_22 <- kl_Ob `pseq` (appl_21 `pseq` klCons kl_Ob appl_21)
                                                                                                                                                                                     !appl_23 <- appl_22 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*tracking*")) appl_22
                                                                                                                                                                                     appl_23 `pseq` applyWrapper appl_20 [appl_23])))
                                                                                                                       !appl_24 <- kl_KL `pseq` evalKL kl_KL
                                                                                                                       appl_24 `pseq` applyWrapper appl_19 [appl_24])))
                                                         !appl_25 <- kl_V2330 `pseq` tl kl_V2330
                                                         !appl_26 <- appl_25 `pseq` hd appl_25
                                                         !appl_27 <- kl_V2330 `pseq` tl kl_V2330
                                                         !appl_28 <- appl_27 `pseq` tl appl_27
                                                         !appl_29 <- appl_28 `pseq` hd appl_28
                                                         !appl_30 <- kl_V2330 `pseq` tl kl_V2330
                                                         !appl_31 <- appl_30 `pseq` hd appl_30
                                                         !appl_32 <- kl_V2330 `pseq` tl kl_V2330
                                                         !appl_33 <- appl_32 `pseq` tl appl_32
                                                         !appl_34 <- appl_33 `pseq` hd appl_33
                                                         !appl_35 <- kl_V2330 `pseq` tl kl_V2330
                                                         !appl_36 <- appl_35 `pseq` tl appl_35
                                                         !appl_37 <- appl_36 `pseq` tl appl_36
                                                         !appl_38 <- appl_37 `pseq` hd appl_37
                                                         !appl_39 <- appl_31 `pseq` (appl_34 `pseq` (appl_38 `pseq` kl_shen_insert_tracking_code appl_31 appl_34 appl_38))
                                                         let !appl_40 = List []
                                                         !appl_41 <- appl_39 `pseq` (appl_40 `pseq` klCons appl_39 appl_40)
                                                         !appl_42 <- appl_29 `pseq` (appl_41 `pseq` klCons appl_29 appl_41)
                                                         !appl_43 <- appl_26 `pseq` (appl_42 `pseq` klCons appl_26 appl_42)
                                                         !appl_44 <- appl_43 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_43
                                                         appl_44 `pseq` applyWrapper appl_18 [appl_44]) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.track-function" kl_shen_track_function))) (do return (List [])))

kl_shen_insert_tracking_code :: Types.KLValue ->
                                Types.KLValue ->
                                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert_tracking_code (!kl_V2331) (!kl_V2332) (!kl_V2333) = do let !appl_0 = List []
                                                                      !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_0
                                                                      !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_1
                                                                      let !appl_3 = List []
                                                                      !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_3
                                                                      !appl_5 <- appl_2 `pseq` (appl_4 `pseq` klCons appl_2 appl_4)
                                                                      !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_5
                                                                      let !appl_7 = List []
                                                                      !appl_8 <- appl_6 `pseq` (appl_7 `pseq` klCons appl_6 appl_7)
                                                                      !appl_9 <- appl_8 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_8
                                                                      !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_9
                                                                      let !appl_11 = List []
                                                                      !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_11
                                                                      !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_12
                                                                      !appl_14 <- kl_V2332 `pseq` kl_shen_cons_form kl_V2332
                                                                      let !appl_15 = List []
                                                                      !appl_16 <- appl_14 `pseq` (appl_15 `pseq` klCons appl_14 appl_15)
                                                                      !appl_17 <- kl_V2331 `pseq` (appl_16 `pseq` klCons kl_V2331 appl_16)
                                                                      !appl_18 <- appl_13 `pseq` (appl_17 `pseq` klCons appl_13 appl_17)
                                                                      !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.input-track" kl_shen_input_track)) appl_18
                                                                      let !appl_20 = List []
                                                                      !appl_21 <- appl_20 `pseq` klCons (ApplC (PL "shen.terpri-or-read-char" kl_shen_terpri_or_read_char)) appl_20
                                                                      let !appl_22 = List []
                                                                      !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_22
                                                                      !appl_24 <- appl_23 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_23
                                                                      let !appl_25 = List []
                                                                      !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_25
                                                                      !appl_27 <- kl_V2331 `pseq` (appl_26 `pseq` klCons kl_V2331 appl_26)
                                                                      !appl_28 <- appl_24 `pseq` (appl_27 `pseq` klCons appl_24 appl_27)
                                                                      !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "shen.output-track" kl_shen_output_track)) appl_28
                                                                      let !appl_30 = List []
                                                                      !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_30
                                                                      !appl_32 <- appl_31 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_31
                                                                      let !appl_33 = List []
                                                                      !appl_34 <- appl_33 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_33
                                                                      !appl_35 <- appl_32 `pseq` (appl_34 `pseq` klCons appl_32 appl_34)
                                                                      !appl_36 <- appl_35 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_35
                                                                      let !appl_37 = List []
                                                                      !appl_38 <- appl_36 `pseq` (appl_37 `pseq` klCons appl_36 appl_37)
                                                                      !appl_39 <- appl_38 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_38
                                                                      !appl_40 <- appl_39 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_39
                                                                      let !appl_41 = List []
                                                                      !appl_42 <- appl_41 `pseq` klCons (ApplC (PL "shen.terpri-or-read-char" kl_shen_terpri_or_read_char)) appl_41
                                                                      let !appl_43 = List []
                                                                      !appl_44 <- appl_43 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_43
                                                                      !appl_45 <- appl_42 `pseq` (appl_44 `pseq` klCons appl_42 appl_44)
                                                                      !appl_46 <- appl_45 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_45
                                                                      let !appl_47 = List []
                                                                      !appl_48 <- appl_46 `pseq` (appl_47 `pseq` klCons appl_46 appl_47)
                                                                      !appl_49 <- appl_40 `pseq` (appl_48 `pseq` klCons appl_40 appl_48)
                                                                      !appl_50 <- appl_49 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_49
                                                                      let !appl_51 = List []
                                                                      !appl_52 <- appl_50 `pseq` (appl_51 `pseq` klCons appl_50 appl_51)
                                                                      !appl_53 <- appl_29 `pseq` (appl_52 `pseq` klCons appl_29 appl_52)
                                                                      !appl_54 <- appl_53 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_53
                                                                      let !appl_55 = List []
                                                                      !appl_56 <- appl_54 `pseq` (appl_55 `pseq` klCons appl_54 appl_55)
                                                                      !appl_57 <- kl_V2333 `pseq` (appl_56 `pseq` klCons kl_V2333 appl_56)
                                                                      !appl_58 <- appl_57 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_57
                                                                      !appl_59 <- appl_58 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_58
                                                                      let !appl_60 = List []
                                                                      !appl_61 <- appl_59 `pseq` (appl_60 `pseq` klCons appl_59 appl_60)
                                                                      !appl_62 <- appl_21 `pseq` (appl_61 `pseq` klCons appl_21 appl_61)
                                                                      !appl_63 <- appl_62 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_62
                                                                      let !appl_64 = List []
                                                                      !appl_65 <- appl_63 `pseq` (appl_64 `pseq` klCons appl_63 appl_64)
                                                                      !appl_66 <- appl_19 `pseq` (appl_65 `pseq` klCons appl_19 appl_65)
                                                                      !appl_67 <- appl_66 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_66
                                                                      let !appl_68 = List []
                                                                      !appl_69 <- appl_67 `pseq` (appl_68 `pseq` klCons appl_67 appl_68)
                                                                      !appl_70 <- appl_10 `pseq` (appl_69 `pseq` klCons appl_10 appl_69)
                                                                      appl_70 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_70

kl_step :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_step (!kl_V2338) = do !kl_if_0 <- kl_V2338 `pseq` eq (ApplC (wrapNamed "+" add)) kl_V2338
                         klIf kl_if_0 (do klSet (Types.Atom (Types.UnboundSym "shen.*step*")) (Atom (B True))) (do !kl_if_1 <- kl_V2338 `pseq` eq (ApplC (wrapNamed "-" Primitives.subtract)) kl_V2338
                                                                                                                   klIf kl_if_1 (do klSet (Types.Atom (Types.UnboundSym "shen.*step*")) (Atom (B False))) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "step expects a + or a -.\n"))) (do return (List []))))

kl_spy :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_spy (!kl_V2343) = do !kl_if_0 <- kl_V2343 `pseq` eq (ApplC (wrapNamed "+" add)) kl_V2343
                        klIf kl_if_0 (do klSet (Types.Atom (Types.UnboundSym "shen.*spy*")) (Atom (B True))) (do !kl_if_1 <- kl_V2343 `pseq` eq (ApplC (wrapNamed "-" Primitives.subtract)) kl_V2343
                                                                                                                 klIf kl_if_1 (do klSet (Types.Atom (Types.UnboundSym "shen.*spy*")) (Atom (B False))) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "spy expects a + or a -.\n"))) (do return (List []))))

kl_shen_terpri_or_read_char :: Types.KLContext Types.Env
                                               Types.KLValue
kl_shen_terpri_or_read_char = do !kl_if_0 <- value (Types.Atom (Types.UnboundSym "shen.*step*"))
                                 klIf kl_if_0 (do !appl_1 <- value (Types.Atom (Types.UnboundSym "*stinput*"))
                                                  !appl_2 <- appl_1 `pseq` readByte appl_1
                                                  appl_2 `pseq` kl_shen_check_byte appl_2) (do kl_nl (Types.Atom (Types.N (Types.KI 1))))

kl_shen_check_byte :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_check_byte (!kl_V2348) = do !appl_0 <- kl_shen_hat
                                    !kl_if_1 <- kl_V2348 `pseq` (appl_0 `pseq` eq kl_V2348 appl_0)
                                    klIf kl_if_1 (do simpleError (Types.Atom (Types.Str "aborted"))) (do klIf (Atom (B True)) (do return (Atom (B True))) (do return (List [])))

kl_shen_input_track :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_input_track (!kl_V2349) (!kl_V2350) (!kl_V2351) = do !appl_0 <- kl_V2349 `pseq` kl_shen_spaces kl_V2349
                                                             !appl_1 <- kl_V2349 `pseq` kl_shen_spaces kl_V2349
                                                             let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [appl_1,
                                                                                                         Types.Atom (Types.Str ""),
                                                                                                         Types.Atom (Types.UnboundSym "shen.a")]
                                                             !appl_4 <- appl_3 `pseq` cn (Types.Atom (Types.Str " \n")) appl_3
                                                             let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_6 <- kl_V2350 `pseq` (appl_4 `pseq` applyWrapper aw_5 [kl_V2350,
                                                                                                                          appl_4,
                                                                                                                          Types.Atom (Types.UnboundSym "shen.a")])
                                                             !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str "> Inputs to ")) appl_6
                                                             let !aw_8 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_9 <- kl_V2349 `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_V2349,
                                                                                                                          appl_7,
                                                                                                                          Types.Atom (Types.UnboundSym "shen.a")])
                                                             !appl_10 <- appl_9 `pseq` cn (Types.Atom (Types.Str "<")) appl_9
                                                             let !aw_11 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_12 <- appl_0 `pseq` (appl_10 `pseq` applyWrapper aw_11 [appl_0,
                                                                                                                           appl_10,
                                                                                                                           Types.Atom (Types.UnboundSym "shen.a")])
                                                             !appl_13 <- appl_12 `pseq` cn (Types.Atom (Types.Str "\n")) appl_12
                                                             !appl_14 <- kl_stoutput
                                                             let !aw_15 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                             !appl_16 <- appl_13 `pseq` (appl_14 `pseq` applyWrapper aw_15 [appl_13,
                                                                                                                            appl_14])
                                                             !appl_17 <- kl_V2351 `pseq` kl_shen_recursively_print kl_V2351
                                                             appl_16 `pseq` (appl_17 `pseq` kl_do appl_16 appl_17)

kl_shen_recursively_print :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_recursively_print (!kl_V2352) = do let !appl_0 = List []
                                           !kl_if_1 <- appl_0 `pseq` (kl_V2352 `pseq` eq appl_0 kl_V2352)
                                           klIf kl_if_1 (do !appl_2 <- kl_stoutput
                                                            let !aw_3 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                            appl_2 `pseq` applyWrapper aw_3 [Types.Atom (Types.Str " ==>"),
                                                                                             appl_2]) (do !kl_if_4 <- kl_V2352 `pseq` consP kl_V2352
                                                                                                          klIf kl_if_4 (do !appl_5 <- kl_V2352 `pseq` hd kl_V2352
                                                                                                                           let !aw_6 = Types.Atom (Types.UnboundSym "print")
                                                                                                                           !appl_7 <- appl_5 `pseq` applyWrapper aw_6 [appl_5]
                                                                                                                           !appl_8 <- kl_stoutput
                                                                                                                           let !aw_9 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                           !appl_10 <- appl_8 `pseq` applyWrapper aw_9 [Types.Atom (Types.Str ", "),
                                                                                                                                                                        appl_8]
                                                                                                                           !appl_11 <- kl_V2352 `pseq` tl kl_V2352
                                                                                                                           !appl_12 <- appl_11 `pseq` kl_shen_recursively_print appl_11
                                                                                                                           !appl_13 <- appl_10 `pseq` (appl_12 `pseq` kl_do appl_10 appl_12)
                                                                                                                           appl_7 `pseq` (appl_13 `pseq` kl_do appl_7 appl_13)) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.recursively-print" kl_shen_recursively_print))) (do return (List []))))

kl_shen_spaces :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_spaces (!kl_V2353) = do !kl_if_0 <- kl_V2353 `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_V2353
                                klIf kl_if_0 (do return (Types.Atom (Types.Str ""))) (do klIf (Atom (B True)) (do !appl_1 <- kl_V2353 `pseq` Primitives.subtract kl_V2353 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                  !appl_2 <- appl_1 `pseq` kl_shen_spaces appl_1
                                                                                                                  appl_2 `pseq` cn (Types.Atom (Types.Str " ")) appl_2) (do return (List [])))

kl_shen_output_track :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_output_track (!kl_V2354) (!kl_V2355) (!kl_V2356) = do !appl_0 <- kl_V2354 `pseq` kl_shen_spaces kl_V2354
                                                              !appl_1 <- kl_V2354 `pseq` kl_shen_spaces kl_V2354
                                                              let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_3 <- kl_V2356 `pseq` applyWrapper aw_2 [kl_V2356,
                                                                                                            Types.Atom (Types.Str ""),
                                                                                                            Types.Atom (Types.UnboundSym "shen.s")]
                                                              !appl_4 <- appl_3 `pseq` cn (Types.Atom (Types.Str "==> ")) appl_3
                                                              let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_6 <- appl_1 `pseq` (appl_4 `pseq` applyWrapper aw_5 [appl_1,
                                                                                                                         appl_4,
                                                                                                                         Types.Atom (Types.UnboundSym "shen.a")])
                                                              !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str " \n")) appl_6
                                                              let !aw_8 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_9 <- kl_V2355 `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_V2355,
                                                                                                                           appl_7,
                                                                                                                           Types.Atom (Types.UnboundSym "shen.a")])
                                                              !appl_10 <- appl_9 `pseq` cn (Types.Atom (Types.Str "> Output from ")) appl_9
                                                              let !aw_11 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_12 <- kl_V2354 `pseq` (appl_10 `pseq` applyWrapper aw_11 [kl_V2354,
                                                                                                                              appl_10,
                                                                                                                              Types.Atom (Types.UnboundSym "shen.a")])
                                                              !appl_13 <- appl_12 `pseq` cn (Types.Atom (Types.Str "<")) appl_12
                                                              let !aw_14 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_15 <- appl_0 `pseq` (appl_13 `pseq` applyWrapper aw_14 [appl_0,
                                                                                                                            appl_13,
                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")])
                                                              !appl_16 <- appl_15 `pseq` cn (Types.Atom (Types.Str "\n")) appl_15
                                                              !appl_17 <- kl_stoutput
                                                              let !aw_18 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                              appl_16 `pseq` (appl_17 `pseq` applyWrapper aw_18 [appl_16,
                                                                                                                 appl_17])

kl_untrack :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_untrack (!kl_V2357) = do !appl_0 <- kl_V2357 `pseq` kl_ps kl_V2357
                            appl_0 `pseq` kl_eval appl_0

kl_profile :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_profile (!kl_V2358) = do !appl_0 <- kl_V2358 `pseq` kl_ps kl_V2358
                            appl_0 `pseq` kl_shen_profile_help appl_0

kl_shen_profile_help :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_profile_help (!kl_V2363) = do !kl_if_0 <- kl_V2363 `pseq` consP kl_V2363
                                      !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V2363 `pseq` hd kl_V2363
                                                                   !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "defun")) appl_2
                                                                   klIf kl_if_3 (do !appl_4 <- kl_V2363 `pseq` tl kl_V2363
                                                                                    !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                    klIf kl_if_5 (do !appl_6 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                     !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                     !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                     klIf kl_if_8 (do !appl_9 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                      !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                      !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                      !kl_if_12 <- appl_11 `pseq` consP appl_11
                                                                                                                      klIf kl_if_12 (do let !appl_13 = List []
                                                                                                                                        !appl_14 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                                        !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                        !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                        !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                                                                        appl_13 `pseq` (appl_17 `pseq` eq appl_13 appl_17)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                      klIf kl_if_1 (do let !appl_18 = ApplC (Func "lambda" (Context (\(!kl_G) -> do let !appl_19 = ApplC (Func "lambda" (Context (\(!kl_Profile) -> do let !appl_20 = ApplC (Func "lambda" (Context (\(!kl_Def) -> do let !appl_21 = ApplC (Func "lambda" (Context (\(!kl_CompileProfile) -> do let !appl_22 = ApplC (Func "lambda" (Context (\(!kl_CompileG) -> do !appl_23 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                                                                                                                                                                                                                                                                                                    appl_23 `pseq` hd appl_23)))
                                                                                                                                                                                                                                                                                                                                !appl_24 <- kl_Def `pseq` kl_shen_eval_without_macros kl_Def
                                                                                                                                                                                                                                                                                                                                appl_24 `pseq` applyWrapper appl_22 [appl_24])))
                                                                                                                                                                                                                                                      !appl_25 <- kl_Profile `pseq` kl_shen_eval_without_macros kl_Profile
                                                                                                                                                                                                                                                      appl_25 `pseq` applyWrapper appl_21 [appl_25])))
                                                                                                                                                                                       !appl_26 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                                                                                       !appl_27 <- appl_26 `pseq` tl appl_26
                                                                                                                                                                                       !appl_28 <- appl_27 `pseq` hd appl_27
                                                                                                                                                                                       !appl_29 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                                                                                       !appl_30 <- appl_29 `pseq` hd appl_29
                                                                                                                                                                                       !appl_31 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                                                                                       !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                       !appl_33 <- appl_32 `pseq` tl appl_32
                                                                                                                                                                                       !appl_34 <- appl_33 `pseq` hd appl_33
                                                                                                                                                                                       !appl_35 <- kl_G `pseq` (appl_30 `pseq` (appl_34 `pseq` kl_subst kl_G appl_30 appl_34))
                                                                                                                                                                                       let !appl_36 = List []
                                                                                                                                                                                       !appl_37 <- appl_35 `pseq` (appl_36 `pseq` klCons appl_35 appl_36)
                                                                                                                                                                                       !appl_38 <- appl_28 `pseq` (appl_37 `pseq` klCons appl_28 appl_37)
                                                                                                                                                                                       !appl_39 <- kl_G `pseq` (appl_38 `pseq` klCons kl_G appl_38)
                                                                                                                                                                                       !appl_40 <- appl_39 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_39
                                                                                                                                                                                       appl_40 `pseq` applyWrapper appl_20 [appl_40])))
                                                                                                                    !appl_41 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                    !appl_42 <- appl_41 `pseq` hd appl_41
                                                                                                                    !appl_43 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                    !appl_44 <- appl_43 `pseq` tl appl_43
                                                                                                                    !appl_45 <- appl_44 `pseq` hd appl_44
                                                                                                                    !appl_46 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                    !appl_47 <- appl_46 `pseq` hd appl_46
                                                                                                                    !appl_48 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                    !appl_49 <- appl_48 `pseq` tl appl_48
                                                                                                                    !appl_50 <- appl_49 `pseq` hd appl_49
                                                                                                                    !appl_51 <- kl_V2363 `pseq` tl kl_V2363
                                                                                                                    !appl_52 <- appl_51 `pseq` tl appl_51
                                                                                                                    !appl_53 <- appl_52 `pseq` hd appl_52
                                                                                                                    !appl_54 <- kl_G `pseq` (appl_53 `pseq` klCons kl_G appl_53)
                                                                                                                    !appl_55 <- appl_47 `pseq` (appl_50 `pseq` (appl_54 `pseq` kl_shen_profile_func appl_47 appl_50 appl_54))
                                                                                                                    let !appl_56 = List []
                                                                                                                    !appl_57 <- appl_55 `pseq` (appl_56 `pseq` klCons appl_55 appl_56)
                                                                                                                    !appl_58 <- appl_45 `pseq` (appl_57 `pseq` klCons appl_45 appl_57)
                                                                                                                    !appl_59 <- appl_42 `pseq` (appl_58 `pseq` klCons appl_42 appl_58)
                                                                                                                    !appl_60 <- appl_59 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_59
                                                                                                                    appl_60 `pseq` applyWrapper appl_19 [appl_60])))
                                                       !appl_61 <- kl_gensym (Types.Atom (Types.UnboundSym "shen.f"))
                                                       appl_61 `pseq` applyWrapper appl_18 [appl_61]) (do klIf (Atom (B True)) (do simpleError (Types.Atom (Types.Str "Cannot profile.\n"))) (do return (List [])))

kl_unprofile :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_unprofile (!kl_V2364) = do kl_V2364 `pseq` kl_untrack kl_V2364

kl_shen_profile_func :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_profile_func (!kl_V2365) (!kl_V2366) (!kl_V2367) = do let !appl_0 = List []
                                                              !appl_1 <- appl_0 `pseq` klCons (Types.Atom (Types.UnboundSym "run")) appl_0
                                                              !appl_2 <- appl_1 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_1
                                                              let !appl_3 = List []
                                                              !appl_4 <- appl_3 `pseq` klCons (Types.Atom (Types.UnboundSym "run")) appl_3
                                                              !appl_5 <- appl_4 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_4
                                                              let !appl_6 = List []
                                                              !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "Start")) appl_6
                                                              !appl_8 <- appl_5 `pseq` (appl_7 `pseq` klCons appl_5 appl_7)
                                                              !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_8
                                                              let !appl_10 = List []
                                                              !appl_11 <- kl_V2365 `pseq` (appl_10 `pseq` klCons kl_V2365 appl_10)
                                                              !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "shen.get-profile" kl_shen_get_profile)) appl_11
                                                              let !appl_13 = List []
                                                              !appl_14 <- appl_13 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_13
                                                              !appl_15 <- appl_12 `pseq` (appl_14 `pseq` klCons appl_12 appl_14)
                                                              !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_15
                                                              let !appl_17 = List []
                                                              !appl_18 <- appl_16 `pseq` (appl_17 `pseq` klCons appl_16 appl_17)
                                                              !appl_19 <- kl_V2365 `pseq` (appl_18 `pseq` klCons kl_V2365 appl_18)
                                                              !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "shen.put-profile" kl_shen_put_profile)) appl_19
                                                              let !appl_21 = List []
                                                              !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_21
                                                              !appl_23 <- appl_20 `pseq` (appl_22 `pseq` klCons appl_20 appl_22)
                                                              !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "Record")) appl_23
                                                              !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_24
                                                              let !appl_26 = List []
                                                              !appl_27 <- appl_25 `pseq` (appl_26 `pseq` klCons appl_25 appl_26)
                                                              !appl_28 <- appl_9 `pseq` (appl_27 `pseq` klCons appl_9 appl_27)
                                                              !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_28
                                                              !appl_30 <- appl_29 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_29
                                                              let !appl_31 = List []
                                                              !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                              !appl_33 <- kl_V2367 `pseq` (appl_32 `pseq` klCons kl_V2367 appl_32)
                                                              !appl_34 <- appl_33 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_33
                                                              !appl_35 <- appl_34 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_34
                                                              let !appl_36 = List []
                                                              !appl_37 <- appl_35 `pseq` (appl_36 `pseq` klCons appl_35 appl_36)
                                                              !appl_38 <- appl_2 `pseq` (appl_37 `pseq` klCons appl_2 appl_37)
                                                              !appl_39 <- appl_38 `pseq` klCons (Types.Atom (Types.UnboundSym "Start")) appl_38
                                                              appl_39 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_39

kl_profile_results :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_profile_results (!kl_V2368) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Results) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Initialise) -> do kl_V2368 `pseq` (kl_Results `pseq` kl_Atp kl_V2368 kl_Results))))
                                                                                                      !appl_2 <- kl_V2368 `pseq` kl_shen_put_profile kl_V2368 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                      appl_2 `pseq` applyWrapper appl_1 [appl_2])))
                                    !appl_3 <- kl_V2368 `pseq` kl_shen_get_profile kl_V2368
                                    appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_get_profile :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_get_profile (!kl_V2369) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                         kl_V2369 `pseq` (appl_0 `pseq` kl_get kl_V2369 (ApplC (wrapNamed "profile" kl_profile)) appl_0)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.N (Types.KI 0))))

kl_shen_put_profile :: Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_put_profile (!kl_V2370) (!kl_V2371) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                                 kl_V2370 `pseq` (kl_V2371 `pseq` (appl_0 `pseq` kl_put kl_V2370 (ApplC (wrapNamed "profile" kl_profile)) kl_V2371 appl_0))

expr7 :: Types.KLContext Types.Env Types.KLValue
expr7 = do (do klSet (Types.Atom (Types.UnboundSym "shen.*step*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
