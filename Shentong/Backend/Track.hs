{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Track where

import Control.Monad.Except
import Control.Parallel
import Environment
import Primitives as Primitives
import Backend.Utils
import Types as Types
import Utils
import Wrap
import Backend.Toplevel
import Backend.Core
import Backend.Sys
import Backend.Sequent
import Backend.Yacc
import Backend.Reader
import Backend.Prolog

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

kl_shen_f_error :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_f_error (!kl_V3779) = do let !aw_0 = Types.Atom (Types.UnboundSym "shen.app")
                                 !appl_1 <- kl_V3779 `pseq` applyWrapper aw_0 [kl_V3779,
                                                                               Types.Atom (Types.Str ";\n"),
                                                                               Types.Atom (Types.UnboundSym "shen.a")]
                                 !appl_2 <- appl_1 `pseq` cn (Types.Atom (Types.Str "partial function ")) appl_1
                                 !appl_3 <- kl_stoutput
                                 let !aw_4 = Types.Atom (Types.UnboundSym "shen.prhush")
                                 !appl_5 <- appl_2 `pseq` (appl_3 `pseq` applyWrapper aw_4 [appl_2,
                                                                                            appl_3])
                                 !appl_6 <- kl_V3779 `pseq` kl_shen_trackedP kl_V3779
                                 !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                 !kl_if_8 <- case kl_if_7 of
                                                 Atom (B (True)) -> do let !aw_9 = Types.Atom (Types.UnboundSym "shen.app")
                                                                       !appl_10 <- kl_V3779 `pseq` applyWrapper aw_9 [kl_V3779,
                                                                                                                      Types.Atom (Types.Str "? "),
                                                                                                                      Types.Atom (Types.UnboundSym "shen.a")]
                                                                       !appl_11 <- appl_10 `pseq` cn (Types.Atom (Types.Str "track ")) appl_10
                                                                       !kl_if_12 <- appl_11 `pseq` kl_y_or_nP appl_11
                                                                       case kl_if_12 of
                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                           _ -> throwError "if: expected boolean"
                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                 _ -> throwError "if: expected boolean"
                                 !appl_13 <- case kl_if_8 of
                                                 Atom (B (True)) -> do !appl_14 <- kl_V3779 `pseq` kl_ps kl_V3779
                                                                       appl_14 `pseq` kl_shen_track_function appl_14
                                                 Atom (B (False)) -> do do return (Types.Atom (Types.UnboundSym "shen.ok"))
                                                 _ -> throwError "if: expected boolean"
                                 !appl_15 <- simpleError (Types.Atom (Types.Str "aborted"))
                                 !appl_16 <- appl_13 `pseq` (appl_15 `pseq` kl_do appl_13 appl_15)
                                 appl_5 `pseq` (appl_16 `pseq` kl_do appl_5 appl_16)

kl_shen_trackedP :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_trackedP (!kl_V3781) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*tracking*"))
                                  kl_V3781 `pseq` (appl_0 `pseq` kl_elementP kl_V3781 appl_0)

kl_track :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_track (!kl_V3783) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Source) -> do kl_Source `pseq` kl_shen_track_function kl_Source)))
                          !appl_1 <- kl_V3783 `pseq` kl_ps kl_V3783
                          appl_1 `pseq` applyWrapper appl_0 [appl_1]

kl_shen_track_function :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_track_function (!kl_V3785) = do let pat_cond_0 kl_V3785 kl_V3785t kl_V3785th kl_V3785tt kl_V3785tth kl_V3785ttt kl_V3785ttth = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_KL) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Ob) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Tr) -> do return kl_Ob)))
                                                                                                                                                                                                                                                                    !appl_4 <- value (Types.Atom (Types.UnboundSym "shen.*tracking*"))
                                                                                                                                                                                                                                                                    !appl_5 <- kl_Ob `pseq` (appl_4 `pseq` klCons kl_Ob appl_4)
                                                                                                                                                                                                                                                                    !appl_6 <- appl_5 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*tracking*")) appl_5
                                                                                                                                                                                                                                                                    appl_6 `pseq` applyWrapper appl_3 [appl_6])))
                                                                                                                                                                                                       !appl_7 <- kl_KL `pseq` evalKL kl_KL
                                                                                                                                                                                                       appl_7 `pseq` applyWrapper appl_2 [appl_7])))
                                                                                                                                          !appl_8 <- kl_V3785th `pseq` (kl_V3785tth `pseq` (kl_V3785ttth `pseq` kl_shen_insert_tracking_code kl_V3785th kl_V3785tth kl_V3785ttth))
                                                                                                                                          !appl_9 <- appl_8 `pseq` klCons appl_8 (Types.Atom Types.Nil)
                                                                                                                                          !appl_10 <- kl_V3785tth `pseq` (appl_9 `pseq` klCons kl_V3785tth appl_9)
                                                                                                                                          !appl_11 <- kl_V3785th `pseq` (appl_10 `pseq` klCons kl_V3785th appl_10)
                                                                                                                                          !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_11
                                                                                                                                          appl_12 `pseq` applyWrapper appl_1 [appl_12]
                                            pat_cond_13 = do do kl_shen_f_error (ApplC (wrapNamed "shen.track-function" kl_shen_track_function))
                                         in case kl_V3785 of
                                                !(kl_V3785@(Cons (Atom (UnboundSym "defun"))
                                                                 (!(kl_V3785t@(Cons (!kl_V3785th)
                                                                                    (!(kl_V3785tt@(Cons (!kl_V3785tth)
                                                                                                        (!(kl_V3785ttt@(Cons (!kl_V3785ttth)
                                                                                                                             (Atom (Nil))))))))))))) -> pat_cond_0 kl_V3785 kl_V3785t kl_V3785th kl_V3785tt kl_V3785tth kl_V3785ttt kl_V3785ttth
                                                !(kl_V3785@(Cons (ApplC (PL "defun" _))
                                                                 (!(kl_V3785t@(Cons (!kl_V3785th)
                                                                                    (!(kl_V3785tt@(Cons (!kl_V3785tth)
                                                                                                        (!(kl_V3785ttt@(Cons (!kl_V3785ttth)
                                                                                                                             (Atom (Nil))))))))))))) -> pat_cond_0 kl_V3785 kl_V3785t kl_V3785th kl_V3785tt kl_V3785tth kl_V3785ttt kl_V3785ttth
                                                !(kl_V3785@(Cons (ApplC (Func "defun" _))
                                                                 (!(kl_V3785t@(Cons (!kl_V3785th)
                                                                                    (!(kl_V3785tt@(Cons (!kl_V3785tth)
                                                                                                        (!(kl_V3785ttt@(Cons (!kl_V3785ttth)
                                                                                                                             (Atom (Nil))))))))))))) -> pat_cond_0 kl_V3785 kl_V3785t kl_V3785th kl_V3785tt kl_V3785tth kl_V3785ttt kl_V3785ttth
                                                _ -> pat_cond_13

kl_shen_insert_tracking_code :: Types.KLValue ->
                                Types.KLValue ->
                                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert_tracking_code (!kl_V3789) (!kl_V3790) (!kl_V3791) = do !appl_0 <- klCons (Types.Atom (Types.UnboundSym "shen.*call*")) (Types.Atom Types.Nil)
                                                                      !appl_1 <- appl_0 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_0
                                                                      !appl_2 <- klCons (Types.Atom (Types.N (Types.KI 1))) (Types.Atom Types.Nil)
                                                                      !appl_3 <- appl_1 `pseq` (appl_2 `pseq` klCons appl_1 appl_2)
                                                                      !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_3
                                                                      !appl_5 <- appl_4 `pseq` klCons appl_4 (Types.Atom Types.Nil)
                                                                      !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_5
                                                                      !appl_7 <- appl_6 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_6
                                                                      !appl_8 <- klCons (Types.Atom (Types.UnboundSym "shen.*call*")) (Types.Atom Types.Nil)
                                                                      !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_8
                                                                      !appl_10 <- kl_V3790 `pseq` kl_shen_cons_form kl_V3790
                                                                      !appl_11 <- appl_10 `pseq` klCons appl_10 (Types.Atom Types.Nil)
                                                                      !appl_12 <- kl_V3789 `pseq` (appl_11 `pseq` klCons kl_V3789 appl_11)
                                                                      !appl_13 <- appl_9 `pseq` (appl_12 `pseq` klCons appl_9 appl_12)
                                                                      !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "shen.input-track" kl_shen_input_track)) appl_13
                                                                      !appl_15 <- klCons (ApplC (PL "shen.terpri-or-read-char" kl_shen_terpri_or_read_char)) (Types.Atom Types.Nil)
                                                                      !appl_16 <- klCons (Types.Atom (Types.UnboundSym "shen.*call*")) (Types.Atom Types.Nil)
                                                                      !appl_17 <- appl_16 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_16
                                                                      !appl_18 <- klCons (Types.Atom (Types.UnboundSym "Result")) (Types.Atom Types.Nil)
                                                                      !appl_19 <- kl_V3789 `pseq` (appl_18 `pseq` klCons kl_V3789 appl_18)
                                                                      !appl_20 <- appl_17 `pseq` (appl_19 `pseq` klCons appl_17 appl_19)
                                                                      !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "shen.output-track" kl_shen_output_track)) appl_20
                                                                      !appl_22 <- klCons (Types.Atom (Types.UnboundSym "shen.*call*")) (Types.Atom Types.Nil)
                                                                      !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_22
                                                                      !appl_24 <- klCons (Types.Atom (Types.N (Types.KI 1))) (Types.Atom Types.Nil)
                                                                      !appl_25 <- appl_23 `pseq` (appl_24 `pseq` klCons appl_23 appl_24)
                                                                      !appl_26 <- appl_25 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_25
                                                                      !appl_27 <- appl_26 `pseq` klCons appl_26 (Types.Atom Types.Nil)
                                                                      !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.*call*")) appl_27
                                                                      !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_28
                                                                      !appl_30 <- klCons (ApplC (PL "shen.terpri-or-read-char" kl_shen_terpri_or_read_char)) (Types.Atom Types.Nil)
                                                                      !appl_31 <- klCons (Types.Atom (Types.UnboundSym "Result")) (Types.Atom Types.Nil)
                                                                      !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                      !appl_33 <- appl_32 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_32
                                                                      !appl_34 <- appl_33 `pseq` klCons appl_33 (Types.Atom Types.Nil)
                                                                      !appl_35 <- appl_29 `pseq` (appl_34 `pseq` klCons appl_29 appl_34)
                                                                      !appl_36 <- appl_35 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_35
                                                                      !appl_37 <- appl_36 `pseq` klCons appl_36 (Types.Atom Types.Nil)
                                                                      !appl_38 <- appl_21 `pseq` (appl_37 `pseq` klCons appl_21 appl_37)
                                                                      !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_38
                                                                      !appl_40 <- appl_39 `pseq` klCons appl_39 (Types.Atom Types.Nil)
                                                                      !appl_41 <- kl_V3791 `pseq` (appl_40 `pseq` klCons kl_V3791 appl_40)
                                                                      !appl_42 <- appl_41 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_41
                                                                      !appl_43 <- appl_42 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_42
                                                                      !appl_44 <- appl_43 `pseq` klCons appl_43 (Types.Atom Types.Nil)
                                                                      !appl_45 <- appl_15 `pseq` (appl_44 `pseq` klCons appl_15 appl_44)
                                                                      !appl_46 <- appl_45 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_45
                                                                      !appl_47 <- appl_46 `pseq` klCons appl_46 (Types.Atom Types.Nil)
                                                                      !appl_48 <- appl_14 `pseq` (appl_47 `pseq` klCons appl_14 appl_47)
                                                                      !appl_49 <- appl_48 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_48
                                                                      !appl_50 <- appl_49 `pseq` klCons appl_49 (Types.Atom Types.Nil)
                                                                      !appl_51 <- appl_7 `pseq` (appl_50 `pseq` klCons appl_7 appl_50)
                                                                      appl_51 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_51

kl_step :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_step (!kl_V3797) = do let pat_cond_0 = do klSet (Types.Atom (Types.UnboundSym "shen.*step*")) (Atom (B True))
                             pat_cond_1 = do klSet (Types.Atom (Types.UnboundSym "shen.*step*")) (Atom (B False))
                             pat_cond_2 = do do simpleError (Types.Atom (Types.Str "step expects a + or a -.\n"))
                          in case kl_V3797 of
                                 kl_V3797@(Atom (UnboundSym "+")) -> pat_cond_0
                                 kl_V3797@(ApplC (PL "+" _)) -> pat_cond_0
                                 kl_V3797@(ApplC (Func "+" _)) -> pat_cond_0
                                 kl_V3797@(Atom (UnboundSym "-")) -> pat_cond_1
                                 kl_V3797@(ApplC (PL "-" _)) -> pat_cond_1
                                 kl_V3797@(ApplC (Func "-" _)) -> pat_cond_1
                                 _ -> pat_cond_2

kl_spy :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_spy (!kl_V3803) = do let pat_cond_0 = do klSet (Types.Atom (Types.UnboundSym "shen.*spy*")) (Atom (B True))
                            pat_cond_1 = do klSet (Types.Atom (Types.UnboundSym "shen.*spy*")) (Atom (B False))
                            pat_cond_2 = do do simpleError (Types.Atom (Types.Str "spy expects a + or a -.\n"))
                         in case kl_V3803 of
                                kl_V3803@(Atom (UnboundSym "+")) -> pat_cond_0
                                kl_V3803@(ApplC (PL "+" _)) -> pat_cond_0
                                kl_V3803@(ApplC (Func "+" _)) -> pat_cond_0
                                kl_V3803@(Atom (UnboundSym "-")) -> pat_cond_1
                                kl_V3803@(ApplC (PL "-" _)) -> pat_cond_1
                                kl_V3803@(ApplC (Func "-" _)) -> pat_cond_1
                                _ -> pat_cond_2

kl_shen_terpri_or_read_char :: Types.KLContext Types.Env
                                               Types.KLValue
kl_shen_terpri_or_read_char = do !kl_if_0 <- value (Types.Atom (Types.UnboundSym "shen.*step*"))
                                 case kl_if_0 of
                                     Atom (B (True)) -> do !appl_1 <- value (Types.Atom (Types.UnboundSym "*stinput*"))
                                                           !appl_2 <- appl_1 `pseq` readByte appl_1
                                                           appl_2 `pseq` kl_shen_check_byte appl_2
                                     Atom (B (False)) -> do do kl_nl (Types.Atom (Types.N (Types.KI 1)))
                                     _ -> throwError "if: expected boolean"

kl_shen_check_byte :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_check_byte (!kl_V3809) = do !appl_0 <- kl_shen_hat
                                    !kl_if_1 <- kl_V3809 `pseq` (appl_0 `pseq` eq kl_V3809 appl_0)
                                    case kl_if_1 of
                                        Atom (B (True)) -> do simpleError (Types.Atom (Types.Str "aborted"))
                                        Atom (B (False)) -> do do return (Atom (B True))
                                        _ -> throwError "if: expected boolean"

kl_shen_input_track :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_input_track (!kl_V3813) (!kl_V3814) (!kl_V3815) = do !appl_0 <- kl_V3813 `pseq` kl_shen_spaces kl_V3813
                                                             !appl_1 <- kl_V3813 `pseq` kl_shen_spaces kl_V3813
                                                             let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [appl_1,
                                                                                                         Types.Atom (Types.Str ""),
                                                                                                         Types.Atom (Types.UnboundSym "shen.a")]
                                                             !appl_4 <- appl_3 `pseq` cn (Types.Atom (Types.Str " \n")) appl_3
                                                             let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_6 <- kl_V3814 `pseq` (appl_4 `pseq` applyWrapper aw_5 [kl_V3814,
                                                                                                                          appl_4,
                                                                                                                          Types.Atom (Types.UnboundSym "shen.a")])
                                                             !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str "> Inputs to ")) appl_6
                                                             let !aw_8 = Types.Atom (Types.UnboundSym "shen.app")
                                                             !appl_9 <- kl_V3813 `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_V3813,
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
                                                             !appl_17 <- kl_V3815 `pseq` kl_shen_recursively_print kl_V3815
                                                             appl_16 `pseq` (appl_17 `pseq` kl_do appl_16 appl_17)

kl_shen_recursively_print :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_recursively_print (!kl_V3817) = do let pat_cond_0 = do !appl_1 <- kl_stoutput
                                                               let !aw_2 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                               appl_1 `pseq` applyWrapper aw_2 [Types.Atom (Types.Str " ==>"),
                                                                                                appl_1]
                                               pat_cond_3 kl_V3817 kl_V3817h kl_V3817t = do let !aw_4 = Types.Atom (Types.UnboundSym "print")
                                                                                            !appl_5 <- kl_V3817h `pseq` applyWrapper aw_4 [kl_V3817h]
                                                                                            !appl_6 <- kl_stoutput
                                                                                            let !aw_7 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                            !appl_8 <- appl_6 `pseq` applyWrapper aw_7 [Types.Atom (Types.Str ", "),
                                                                                                                                        appl_6]
                                                                                            !appl_9 <- kl_V3817t `pseq` kl_shen_recursively_print kl_V3817t
                                                                                            !appl_10 <- appl_8 `pseq` (appl_9 `pseq` kl_do appl_8 appl_9)
                                                                                            appl_5 `pseq` (appl_10 `pseq` kl_do appl_5 appl_10)
                                               pat_cond_11 = do do kl_shen_f_error (ApplC (wrapNamed "shen.recursively-print" kl_shen_recursively_print))
                                            in case kl_V3817 of
                                                   kl_V3817@(Atom (Nil)) -> pat_cond_0
                                                   !(kl_V3817@(Cons (!kl_V3817h)
                                                                    (!kl_V3817t))) -> pat_cond_3 kl_V3817 kl_V3817h kl_V3817t
                                                   _ -> pat_cond_11

kl_shen_spaces :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_spaces (!kl_V3819) = do let pat_cond_0 = do return (Types.Atom (Types.Str ""))
                                    pat_cond_1 = do do !appl_2 <- kl_V3819 `pseq` Primitives.subtract kl_V3819 (Types.Atom (Types.N (Types.KI 1)))
                                                       !appl_3 <- appl_2 `pseq` kl_shen_spaces appl_2
                                                       appl_3 `pseq` cn (Types.Atom (Types.Str " ")) appl_3
                                 in case kl_V3819 of
                                        kl_V3819@(Atom (N (KI 0))) -> pat_cond_0
                                        _ -> pat_cond_1

kl_shen_output_track :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_output_track (!kl_V3823) (!kl_V3824) (!kl_V3825) = do !appl_0 <- kl_V3823 `pseq` kl_shen_spaces kl_V3823
                                                              !appl_1 <- kl_V3823 `pseq` kl_shen_spaces kl_V3823
                                                              let !aw_2 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_3 <- kl_V3825 `pseq` applyWrapper aw_2 [kl_V3825,
                                                                                                            Types.Atom (Types.Str ""),
                                                                                                            Types.Atom (Types.UnboundSym "shen.s")]
                                                              !appl_4 <- appl_3 `pseq` cn (Types.Atom (Types.Str "==> ")) appl_3
                                                              let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_6 <- appl_1 `pseq` (appl_4 `pseq` applyWrapper aw_5 [appl_1,
                                                                                                                         appl_4,
                                                                                                                         Types.Atom (Types.UnboundSym "shen.a")])
                                                              !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str " \n")) appl_6
                                                              let !aw_8 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_9 <- kl_V3824 `pseq` (appl_7 `pseq` applyWrapper aw_8 [kl_V3824,
                                                                                                                           appl_7,
                                                                                                                           Types.Atom (Types.UnboundSym "shen.a")])
                                                              !appl_10 <- appl_9 `pseq` cn (Types.Atom (Types.Str "> Output from ")) appl_9
                                                              let !aw_11 = Types.Atom (Types.UnboundSym "shen.app")
                                                              !appl_12 <- kl_V3823 `pseq` (appl_10 `pseq` applyWrapper aw_11 [kl_V3823,
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
kl_untrack (!kl_V3827) = do !appl_0 <- kl_V3827 `pseq` kl_ps kl_V3827
                            appl_0 `pseq` kl_eval appl_0

kl_profile :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_profile (!kl_V3829) = do !appl_0 <- kl_V3829 `pseq` kl_ps kl_V3829
                            appl_0 `pseq` kl_shen_profile_help appl_0

kl_shen_profile_help :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_profile_help (!kl_V3835) = do let pat_cond_0 kl_V3835 kl_V3835t kl_V3835th kl_V3835tt kl_V3835tth kl_V3835ttt kl_V3835ttth = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_G) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Profile) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Def) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_CompileProfile) -> do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_CompileG) -> do return kl_V3835th)))
                                                                                                                                                                                                                                                                                                                                                                                                             !appl_6 <- kl_Def `pseq` kl_shen_eval_without_macros kl_Def
                                                                                                                                                                                                                                                                                                                                                                                                             appl_6 `pseq` applyWrapper appl_5 [appl_6])))
                                                                                                                                                                                                                                                                                                                                    !appl_7 <- kl_Profile `pseq` kl_shen_eval_without_macros kl_Profile
                                                                                                                                                                                                                                                                                                                                    appl_7 `pseq` applyWrapper appl_4 [appl_7])))
                                                                                                                                                                                                                                                                      !appl_8 <- kl_G `pseq` (kl_V3835th `pseq` (kl_V3835ttth `pseq` kl_subst kl_G kl_V3835th kl_V3835ttth))
                                                                                                                                                                                                                                                                      !appl_9 <- appl_8 `pseq` klCons appl_8 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                      !appl_10 <- kl_V3835tth `pseq` (appl_9 `pseq` klCons kl_V3835tth appl_9)
                                                                                                                                                                                                                                                                      !appl_11 <- kl_G `pseq` (appl_10 `pseq` klCons kl_G appl_10)
                                                                                                                                                                                                                                                                      !appl_12 <- appl_11 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_11
                                                                                                                                                                                                                                                                      appl_12 `pseq` applyWrapper appl_3 [appl_12])))
                                                                                                                                                                                                    !appl_13 <- kl_G `pseq` (kl_V3835tth `pseq` klCons kl_G kl_V3835tth)
                                                                                                                                                                                                    !appl_14 <- kl_V3835th `pseq` (kl_V3835tth `pseq` (appl_13 `pseq` kl_shen_profile_func kl_V3835th kl_V3835tth appl_13))
                                                                                                                                                                                                    !appl_15 <- appl_14 `pseq` klCons appl_14 (Types.Atom Types.Nil)
                                                                                                                                                                                                    !appl_16 <- kl_V3835tth `pseq` (appl_15 `pseq` klCons kl_V3835tth appl_15)
                                                                                                                                                                                                    !appl_17 <- kl_V3835th `pseq` (appl_16 `pseq` klCons kl_V3835th appl_16)
                                                                                                                                                                                                    !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_17
                                                                                                                                                                                                    appl_18 `pseq` applyWrapper appl_2 [appl_18])))
                                                                                                                                        !appl_19 <- kl_gensym (Types.Atom (Types.UnboundSym "shen.f"))
                                                                                                                                        appl_19 `pseq` applyWrapper appl_1 [appl_19]
                                          pat_cond_20 = do do simpleError (Types.Atom (Types.Str "Cannot profile.\n"))
                                       in case kl_V3835 of
                                              !(kl_V3835@(Cons (Atom (UnboundSym "defun"))
                                                               (!(kl_V3835t@(Cons (!kl_V3835th)
                                                                                  (!(kl_V3835tt@(Cons (!kl_V3835tth)
                                                                                                      (!(kl_V3835ttt@(Cons (!kl_V3835ttth)
                                                                                                                           (Atom (Nil))))))))))))) -> pat_cond_0 kl_V3835 kl_V3835t kl_V3835th kl_V3835tt kl_V3835tth kl_V3835ttt kl_V3835ttth
                                              !(kl_V3835@(Cons (ApplC (PL "defun" _))
                                                               (!(kl_V3835t@(Cons (!kl_V3835th)
                                                                                  (!(kl_V3835tt@(Cons (!kl_V3835tth)
                                                                                                      (!(kl_V3835ttt@(Cons (!kl_V3835ttth)
                                                                                                                           (Atom (Nil))))))))))))) -> pat_cond_0 kl_V3835 kl_V3835t kl_V3835th kl_V3835tt kl_V3835tth kl_V3835ttt kl_V3835ttth
                                              !(kl_V3835@(Cons (ApplC (Func "defun" _))
                                                               (!(kl_V3835t@(Cons (!kl_V3835th)
                                                                                  (!(kl_V3835tt@(Cons (!kl_V3835tth)
                                                                                                      (!(kl_V3835ttt@(Cons (!kl_V3835ttth)
                                                                                                                           (Atom (Nil))))))))))))) -> pat_cond_0 kl_V3835 kl_V3835t kl_V3835th kl_V3835tt kl_V3835tth kl_V3835ttt kl_V3835ttth
                                              _ -> pat_cond_20

kl_unprofile :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_unprofile (!kl_V3837) = do kl_V3837 `pseq` kl_untrack kl_V3837

kl_shen_profile_func :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_profile_func (!kl_V3841) (!kl_V3842) (!kl_V3843) = do !appl_0 <- klCons (Types.Atom (Types.UnboundSym "run")) (Types.Atom Types.Nil)
                                                              !appl_1 <- appl_0 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_0
                                                              !appl_2 <- klCons (Types.Atom (Types.UnboundSym "run")) (Types.Atom Types.Nil)
                                                              !appl_3 <- appl_2 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_2
                                                              !appl_4 <- klCons (Types.Atom (Types.UnboundSym "Start")) (Types.Atom Types.Nil)
                                                              !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                              !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_5
                                                              !appl_7 <- kl_V3841 `pseq` klCons kl_V3841 (Types.Atom Types.Nil)
                                                              !appl_8 <- appl_7 `pseq` klCons (ApplC (wrapNamed "shen.get-profile" kl_shen_get_profile)) appl_7
                                                              !appl_9 <- klCons (Types.Atom (Types.UnboundSym "Finish")) (Types.Atom Types.Nil)
                                                              !appl_10 <- appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9)
                                                              !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_10
                                                              !appl_12 <- appl_11 `pseq` klCons appl_11 (Types.Atom Types.Nil)
                                                              !appl_13 <- kl_V3841 `pseq` (appl_12 `pseq` klCons kl_V3841 appl_12)
                                                              !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "shen.put-profile" kl_shen_put_profile)) appl_13
                                                              !appl_15 <- klCons (Types.Atom (Types.UnboundSym "Result")) (Types.Atom Types.Nil)
                                                              !appl_16 <- appl_14 `pseq` (appl_15 `pseq` klCons appl_14 appl_15)
                                                              !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.UnboundSym "Record")) appl_16
                                                              !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_17
                                                              !appl_19 <- appl_18 `pseq` klCons appl_18 (Types.Atom Types.Nil)
                                                              !appl_20 <- appl_6 `pseq` (appl_19 `pseq` klCons appl_6 appl_19)
                                                              !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_20
                                                              !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_21
                                                              !appl_23 <- appl_22 `pseq` klCons appl_22 (Types.Atom Types.Nil)
                                                              !appl_24 <- kl_V3843 `pseq` (appl_23 `pseq` klCons kl_V3843 appl_23)
                                                              !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_24
                                                              !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_25
                                                              !appl_27 <- appl_26 `pseq` klCons appl_26 (Types.Atom Types.Nil)
                                                              !appl_28 <- appl_1 `pseq` (appl_27 `pseq` klCons appl_1 appl_27)
                                                              !appl_29 <- appl_28 `pseq` klCons (Types.Atom (Types.UnboundSym "Start")) appl_28
                                                              appl_29 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_29

kl_profile_results :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_profile_results (!kl_V3845) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Results) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Initialise) -> do kl_V3845 `pseq` (kl_Results `pseq` kl_Atp kl_V3845 kl_Results))))
                                                                                                      !appl_2 <- kl_V3845 `pseq` kl_shen_put_profile kl_V3845 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                      appl_2 `pseq` applyWrapper appl_1 [appl_2])))
                                    !appl_3 <- kl_V3845 `pseq` kl_shen_get_profile kl_V3845
                                    appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_get_profile :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_get_profile (!kl_V3847) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                         kl_V3847 `pseq` (appl_0 `pseq` kl_get kl_V3847 (ApplC (wrapNamed "profile" kl_profile)) appl_0)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.N (Types.KI 0))))

kl_shen_put_profile :: Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_put_profile (!kl_V3850) (!kl_V3851) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                                 kl_V3850 `pseq` (kl_V3851 `pseq` (appl_0 `pseq` kl_put kl_V3850 (ApplC (wrapNamed "profile" kl_profile)) kl_V3851 appl_0))

expr7 :: Types.KLContext Types.Env Types.KLValue
expr7 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
           (do klSet (Types.Atom (Types.UnboundSym "shen.*step*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
