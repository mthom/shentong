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

module Macros where

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
import Track
import Load
import Writer

kl_macroexpand :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_macroexpand (!kl_V773) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do !kl_if_1 <- kl_V773 `pseq` (kl_Y `pseq` eq kl_V773 kl_Y)
                                                                                           klIf kl_if_1 (do return kl_V773) (do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_V770) -> do kl_V770 `pseq` kl_macroexpand kl_V770)))
                                                                                                                                appl_2 `pseq` (kl_Y `pseq` kl_shen_walk appl_2 kl_Y)))))
                               !appl_3 <- value (Types.Atom (Types.UnboundSym "*macros*"))
                               !appl_4 <- appl_3 `pseq` (kl_V773 `pseq` kl_shen_compose appl_3 kl_V773)
                               appl_4 `pseq` applyWrapper appl_0 [appl_4]

kl_shen_error_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_error_macro (!kl_V774) = do !kl_if_0 <- kl_V774 `pseq` consP kl_V774
                                    !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V774 `pseq` hd kl_V774
                                                                 !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "error")) appl_2
                                                                 klIf kl_if_3 (do !appl_4 <- kl_V774 `pseq` tl kl_V774
                                                                                  appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                    klIf kl_if_1 (do !appl_5 <- kl_V774 `pseq` tl kl_V774
                                                     !appl_6 <- appl_5 `pseq` hd appl_5
                                                     !appl_7 <- kl_V774 `pseq` tl kl_V774
                                                     !appl_8 <- appl_7 `pseq` tl appl_7
                                                     !appl_9 <- appl_6 `pseq` (appl_8 `pseq` kl_shen_mkstr appl_6 appl_8)
                                                     let !appl_10 = List []
                                                     !appl_11 <- appl_9 `pseq` (appl_10 `pseq` klCons appl_9 appl_10)
                                                     appl_11 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_11) (do klIf (Atom (B True)) (do return kl_V774) (do return (List [])))

kl_shen_output_macro :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_output_macro (!kl_V775) = do !kl_if_0 <- kl_V775 `pseq` consP kl_V775
                                     !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V775 `pseq` hd kl_V775
                                                                  !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "output")) appl_2
                                                                  klIf kl_if_3 (do !appl_4 <- kl_V775 `pseq` tl kl_V775
                                                                                   appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                     klIf kl_if_1 (do !appl_5 <- kl_V775 `pseq` tl kl_V775
                                                      !appl_6 <- appl_5 `pseq` hd appl_5
                                                      !appl_7 <- kl_V775 `pseq` tl kl_V775
                                                      !appl_8 <- appl_7 `pseq` tl appl_7
                                                      !appl_9 <- appl_6 `pseq` (appl_8 `pseq` kl_shen_mkstr appl_6 appl_8)
                                                      let !appl_10 = List []
                                                      !appl_11 <- appl_10 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_10
                                                      let !appl_12 = List []
                                                      !appl_13 <- appl_11 `pseq` (appl_12 `pseq` klCons appl_11 appl_12)
                                                      !appl_14 <- appl_9 `pseq` (appl_13 `pseq` klCons appl_9 appl_13)
                                                      appl_14 `pseq` klCons (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_14) (do !kl_if_15 <- kl_V775 `pseq` consP kl_V775
                                                                                                                                          !kl_if_16 <- klIf kl_if_15 (do !appl_17 <- kl_V775 `pseq` hd kl_V775
                                                                                                                                                                         !kl_if_18 <- appl_17 `pseq` eq (ApplC (wrapNamed "pr" kl_pr)) appl_17
                                                                                                                                                                         klIf kl_if_18 (do !appl_19 <- kl_V775 `pseq` tl kl_V775
                                                                                                                                                                                           !kl_if_20 <- appl_19 `pseq` consP appl_19
                                                                                                                                                                                           klIf kl_if_20 (do let !appl_21 = List []
                                                                                                                                                                                                             !appl_22 <- kl_V775 `pseq` tl kl_V775
                                                                                                                                                                                                             !appl_23 <- appl_22 `pseq` tl appl_22
                                                                                                                                                                                                             appl_21 `pseq` (appl_23 `pseq` eq appl_21 appl_23)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                          klIf kl_if_16 (do !appl_24 <- kl_V775 `pseq` tl kl_V775
                                                                                                                                                            !appl_25 <- appl_24 `pseq` hd appl_24
                                                                                                                                                            let !appl_26 = List []
                                                                                                                                                            !appl_27 <- appl_26 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_26
                                                                                                                                                            let !appl_28 = List []
                                                                                                                                                            !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                                                                                                                            !appl_30 <- appl_25 `pseq` (appl_29 `pseq` klCons appl_25 appl_29)
                                                                                                                                                            appl_30 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_30) (do klIf (Atom (B True)) (do return kl_V775) (do return (List []))))

kl_shen_make_string_macro :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_make_string_macro (!kl_V776) = do !kl_if_0 <- kl_V776 `pseq` consP kl_V776
                                          !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V776 `pseq` hd kl_V776
                                                                       !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "make-string")) appl_2
                                                                       klIf kl_if_3 (do !appl_4 <- kl_V776 `pseq` tl kl_V776
                                                                                        appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                          klIf kl_if_1 (do !appl_5 <- kl_V776 `pseq` tl kl_V776
                                                           !appl_6 <- appl_5 `pseq` hd appl_5
                                                           !appl_7 <- kl_V776 `pseq` tl kl_V776
                                                           !appl_8 <- appl_7 `pseq` tl appl_7
                                                           appl_6 `pseq` (appl_8 `pseq` kl_shen_mkstr appl_6 appl_8)) (do klIf (Atom (B True)) (do return kl_V776) (do return (List [])))

kl_shen_input_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_input_macro (!kl_V777) = do !kl_if_0 <- kl_V777 `pseq` consP kl_V777
                                    !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V777 `pseq` hd kl_V777
                                                                 !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "lineread" kl_lineread)) appl_2
                                                                 klIf kl_if_3 (do let !appl_4 = List []
                                                                                  !appl_5 <- kl_V777 `pseq` tl kl_V777
                                                                                  appl_4 `pseq` (appl_5 `pseq` eq appl_4 appl_5)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                    klIf kl_if_1 (do let !appl_6 = List []
                                                     !appl_7 <- appl_6 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_6
                                                     let !appl_8 = List []
                                                     !appl_9 <- appl_7 `pseq` (appl_8 `pseq` klCons appl_7 appl_8)
                                                     appl_9 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_9) (do !kl_if_10 <- kl_V777 `pseq` consP kl_V777
                                                                                                                                 !kl_if_11 <- klIf kl_if_10 (do !appl_12 <- kl_V777 `pseq` hd kl_V777
                                                                                                                                                                !kl_if_13 <- appl_12 `pseq` eq (ApplC (wrapNamed "input" kl_input)) appl_12
                                                                                                                                                                klIf kl_if_13 (do let !appl_14 = List []
                                                                                                                                                                                  !appl_15 <- kl_V777 `pseq` tl kl_V777
                                                                                                                                                                                  appl_14 `pseq` (appl_15 `pseq` eq appl_14 appl_15)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                 klIf kl_if_11 (do let !appl_16 = List []
                                                                                                                                                   !appl_17 <- appl_16 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_16
                                                                                                                                                   let !appl_18 = List []
                                                                                                                                                   !appl_19 <- appl_17 `pseq` (appl_18 `pseq` klCons appl_17 appl_18)
                                                                                                                                                   appl_19 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_19) (do !kl_if_20 <- kl_V777 `pseq` consP kl_V777
                                                                                                                                                                                                                           !kl_if_21 <- klIf kl_if_20 (do !appl_22 <- kl_V777 `pseq` hd kl_V777
                                                                                                                                                                                                                                                          !kl_if_23 <- appl_22 `pseq` eq (ApplC (wrapNamed "read" kl_read)) appl_22
                                                                                                                                                                                                                                                          klIf kl_if_23 (do let !appl_24 = List []
                                                                                                                                                                                                                                                                            !appl_25 <- kl_V777 `pseq` tl kl_V777
                                                                                                                                                                                                                                                                            appl_24 `pseq` (appl_25 `pseq` eq appl_24 appl_25)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                           klIf kl_if_21 (do let !appl_26 = List []
                                                                                                                                                                                                                                             !appl_27 <- appl_26 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_26
                                                                                                                                                                                                                                             let !appl_28 = List []
                                                                                                                                                                                                                                             !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                                                                                                                                                                                                             appl_29 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_29) (do !kl_if_30 <- kl_V777 `pseq` consP kl_V777
                                                                                                                                                                                                                                                                                                                   !kl_if_31 <- klIf kl_if_30 (do !appl_32 <- kl_V777 `pseq` hd kl_V777
                                                                                                                                                                                                                                                                                                                                                  !kl_if_33 <- appl_32 `pseq` eq (ApplC (wrapNamed "input+" kl_inputPlus)) appl_32
                                                                                                                                                                                                                                                                                                                                                  klIf kl_if_33 (do !appl_34 <- kl_V777 `pseq` tl kl_V777
                                                                                                                                                                                                                                                                                                                                                                    !kl_if_35 <- appl_34 `pseq` consP appl_34
                                                                                                                                                                                                                                                                                                                                                                    klIf kl_if_35 (do let !appl_36 = List []
                                                                                                                                                                                                                                                                                                                                                                                      !appl_37 <- kl_V777 `pseq` tl kl_V777
                                                                                                                                                                                                                                                                                                                                                                                      !appl_38 <- appl_37 `pseq` tl appl_37
                                                                                                                                                                                                                                                                                                                                                                                      appl_36 `pseq` (appl_38 `pseq` eq appl_36 appl_38)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                                                                   klIf kl_if_31 (do !appl_39 <- kl_V777 `pseq` tl kl_V777
                                                                                                                                                                                                                                                                                                                                     !appl_40 <- appl_39 `pseq` hd appl_39
                                                                                                                                                                                                                                                                                                                                     let !appl_41 = List []
                                                                                                                                                                                                                                                                                                                                     !appl_42 <- appl_41 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_41
                                                                                                                                                                                                                                                                                                                                     let !appl_43 = List []
                                                                                                                                                                                                                                                                                                                                     !appl_44 <- appl_42 `pseq` (appl_43 `pseq` klCons appl_42 appl_43)
                                                                                                                                                                                                                                                                                                                                     !appl_45 <- appl_40 `pseq` (appl_44 `pseq` klCons appl_40 appl_44)
                                                                                                                                                                                                                                                                                                                                     appl_45 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_45) (do !kl_if_46 <- kl_V777 `pseq` consP kl_V777
                                                                                                                                                                                                                                                                                                                                                                                                                  !kl_if_47 <- klIf kl_if_46 (do !appl_48 <- kl_V777 `pseq` hd kl_V777
                                                                                                                                                                                                                                                                                                                                                                                                                                                 !kl_if_49 <- appl_48 `pseq` eq (ApplC (wrapNamed "read-byte" readByte)) appl_48
                                                                                                                                                                                                                                                                                                                                                                                                                                                 klIf kl_if_49 (do let !appl_50 = List []
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   !appl_51 <- kl_V777 `pseq` tl kl_V777
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   appl_50 `pseq` (appl_51 `pseq` eq appl_50 appl_51)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                                                                                                                                                                  klIf kl_if_47 (do let !appl_52 = List []
                                                                                                                                                                                                                                                                                                                                                                                                                                    !appl_53 <- appl_52 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_52
                                                                                                                                                                                                                                                                                                                                                                                                                                    let !appl_54 = List []
                                                                                                                                                                                                                                                                                                                                                                                                                                    !appl_55 <- appl_53 `pseq` (appl_54 `pseq` klCons appl_53 appl_54)
                                                                                                                                                                                                                                                                                                                                                                                                                                    appl_55 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_55) (do klIf (Atom (B True)) (do return kl_V777) (do return (List [])))))))

kl_shen_compose :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_compose (!kl_V778) (!kl_V779) = do let !appl_0 = List []
                                           !kl_if_1 <- appl_0 `pseq` (kl_V778 `pseq` eq appl_0 kl_V778)
                                           klIf kl_if_1 (do return kl_V779) (do !kl_if_2 <- kl_V778 `pseq` consP kl_V778
                                                                                klIf kl_if_2 (do !appl_3 <- kl_V778 `pseq` tl kl_V778
                                                                                                 !appl_4 <- kl_V778 `pseq` hd kl_V778
                                                                                                 !appl_5 <- kl_V779 `pseq` applyWrapper appl_4 [kl_V779]
                                                                                                 appl_3 `pseq` (appl_5 `pseq` kl_shen_compose appl_3 appl_5)) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.compose" kl_shen_compose))) (do return (List []))))

kl_shen_compile_macro :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_compile_macro (!kl_V780) = do !kl_if_0 <- kl_V780 `pseq` consP kl_V780
                                      !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V780 `pseq` hd kl_V780
                                                                   !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "compile" kl_compile)) appl_2
                                                                   klIf kl_if_3 (do !appl_4 <- kl_V780 `pseq` tl kl_V780
                                                                                    !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                    klIf kl_if_5 (do !appl_6 <- kl_V780 `pseq` tl kl_V780
                                                                                                     !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                     !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                     klIf kl_if_8 (do let !appl_9 = List []
                                                                                                                      !appl_10 <- kl_V780 `pseq` tl kl_V780
                                                                                                                      !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                      !appl_12 <- appl_11 `pseq` tl appl_11
                                                                                                                      appl_9 `pseq` (appl_12 `pseq` eq appl_9 appl_12)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                      klIf kl_if_1 (do !appl_13 <- kl_V780 `pseq` tl kl_V780
                                                       !appl_14 <- appl_13 `pseq` hd appl_13
                                                       !appl_15 <- kl_V780 `pseq` tl kl_V780
                                                       !appl_16 <- appl_15 `pseq` tl appl_15
                                                       !appl_17 <- appl_16 `pseq` hd appl_16
                                                       let !appl_18 = List []
                                                       !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_18
                                                       !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_19
                                                       let !appl_21 = List []
                                                       !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_21
                                                       !appl_23 <- appl_22 `pseq` klCons (Types.Atom (Types.Str "parse error here: ~S~%")) appl_22
                                                       !appl_24 <- appl_23 `pseq` klCons (Types.Atom (Types.UnboundSym "error")) appl_23
                                                       let !appl_25 = List []
                                                       !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.Str "parse error~%")) appl_25
                                                       !appl_27 <- appl_26 `pseq` klCons (Types.Atom (Types.UnboundSym "error")) appl_26
                                                       let !appl_28 = List []
                                                       !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                       !appl_30 <- appl_24 `pseq` (appl_29 `pseq` klCons appl_24 appl_29)
                                                       !appl_31 <- appl_20 `pseq` (appl_30 `pseq` klCons appl_20 appl_30)
                                                       !appl_32 <- appl_31 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_31
                                                       let !appl_33 = List []
                                                       !appl_34 <- appl_32 `pseq` (appl_33 `pseq` klCons appl_32 appl_33)
                                                       !appl_35 <- appl_34 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_34
                                                       !appl_36 <- appl_35 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_35
                                                       let !appl_37 = List []
                                                       !appl_38 <- appl_36 `pseq` (appl_37 `pseq` klCons appl_36 appl_37)
                                                       !appl_39 <- appl_17 `pseq` (appl_38 `pseq` klCons appl_17 appl_38)
                                                       !appl_40 <- appl_14 `pseq` (appl_39 `pseq` klCons appl_14 appl_39)
                                                       appl_40 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_40) (do klIf (Atom (B True)) (do return kl_V780) (do return (List [])))

kl_shen_prolog_macro :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_prolog_macro (!kl_V781) = do !kl_if_0 <- kl_V781 `pseq` consP kl_V781
                                     !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V781 `pseq` hd kl_V781
                                                                  appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "prolog?")) appl_2) (do return (Atom (B False)))
                                     klIf kl_if_1 (do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_F) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Receive) -> do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_PrologDef) -> do let !appl_6 = ApplC (Func "lambda" (Context (\(!kl_Query) -> do return kl_Query)))
                                                                                                                                                                                                                                                        let !appl_7 = List []
                                                                                                                                                                                                                                                        !appl_8 <- appl_7 `pseq` klCons (ApplC (PL "shen.start-new-prolog-process" kl_shen_start_new_prolog_process)) appl_7
                                                                                                                                                                                                                                                        let !appl_9 = List []
                                                                                                                                                                                                                                                        !appl_10 <- appl_9 `pseq` klCons (Atom (B True)) appl_9
                                                                                                                                                                                                                                                        !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.UnboundSym "freeze")) appl_10
                                                                                                                                                                                                                                                        let !appl_12 = List []
                                                                                                                                                                                                                                                        !appl_13 <- appl_11 `pseq` (appl_12 `pseq` klCons appl_11 appl_12)
                                                                                                                                                                                                                                                        !appl_14 <- appl_8 `pseq` (appl_13 `pseq` klCons appl_8 appl_13)
                                                                                                                                                                                                                                                        !appl_15 <- kl_Receive `pseq` (appl_14 `pseq` kl_append kl_Receive appl_14)
                                                                                                                                                                                                                                                        !appl_16 <- kl_F `pseq` (appl_15 `pseq` klCons kl_F appl_15)
                                                                                                                                                                                                                                                        appl_16 `pseq` applyWrapper appl_6 [appl_16])))
                                                                                                                                                                                    let !appl_17 = List []
                                                                                                                                                                                    !appl_18 <- kl_F `pseq` (appl_17 `pseq` klCons kl_F appl_17)
                                                                                                                                                                                    !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.UnboundSym "defprolog")) appl_18
                                                                                                                                                                                    let !appl_20 = List []
                                                                                                                                                                                    !appl_21 <- appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "<--")) appl_20
                                                                                                                                                                                    !appl_22 <- kl_V781 `pseq` tl kl_V781
                                                                                                                                                                                    !appl_23 <- appl_22 `pseq` kl_shen_pass_literals appl_22
                                                                                                                                                                                    let !appl_24 = List []
                                                                                                                                                                                    !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.UnboundSym ";")) appl_24
                                                                                                                                                                                    !appl_26 <- appl_23 `pseq` (appl_25 `pseq` kl_append appl_23 appl_25)
                                                                                                                                                                                    !appl_27 <- appl_21 `pseq` (appl_26 `pseq` kl_append appl_21 appl_26)
                                                                                                                                                                                    !appl_28 <- kl_Receive `pseq` (appl_27 `pseq` kl_append kl_Receive appl_27)
                                                                                                                                                                                    !appl_29 <- appl_19 `pseq` (appl_28 `pseq` kl_append appl_19 appl_28)
                                                                                                                                                                                    !appl_30 <- appl_29 `pseq` kl_eval appl_29
                                                                                                                                                                                    appl_30 `pseq` applyWrapper appl_5 [appl_30])))
                                                                                                                  !appl_31 <- kl_V781 `pseq` tl kl_V781
                                                                                                                  !appl_32 <- appl_31 `pseq` kl_shen_receive_terms appl_31
                                                                                                                  appl_32 `pseq` applyWrapper appl_4 [appl_32])))
                                                      !appl_33 <- kl_gensym (Types.Atom (Types.UnboundSym "shen.f"))
                                                      appl_33 `pseq` applyWrapper appl_3 [appl_33]) (do klIf (Atom (B True)) (do return kl_V781) (do return (List [])))

kl_shen_receive_terms :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_receive_terms (!kl_V786) = do let !appl_0 = List []
                                      !kl_if_1 <- appl_0 `pseq` (kl_V786 `pseq` eq appl_0 kl_V786)
                                      klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V786 `pseq` consP kl_V786
                                                                             !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V786 `pseq` hd kl_V786
                                                                                                          !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                          klIf kl_if_5 (do !appl_6 <- kl_V786 `pseq` hd kl_V786
                                                                                                                           !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                           !kl_if_8 <- appl_7 `pseq` eq (Types.Atom (Types.UnboundSym "shen.receive")) appl_7
                                                                                                                           klIf kl_if_8 (do !appl_9 <- kl_V786 `pseq` hd kl_V786
                                                                                                                                            !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                                            !kl_if_11 <- appl_10 `pseq` consP appl_10
                                                                                                                                            klIf kl_if_11 (do let !appl_12 = List []
                                                                                                                                                              !appl_13 <- kl_V786 `pseq` hd kl_V786
                                                                                                                                                              !appl_14 <- appl_13 `pseq` tl appl_13
                                                                                                                                                              !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                                              appl_12 `pseq` (appl_15 `pseq` eq appl_12 appl_15)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                             klIf kl_if_3 (do !appl_16 <- kl_V786 `pseq` hd kl_V786
                                                                                              !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                              !appl_18 <- appl_17 `pseq` hd appl_17
                                                                                              !appl_19 <- kl_V786 `pseq` tl kl_V786
                                                                                              !appl_20 <- appl_19 `pseq` kl_shen_receive_terms appl_19
                                                                                              appl_18 `pseq` (appl_20 `pseq` klCons appl_18 appl_20)) (do !kl_if_21 <- kl_V786 `pseq` consP kl_V786
                                                                                                                                                          klIf kl_if_21 (do !appl_22 <- kl_V786 `pseq` tl kl_V786
                                                                                                                                                                            appl_22 `pseq` kl_shen_receive_terms appl_22) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.receive-terms" kl_shen_receive_terms))) (do return (List [])))))

kl_shen_pass_literals :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_pass_literals (!kl_V789) = do let !appl_0 = List []
                                      !kl_if_1 <- appl_0 `pseq` (kl_V789 `pseq` eq appl_0 kl_V789)
                                      klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V789 `pseq` consP kl_V789
                                                                             !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V789 `pseq` hd kl_V789
                                                                                                          !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                          klIf kl_if_5 (do !appl_6 <- kl_V789 `pseq` hd kl_V789
                                                                                                                           !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                           !kl_if_8 <- appl_7 `pseq` eq (Types.Atom (Types.UnboundSym "shen.receive")) appl_7
                                                                                                                           klIf kl_if_8 (do !appl_9 <- kl_V789 `pseq` hd kl_V789
                                                                                                                                            !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                                            !kl_if_11 <- appl_10 `pseq` consP appl_10
                                                                                                                                            klIf kl_if_11 (do let !appl_12 = List []
                                                                                                                                                              !appl_13 <- kl_V789 `pseq` hd kl_V789
                                                                                                                                                              !appl_14 <- appl_13 `pseq` tl appl_13
                                                                                                                                                              !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                                              appl_12 `pseq` (appl_15 `pseq` eq appl_12 appl_15)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                             klIf kl_if_3 (do !appl_16 <- kl_V789 `pseq` tl kl_V789
                                                                                              appl_16 `pseq` kl_shen_pass_literals appl_16) (do !kl_if_17 <- kl_V789 `pseq` consP kl_V789
                                                                                                                                                klIf kl_if_17 (do !appl_18 <- kl_V789 `pseq` hd kl_V789
                                                                                                                                                                  !appl_19 <- kl_V789 `pseq` tl kl_V789
                                                                                                                                                                  !appl_20 <- appl_19 `pseq` kl_shen_pass_literals appl_19
                                                                                                                                                                  appl_18 `pseq` (appl_20 `pseq` klCons appl_18 appl_20)) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.pass-literals" kl_shen_pass_literals))) (do return (List [])))))

kl_shen_defprolog_macro :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_defprolog_macro (!kl_V790) = do !kl_if_0 <- kl_V790 `pseq` consP kl_V790
                                        !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V790 `pseq` hd kl_V790
                                                                     !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "defprolog")) appl_2
                                                                     klIf kl_if_3 (do !appl_4 <- kl_V790 `pseq` tl kl_V790
                                                                                      appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                        klIf kl_if_1 (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_V771) -> do kl_V771 `pseq` kl_shen_LBdefprologRB kl_V771)))
                                                         !appl_6 <- kl_V790 `pseq` tl kl_V790
                                                         let !appl_7 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do !appl_8 <- kl_V790 `pseq` tl kl_V790
                                                                                                                     !appl_9 <- appl_8 `pseq` hd appl_8
                                                                                                                     appl_9 `pseq` (kl_Y `pseq` kl_shen_prolog_error appl_9 kl_Y))))
                                                         appl_5 `pseq` (appl_6 `pseq` (appl_7 `pseq` kl_compile appl_5 appl_6 appl_7))) (do klIf (Atom (B True)) (do return kl_V790) (do return (List [])))

kl_shen_datatype_macro :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_datatype_macro (!kl_V791) = do !kl_if_0 <- kl_V791 `pseq` consP kl_V791
                                       !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V791 `pseq` hd kl_V791
                                                                    !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "datatype")) appl_2
                                                                    klIf kl_if_3 (do !appl_4 <- kl_V791 `pseq` tl kl_V791
                                                                                     appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                       klIf kl_if_1 (do !appl_5 <- kl_V791 `pseq` tl kl_V791
                                                        !appl_6 <- appl_5 `pseq` hd appl_5
                                                        !appl_7 <- appl_6 `pseq` kl_shen_intern_type appl_6
                                                        let !appl_8 = List []
                                                        !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "shen.<datatype-rules>" kl_shen_LBdatatype_rulesRB)) appl_8
                                                        !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.UnboundSym "function")) appl_9
                                                        !appl_11 <- kl_V791 `pseq` tl kl_V791
                                                        !appl_12 <- appl_11 `pseq` tl appl_11
                                                        !appl_13 <- appl_12 `pseq` kl_shen_rcons_form appl_12
                                                        let !appl_14 = List []
                                                        !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "shen.datatype-error" kl_shen_datatype_error)) appl_14
                                                        !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.UnboundSym "function")) appl_15
                                                        let !appl_17 = List []
                                                        !appl_18 <- appl_16 `pseq` (appl_17 `pseq` klCons appl_16 appl_17)
                                                        !appl_19 <- appl_13 `pseq` (appl_18 `pseq` klCons appl_13 appl_18)
                                                        !appl_20 <- appl_10 `pseq` (appl_19 `pseq` klCons appl_10 appl_19)
                                                        !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_20
                                                        let !appl_22 = List []
                                                        !appl_23 <- appl_21 `pseq` (appl_22 `pseq` klCons appl_21 appl_22)
                                                        !appl_24 <- appl_7 `pseq` (appl_23 `pseq` klCons appl_7 appl_23)
                                                        appl_24 `pseq` klCons (ApplC (wrapNamed "shen.process-datatype" kl_shen_process_datatype)) appl_24) (do klIf (Atom (B True)) (do return kl_V791) (do return (List [])))

kl_shen_intern_type :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_intern_type (!kl_V792) = do !appl_0 <- kl_V792 `pseq` str kl_V792
                                    !appl_1 <- appl_0 `pseq` cn (Types.Atom (Types.Str "type#")) appl_0
                                    appl_1 `pseq` intern appl_1

kl_shen_Ats_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_Ats_macro (!kl_V793) = do !kl_if_0 <- kl_V793 `pseq` consP kl_V793
                                  !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V793 `pseq` hd kl_V793
                                                               !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "@s" kl_Ats)) appl_2
                                                               klIf kl_if_3 (do !appl_4 <- kl_V793 `pseq` tl kl_V793
                                                                                !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                klIf kl_if_5 (do !appl_6 <- kl_V793 `pseq` tl kl_V793
                                                                                                 !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                 !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                 klIf kl_if_8 (do !appl_9 <- kl_V793 `pseq` tl kl_V793
                                                                                                                  !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                  !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                  appl_11 `pseq` consP appl_11) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                  klIf kl_if_1 (do !appl_12 <- kl_V793 `pseq` tl kl_V793
                                                   !appl_13 <- appl_12 `pseq` hd appl_12
                                                   !appl_14 <- kl_V793 `pseq` tl kl_V793
                                                   !appl_15 <- appl_14 `pseq` tl appl_14
                                                   !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_15
                                                   !appl_17 <- appl_16 `pseq` kl_shen_Ats_macro appl_16
                                                   let !appl_18 = List []
                                                   !appl_19 <- appl_17 `pseq` (appl_18 `pseq` klCons appl_17 appl_18)
                                                   !appl_20 <- appl_13 `pseq` (appl_19 `pseq` klCons appl_13 appl_19)
                                                   appl_20 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_20) (do !kl_if_21 <- kl_V793 `pseq` consP kl_V793
                                                                                                                      !kl_if_22 <- klIf kl_if_21 (do !appl_23 <- kl_V793 `pseq` hd kl_V793
                                                                                                                                                     !kl_if_24 <- appl_23 `pseq` eq (ApplC (wrapNamed "@s" kl_Ats)) appl_23
                                                                                                                                                     klIf kl_if_24 (do !appl_25 <- kl_V793 `pseq` tl kl_V793
                                                                                                                                                                       !kl_if_26 <- appl_25 `pseq` consP appl_25
                                                                                                                                                                       klIf kl_if_26 (do !appl_27 <- kl_V793 `pseq` tl kl_V793
                                                                                                                                                                                         !appl_28 <- appl_27 `pseq` tl appl_27
                                                                                                                                                                                         !kl_if_29 <- appl_28 `pseq` consP appl_28
                                                                                                                                                                                         klIf kl_if_29 (do let !appl_30 = List []
                                                                                                                                                                                                           !appl_31 <- kl_V793 `pseq` tl kl_V793
                                                                                                                                                                                                           !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                                           !appl_33 <- appl_32 `pseq` tl appl_32
                                                                                                                                                                                                           !kl_if_34 <- appl_30 `pseq` (appl_33 `pseq` eq appl_30 appl_33)
                                                                                                                                                                                                           klIf kl_if_34 (do !appl_35 <- kl_V793 `pseq` tl kl_V793
                                                                                                                                                                                                                             !appl_36 <- appl_35 `pseq` hd appl_35
                                                                                                                                                                                                                             appl_36 `pseq` stringP appl_36) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                      klIf kl_if_22 (do let !appl_37 = ApplC (Func "lambda" (Context (\(!kl_E) -> do !appl_38 <- kl_E `pseq` kl_length kl_E
                                                                                                                                                                                                     !kl_if_39 <- appl_38 `pseq` greaterThan appl_38 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                     klIf kl_if_39 (do !appl_40 <- kl_V793 `pseq` tl kl_V793
                                                                                                                                                                                                                       !appl_41 <- appl_40 `pseq` tl appl_40
                                                                                                                                                                                                                       !appl_42 <- kl_E `pseq` (appl_41 `pseq` kl_append kl_E appl_41)
                                                                                                                                                                                                                       !appl_43 <- appl_42 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_42
                                                                                                                                                                                                                       appl_43 `pseq` kl_shen_Ats_macro appl_43) (do return kl_V793))))
                                                                                                                                        !appl_44 <- kl_V793 `pseq` tl kl_V793
                                                                                                                                        !appl_45 <- appl_44 `pseq` hd appl_44
                                                                                                                                        !appl_46 <- appl_45 `pseq` kl_explode appl_45
                                                                                                                                        appl_46 `pseq` applyWrapper appl_37 [appl_46]) (do klIf (Atom (B True)) (do return kl_V793) (do return (List []))))

kl_shen_synonyms_macro :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_synonyms_macro (!kl_V794) = do !kl_if_0 <- kl_V794 `pseq` consP kl_V794
                                       !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V794 `pseq` hd kl_V794
                                                                    appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "synonyms")) appl_2) (do return (Atom (B False)))
                                       klIf kl_if_1 (do !appl_3 <- kl_V794 `pseq` tl kl_V794
                                                        !appl_4 <- appl_3 `pseq` kl_shen_curry_synonyms appl_3
                                                        !appl_5 <- appl_4 `pseq` kl_shen_rcons_form appl_4
                                                        let !appl_6 = List []
                                                        !appl_7 <- appl_5 `pseq` (appl_6 `pseq` klCons appl_5 appl_6)
                                                        appl_7 `pseq` klCons (ApplC (wrapNamed "shen.synonyms-help" kl_shen_synonyms_help)) appl_7) (do klIf (Atom (B True)) (do return kl_V794) (do return (List [])))

kl_shen_curry_synonyms :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_curry_synonyms (!kl_V795) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_V772) -> do kl_V772 `pseq` kl_shen_curry_type kl_V772)))
                                       appl_0 `pseq` (kl_V795 `pseq` kl_map appl_0 kl_V795)

kl_shen_nl_macro :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_nl_macro (!kl_V796) = do !kl_if_0 <- kl_V796 `pseq` consP kl_V796
                                 !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V796 `pseq` hd kl_V796
                                                              !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "nl" kl_nl)) appl_2
                                                              klIf kl_if_3 (do let !appl_4 = List []
                                                                               !appl_5 <- kl_V796 `pseq` tl kl_V796
                                                                               appl_4 `pseq` (appl_5 `pseq` eq appl_4 appl_5)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                 klIf kl_if_1 (do let !appl_6 = List []
                                                  !appl_7 <- appl_6 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_6
                                                  appl_7 `pseq` klCons (ApplC (wrapNamed "nl" kl_nl)) appl_7) (do klIf (Atom (B True)) (do return kl_V796) (do return (List [])))

kl_shen_assoc_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_assoc_macro (!kl_V797) = do !kl_if_0 <- kl_V797 `pseq` consP kl_V797
                                    !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V797 `pseq` tl kl_V797
                                                                 !kl_if_3 <- appl_2 `pseq` consP appl_2
                                                                 klIf kl_if_3 (do !appl_4 <- kl_V797 `pseq` tl kl_V797
                                                                                  !appl_5 <- appl_4 `pseq` tl appl_4
                                                                                  !kl_if_6 <- appl_5 `pseq` consP appl_5
                                                                                  klIf kl_if_6 (do !appl_7 <- kl_V797 `pseq` tl kl_V797
                                                                                                   !appl_8 <- appl_7 `pseq` tl appl_7
                                                                                                   !appl_9 <- appl_8 `pseq` tl appl_8
                                                                                                   !kl_if_10 <- appl_9 `pseq` consP appl_9
                                                                                                   klIf kl_if_10 (do !appl_11 <- kl_V797 `pseq` hd kl_V797
                                                                                                                     let !appl_12 = List []
                                                                                                                     !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_12
                                                                                                                     !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_13
                                                                                                                     !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_14
                                                                                                                     !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.UnboundSym "or")) appl_15
                                                                                                                     !appl_17 <- appl_16 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_16
                                                                                                                     !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_17
                                                                                                                     !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_18
                                                                                                                     !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_19
                                                                                                                     appl_11 `pseq` (appl_20 `pseq` kl_elementP appl_11 appl_20)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                    klIf kl_if_1 (do !appl_21 <- kl_V797 `pseq` hd kl_V797
                                                     !appl_22 <- kl_V797 `pseq` tl kl_V797
                                                     !appl_23 <- appl_22 `pseq` hd appl_22
                                                     !appl_24 <- kl_V797 `pseq` hd kl_V797
                                                     !appl_25 <- kl_V797 `pseq` tl kl_V797
                                                     !appl_26 <- appl_25 `pseq` tl appl_25
                                                     !appl_27 <- appl_24 `pseq` (appl_26 `pseq` klCons appl_24 appl_26)
                                                     !appl_28 <- appl_27 `pseq` kl_shen_assoc_macro appl_27
                                                     let !appl_29 = List []
                                                     !appl_30 <- appl_28 `pseq` (appl_29 `pseq` klCons appl_28 appl_29)
                                                     !appl_31 <- appl_23 `pseq` (appl_30 `pseq` klCons appl_23 appl_30)
                                                     appl_21 `pseq` (appl_31 `pseq` klCons appl_21 appl_31)) (do klIf (Atom (B True)) (do return kl_V797) (do return (List [])))

kl_shen_let_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_let_macro (!kl_V798) = do !kl_if_0 <- kl_V798 `pseq` consP kl_V798
                                  !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V798 `pseq` hd kl_V798
                                                               !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "let")) appl_2
                                                               klIf kl_if_3 (do !appl_4 <- kl_V798 `pseq` tl kl_V798
                                                                                !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                klIf kl_if_5 (do !appl_6 <- kl_V798 `pseq` tl kl_V798
                                                                                                 !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                 !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                 klIf kl_if_8 (do !appl_9 <- kl_V798 `pseq` tl kl_V798
                                                                                                                  !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                  !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                  !kl_if_12 <- appl_11 `pseq` consP appl_11
                                                                                                                  klIf kl_if_12 (do !appl_13 <- kl_V798 `pseq` tl kl_V798
                                                                                                                                    !appl_14 <- appl_13 `pseq` tl appl_13
                                                                                                                                    !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                    !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                    appl_16 `pseq` consP appl_16) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                  klIf kl_if_1 (do !appl_17 <- kl_V798 `pseq` tl kl_V798
                                                   !appl_18 <- appl_17 `pseq` hd appl_17
                                                   !appl_19 <- kl_V798 `pseq` tl kl_V798
                                                   !appl_20 <- appl_19 `pseq` tl appl_19
                                                   !appl_21 <- appl_20 `pseq` hd appl_20
                                                   !appl_22 <- kl_V798 `pseq` tl kl_V798
                                                   !appl_23 <- appl_22 `pseq` tl appl_22
                                                   !appl_24 <- appl_23 `pseq` tl appl_23
                                                   !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_24
                                                   !appl_26 <- appl_25 `pseq` kl_shen_let_macro appl_25
                                                   let !appl_27 = List []
                                                   !appl_28 <- appl_26 `pseq` (appl_27 `pseq` klCons appl_26 appl_27)
                                                   !appl_29 <- appl_21 `pseq` (appl_28 `pseq` klCons appl_21 appl_28)
                                                   !appl_30 <- appl_18 `pseq` (appl_29 `pseq` klCons appl_18 appl_29)
                                                   appl_30 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_30) (do klIf (Atom (B True)) (do return kl_V798) (do return (List [])))

kl_shen_abs_macro :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_abs_macro (!kl_V799) = do !kl_if_0 <- kl_V799 `pseq` consP kl_V799
                                  !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V799 `pseq` hd kl_V799
                                                               !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "/.")) appl_2
                                                               klIf kl_if_3 (do !appl_4 <- kl_V799 `pseq` tl kl_V799
                                                                                !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                klIf kl_if_5 (do !appl_6 <- kl_V799 `pseq` tl kl_V799
                                                                                                 !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                 !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                 klIf kl_if_8 (do !appl_9 <- kl_V799 `pseq` tl kl_V799
                                                                                                                  !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                  !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                  appl_11 `pseq` consP appl_11) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                  klIf kl_if_1 (do !appl_12 <- kl_V799 `pseq` tl kl_V799
                                                   !appl_13 <- appl_12 `pseq` hd appl_12
                                                   !appl_14 <- kl_V799 `pseq` tl kl_V799
                                                   !appl_15 <- appl_14 `pseq` tl appl_14
                                                   !appl_16 <- appl_15 `pseq` klCons (Types.Atom (Types.UnboundSym "/.")) appl_15
                                                   !appl_17 <- appl_16 `pseq` kl_shen_abs_macro appl_16
                                                   let !appl_18 = List []
                                                   !appl_19 <- appl_17 `pseq` (appl_18 `pseq` klCons appl_17 appl_18)
                                                   !appl_20 <- appl_13 `pseq` (appl_19 `pseq` klCons appl_13 appl_19)
                                                   appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_20) (do !kl_if_21 <- kl_V799 `pseq` consP kl_V799
                                                                                                                               !kl_if_22 <- klIf kl_if_21 (do !appl_23 <- kl_V799 `pseq` hd kl_V799
                                                                                                                                                              !kl_if_24 <- appl_23 `pseq` eq (Types.Atom (Types.UnboundSym "/.")) appl_23
                                                                                                                                                              klIf kl_if_24 (do !appl_25 <- kl_V799 `pseq` tl kl_V799
                                                                                                                                                                                !kl_if_26 <- appl_25 `pseq` consP appl_25
                                                                                                                                                                                klIf kl_if_26 (do !appl_27 <- kl_V799 `pseq` tl kl_V799
                                                                                                                                                                                                  !appl_28 <- appl_27 `pseq` tl appl_27
                                                                                                                                                                                                  !kl_if_29 <- appl_28 `pseq` consP appl_28
                                                                                                                                                                                                  klIf kl_if_29 (do let !appl_30 = List []
                                                                                                                                                                                                                    !appl_31 <- kl_V799 `pseq` tl kl_V799
                                                                                                                                                                                                                    !appl_32 <- appl_31 `pseq` tl appl_31
                                                                                                                                                                                                                    !appl_33 <- appl_32 `pseq` tl appl_32
                                                                                                                                                                                                                    appl_30 `pseq` (appl_33 `pseq` eq appl_30 appl_33)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                               klIf kl_if_22 (do !appl_34 <- kl_V799 `pseq` tl kl_V799
                                                                                                                                                 appl_34 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_34) (do klIf (Atom (B True)) (do return kl_V799) (do return (List []))))

kl_shen_cases_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_cases_macro (!kl_V802) = do !kl_if_0 <- kl_V802 `pseq` consP kl_V802
                                    !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V802 `pseq` hd kl_V802
                                                                 !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "cases")) appl_2
                                                                 klIf kl_if_3 (do !appl_4 <- kl_V802 `pseq` tl kl_V802
                                                                                  !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                  klIf kl_if_5 (do !appl_6 <- kl_V802 `pseq` tl kl_V802
                                                                                                   !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                   !kl_if_8 <- appl_7 `pseq` eq (Atom (B True)) appl_7
                                                                                                   klIf kl_if_8 (do !appl_9 <- kl_V802 `pseq` tl kl_V802
                                                                                                                    !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                    appl_10 `pseq` consP appl_10) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                    klIf kl_if_1 (do !appl_11 <- kl_V802 `pseq` tl kl_V802
                                                     !appl_12 <- appl_11 `pseq` tl appl_11
                                                     appl_12 `pseq` hd appl_12) (do !kl_if_13 <- kl_V802 `pseq` consP kl_V802
                                                                                    !kl_if_14 <- klIf kl_if_13 (do !appl_15 <- kl_V802 `pseq` hd kl_V802
                                                                                                                   !kl_if_16 <- appl_15 `pseq` eq (Types.Atom (Types.UnboundSym "cases")) appl_15
                                                                                                                   klIf kl_if_16 (do !appl_17 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                     !kl_if_18 <- appl_17 `pseq` consP appl_17
                                                                                                                                     klIf kl_if_18 (do !appl_19 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                       !appl_20 <- appl_19 `pseq` tl appl_19
                                                                                                                                                       !kl_if_21 <- appl_20 `pseq` consP appl_20
                                                                                                                                                       klIf kl_if_21 (do let !appl_22 = List []
                                                                                                                                                                         !appl_23 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                         !appl_24 <- appl_23 `pseq` tl appl_23
                                                                                                                                                                         !appl_25 <- appl_24 `pseq` tl appl_24
                                                                                                                                                                         appl_22 `pseq` (appl_25 `pseq` eq appl_22 appl_25)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                    klIf kl_if_14 (do !appl_26 <- kl_V802 `pseq` tl kl_V802
                                                                                                      !appl_27 <- appl_26 `pseq` hd appl_26
                                                                                                      !appl_28 <- kl_V802 `pseq` tl kl_V802
                                                                                                      !appl_29 <- appl_28 `pseq` tl appl_28
                                                                                                      !appl_30 <- appl_29 `pseq` hd appl_29
                                                                                                      let !appl_31 = List []
                                                                                                      !appl_32 <- appl_31 `pseq` klCons (Types.Atom (Types.Str "error: cases exhausted")) appl_31
                                                                                                      !appl_33 <- appl_32 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_32
                                                                                                      let !appl_34 = List []
                                                                                                      !appl_35 <- appl_33 `pseq` (appl_34 `pseq` klCons appl_33 appl_34)
                                                                                                      !appl_36 <- appl_30 `pseq` (appl_35 `pseq` klCons appl_30 appl_35)
                                                                                                      !appl_37 <- appl_27 `pseq` (appl_36 `pseq` klCons appl_27 appl_36)
                                                                                                      appl_37 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_37) (do !kl_if_38 <- kl_V802 `pseq` consP kl_V802
                                                                                                                                                                              !kl_if_39 <- klIf kl_if_38 (do !appl_40 <- kl_V802 `pseq` hd kl_V802
                                                                                                                                                                                                             !kl_if_41 <- appl_40 `pseq` eq (Types.Atom (Types.UnboundSym "cases")) appl_40
                                                                                                                                                                                                             klIf kl_if_41 (do !appl_42 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                                               !kl_if_43 <- appl_42 `pseq` consP appl_42
                                                                                                                                                                                                                               klIf kl_if_43 (do !appl_44 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                                                                 !appl_45 <- appl_44 `pseq` tl appl_44
                                                                                                                                                                                                                                                 appl_45 `pseq` consP appl_45) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                              klIf kl_if_39 (do !appl_46 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                !appl_47 <- appl_46 `pseq` hd appl_46
                                                                                                                                                                                                !appl_48 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                !appl_49 <- appl_48 `pseq` tl appl_48
                                                                                                                                                                                                !appl_50 <- appl_49 `pseq` hd appl_49
                                                                                                                                                                                                !appl_51 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                !appl_52 <- appl_51 `pseq` tl appl_51
                                                                                                                                                                                                !appl_53 <- appl_52 `pseq` tl appl_52
                                                                                                                                                                                                !appl_54 <- appl_53 `pseq` klCons (Types.Atom (Types.UnboundSym "cases")) appl_53
                                                                                                                                                                                                !appl_55 <- appl_54 `pseq` kl_shen_cases_macro appl_54
                                                                                                                                                                                                let !appl_56 = List []
                                                                                                                                                                                                !appl_57 <- appl_55 `pseq` (appl_56 `pseq` klCons appl_55 appl_56)
                                                                                                                                                                                                !appl_58 <- appl_50 `pseq` (appl_57 `pseq` klCons appl_50 appl_57)
                                                                                                                                                                                                !appl_59 <- appl_47 `pseq` (appl_58 `pseq` klCons appl_47 appl_58)
                                                                                                                                                                                                appl_59 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_59) (do !kl_if_60 <- kl_V802 `pseq` consP kl_V802
                                                                                                                                                                                                                                                                        !kl_if_61 <- klIf kl_if_60 (do !appl_62 <- kl_V802 `pseq` hd kl_V802
                                                                                                                                                                                                                                                                                                       !kl_if_63 <- appl_62 `pseq` eq (Types.Atom (Types.UnboundSym "cases")) appl_62
                                                                                                                                                                                                                                                                                                       klIf kl_if_63 (do !appl_64 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                                                                                                                                         !kl_if_65 <- appl_64 `pseq` consP appl_64
                                                                                                                                                                                                                                                                                                                         klIf kl_if_65 (do let !appl_66 = List []
                                                                                                                                                                                                                                                                                                                                           !appl_67 <- kl_V802 `pseq` tl kl_V802
                                                                                                                                                                                                                                                                                                                                           !appl_68 <- appl_67 `pseq` tl appl_67
                                                                                                                                                                                                                                                                                                                                           appl_66 `pseq` (appl_68 `pseq` eq appl_66 appl_68)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                                                                        klIf kl_if_61 (do simpleError (Types.Atom (Types.Str "error: odd number of case elements\n"))) (do klIf (Atom (B True)) (do return kl_V802) (do return (List []))))))

kl_shen_timer_macro :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_timer_macro (!kl_V803) = do !kl_if_0 <- kl_V803 `pseq` consP kl_V803
                                    !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V803 `pseq` hd kl_V803
                                                                 !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "time")) appl_2
                                                                 klIf kl_if_3 (do !appl_4 <- kl_V803 `pseq` tl kl_V803
                                                                                  !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                  klIf kl_if_5 (do let !appl_6 = List []
                                                                                                   !appl_7 <- kl_V803 `pseq` tl kl_V803
                                                                                                   !appl_8 <- appl_7 `pseq` tl appl_7
                                                                                                   appl_6 `pseq` (appl_8 `pseq` eq appl_6 appl_8)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                    klIf kl_if_1 (do let !appl_9 = List []
                                                     !appl_10 <- appl_9 `pseq` klCons (Types.Atom (Types.UnboundSym "run")) appl_9
                                                     !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_10
                                                     !appl_12 <- kl_V803 `pseq` tl kl_V803
                                                     !appl_13 <- appl_12 `pseq` hd appl_12
                                                     let !appl_14 = List []
                                                     !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.UnboundSym "run")) appl_14
                                                     !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_15
                                                     let !appl_17 = List []
                                                     !appl_18 <- appl_17 `pseq` klCons (Types.Atom (Types.UnboundSym "Start")) appl_17
                                                     !appl_19 <- appl_18 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_18
                                                     !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_19
                                                     let !appl_21 = List []
                                                     !appl_22 <- appl_21 `pseq` klCons (Types.Atom (Types.UnboundSym "Time")) appl_21
                                                     !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "str" str)) appl_22
                                                     let !appl_24 = List []
                                                     !appl_25 <- appl_24 `pseq` klCons (Types.Atom (Types.Str " secs\n")) appl_24
                                                     !appl_26 <- appl_23 `pseq` (appl_25 `pseq` klCons appl_23 appl_25)
                                                     !appl_27 <- appl_26 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_26
                                                     let !appl_28 = List []
                                                     !appl_29 <- appl_27 `pseq` (appl_28 `pseq` klCons appl_27 appl_28)
                                                     !appl_30 <- appl_29 `pseq` klCons (Types.Atom (Types.Str "\nrun time: ")) appl_29
                                                     !appl_31 <- appl_30 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_30
                                                     let !appl_32 = List []
                                                     !appl_33 <- appl_32 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_32
                                                     let !appl_34 = List []
                                                     !appl_35 <- appl_33 `pseq` (appl_34 `pseq` klCons appl_33 appl_34)
                                                     !appl_36 <- appl_31 `pseq` (appl_35 `pseq` klCons appl_31 appl_35)
                                                     !appl_37 <- appl_36 `pseq` klCons (ApplC (wrapNamed "shen.prhush" kl_shen_prhush)) appl_36
                                                     let !appl_38 = List []
                                                     !appl_39 <- appl_38 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_38
                                                     !appl_40 <- appl_37 `pseq` (appl_39 `pseq` klCons appl_37 appl_39)
                                                     !appl_41 <- appl_40 `pseq` klCons (Types.Atom (Types.UnboundSym "Message")) appl_40
                                                     !appl_42 <- appl_20 `pseq` (appl_41 `pseq` klCons appl_20 appl_41)
                                                     !appl_43 <- appl_42 `pseq` klCons (Types.Atom (Types.UnboundSym "Time")) appl_42
                                                     !appl_44 <- appl_16 `pseq` (appl_43 `pseq` klCons appl_16 appl_43)
                                                     !appl_45 <- appl_44 `pseq` klCons (Types.Atom (Types.UnboundSym "Finish")) appl_44
                                                     !appl_46 <- appl_13 `pseq` (appl_45 `pseq` klCons appl_13 appl_45)
                                                     !appl_47 <- appl_46 `pseq` klCons (Types.Atom (Types.UnboundSym "Result")) appl_46
                                                     !appl_48 <- appl_11 `pseq` (appl_47 `pseq` klCons appl_11 appl_47)
                                                     !appl_49 <- appl_48 `pseq` klCons (Types.Atom (Types.UnboundSym "Start")) appl_48
                                                     !appl_50 <- appl_49 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_49
                                                     appl_50 `pseq` kl_shen_let_macro appl_50) (do klIf (Atom (B True)) (do return kl_V803) (do return (List [])))

kl_shen_tuple_up :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_tuple_up (!kl_V804) = do !kl_if_0 <- kl_V804 `pseq` consP kl_V804
                                 klIf kl_if_0 (do !appl_1 <- kl_V804 `pseq` hd kl_V804
                                                  !appl_2 <- kl_V804 `pseq` tl kl_V804
                                                  !appl_3 <- appl_2 `pseq` kl_shen_tuple_up appl_2
                                                  let !appl_4 = List []
                                                  !appl_5 <- appl_3 `pseq` (appl_4 `pseq` klCons appl_3 appl_4)
                                                  !appl_6 <- appl_1 `pseq` (appl_5 `pseq` klCons appl_1 appl_5)
                                                  appl_6 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_6) (do klIf (Atom (B True)) (do return kl_V804) (do return (List [])))

kl_shen_putDivget_macro :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_putDivget_macro (!kl_V805) = do !kl_if_0 <- kl_V805 `pseq` consP kl_V805
                                        !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V805 `pseq` hd kl_V805
                                                                     !kl_if_3 <- appl_2 `pseq` eq (ApplC (wrapNamed "put" kl_put)) appl_2
                                                                     klIf kl_if_3 (do !appl_4 <- kl_V805 `pseq` tl kl_V805
                                                                                      !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                      klIf kl_if_5 (do !appl_6 <- kl_V805 `pseq` tl kl_V805
                                                                                                       !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                       !kl_if_8 <- appl_7 `pseq` consP appl_7
                                                                                                       klIf kl_if_8 (do !appl_9 <- kl_V805 `pseq` tl kl_V805
                                                                                                                        !appl_10 <- appl_9 `pseq` tl appl_9
                                                                                                                        !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                                                        !kl_if_12 <- appl_11 `pseq` consP appl_11
                                                                                                                        klIf kl_if_12 (do let !appl_13 = List []
                                                                                                                                          !appl_14 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                          !appl_15 <- appl_14 `pseq` tl appl_14
                                                                                                                                          !appl_16 <- appl_15 `pseq` tl appl_15
                                                                                                                                          !appl_17 <- appl_16 `pseq` tl appl_16
                                                                                                                                          appl_13 `pseq` (appl_17 `pseq` eq appl_13 appl_17)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                        klIf kl_if_1 (do !appl_18 <- kl_V805 `pseq` tl kl_V805
                                                         !appl_19 <- appl_18 `pseq` hd appl_18
                                                         !appl_20 <- kl_V805 `pseq` tl kl_V805
                                                         !appl_21 <- appl_20 `pseq` tl appl_20
                                                         !appl_22 <- appl_21 `pseq` hd appl_21
                                                         !appl_23 <- kl_V805 `pseq` tl kl_V805
                                                         !appl_24 <- appl_23 `pseq` tl appl_23
                                                         !appl_25 <- appl_24 `pseq` tl appl_24
                                                         !appl_26 <- appl_25 `pseq` hd appl_25
                                                         let !appl_27 = List []
                                                         !appl_28 <- appl_27 `pseq` klCons (Types.Atom (Types.UnboundSym "*property-vector*")) appl_27
                                                         !appl_29 <- appl_28 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_28
                                                         let !appl_30 = List []
                                                         !appl_31 <- appl_29 `pseq` (appl_30 `pseq` klCons appl_29 appl_30)
                                                         !appl_32 <- appl_26 `pseq` (appl_31 `pseq` klCons appl_26 appl_31)
                                                         !appl_33 <- appl_22 `pseq` (appl_32 `pseq` klCons appl_22 appl_32)
                                                         !appl_34 <- appl_19 `pseq` (appl_33 `pseq` klCons appl_19 appl_33)
                                                         appl_34 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_34) (do !kl_if_35 <- kl_V805 `pseq` consP kl_V805
                                                                                                                             !kl_if_36 <- klIf kl_if_35 (do !appl_37 <- kl_V805 `pseq` hd kl_V805
                                                                                                                                                            !kl_if_38 <- appl_37 `pseq` eq (ApplC (wrapNamed "get" kl_get)) appl_37
                                                                                                                                                            klIf kl_if_38 (do !appl_39 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                              !kl_if_40 <- appl_39 `pseq` consP appl_39
                                                                                                                                                                              klIf kl_if_40 (do !appl_41 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                !appl_42 <- appl_41 `pseq` tl appl_41
                                                                                                                                                                                                !kl_if_43 <- appl_42 `pseq` consP appl_42
                                                                                                                                                                                                klIf kl_if_43 (do let !appl_44 = List []
                                                                                                                                                                                                                  !appl_45 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                                  !appl_46 <- appl_45 `pseq` tl appl_45
                                                                                                                                                                                                                  !appl_47 <- appl_46 `pseq` tl appl_46
                                                                                                                                                                                                                  appl_44 `pseq` (appl_47 `pseq` eq appl_44 appl_47)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                             klIf kl_if_36 (do !appl_48 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                               !appl_49 <- appl_48 `pseq` hd appl_48
                                                                                                                                               !appl_50 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                               !appl_51 <- appl_50 `pseq` tl appl_50
                                                                                                                                               !appl_52 <- appl_51 `pseq` hd appl_51
                                                                                                                                               let !appl_53 = List []
                                                                                                                                               !appl_54 <- appl_53 `pseq` klCons (Types.Atom (Types.UnboundSym "*property-vector*")) appl_53
                                                                                                                                               !appl_55 <- appl_54 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_54
                                                                                                                                               let !appl_56 = List []
                                                                                                                                               !appl_57 <- appl_55 `pseq` (appl_56 `pseq` klCons appl_55 appl_56)
                                                                                                                                               !appl_58 <- appl_52 `pseq` (appl_57 `pseq` klCons appl_52 appl_57)
                                                                                                                                               !appl_59 <- appl_49 `pseq` (appl_58 `pseq` klCons appl_49 appl_58)
                                                                                                                                               appl_59 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_59) (do !kl_if_60 <- kl_V805 `pseq` consP kl_V805
                                                                                                                                                                                                                   !kl_if_61 <- klIf kl_if_60 (do !appl_62 <- kl_V805 `pseq` hd kl_V805
                                                                                                                                                                                                                                                  !kl_if_63 <- appl_62 `pseq` eq (ApplC (wrapNamed "unput" kl_unput)) appl_62
                                                                                                                                                                                                                                                  klIf kl_if_63 (do !appl_64 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                                                                                    !kl_if_65 <- appl_64 `pseq` consP appl_64
                                                                                                                                                                                                                                                                    klIf kl_if_65 (do !appl_66 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                                                                                                      !appl_67 <- appl_66 `pseq` tl appl_66
                                                                                                                                                                                                                                                                                      !kl_if_68 <- appl_67 `pseq` consP appl_67
                                                                                                                                                                                                                                                                                      klIf kl_if_68 (do let !appl_69 = List []
                                                                                                                                                                                                                                                                                                        !appl_70 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                                                                                                                        !appl_71 <- appl_70 `pseq` tl appl_70
                                                                                                                                                                                                                                                                                                        !appl_72 <- appl_71 `pseq` tl appl_71
                                                                                                                                                                                                                                                                                                        appl_69 `pseq` (appl_72 `pseq` eq appl_69 appl_72)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                                                                                                                                                   klIf kl_if_61 (do !appl_73 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                                                     !appl_74 <- appl_73 `pseq` hd appl_73
                                                                                                                                                                                                                                     !appl_75 <- kl_V805 `pseq` tl kl_V805
                                                                                                                                                                                                                                     !appl_76 <- appl_75 `pseq` tl appl_75
                                                                                                                                                                                                                                     !appl_77 <- appl_76 `pseq` hd appl_76
                                                                                                                                                                                                                                     let !appl_78 = List []
                                                                                                                                                                                                                                     !appl_79 <- appl_78 `pseq` klCons (Types.Atom (Types.UnboundSym "*property-vector*")) appl_78
                                                                                                                                                                                                                                     !appl_80 <- appl_79 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_79
                                                                                                                                                                                                                                     let !appl_81 = List []
                                                                                                                                                                                                                                     !appl_82 <- appl_80 `pseq` (appl_81 `pseq` klCons appl_80 appl_81)
                                                                                                                                                                                                                                     !appl_83 <- appl_77 `pseq` (appl_82 `pseq` klCons appl_77 appl_82)
                                                                                                                                                                                                                                     !appl_84 <- appl_74 `pseq` (appl_83 `pseq` klCons appl_74 appl_83)
                                                                                                                                                                                                                                     appl_84 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_84) (do klIf (Atom (B True)) (do return kl_V805) (do return (List [])))))

kl_shen_function_macro :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_function_macro (!kl_V806) = do !kl_if_0 <- kl_V806 `pseq` consP kl_V806
                                       !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V806 `pseq` hd kl_V806
                                                                    !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "function")) appl_2
                                                                    klIf kl_if_3 (do !appl_4 <- kl_V806 `pseq` tl kl_V806
                                                                                     !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                     klIf kl_if_5 (do let !appl_6 = List []
                                                                                                      !appl_7 <- kl_V806 `pseq` tl kl_V806
                                                                                                      !appl_8 <- appl_7 `pseq` tl appl_7
                                                                                                      appl_6 `pseq` (appl_8 `pseq` eq appl_6 appl_8)) (do return (Atom (B False)))) (do return (Atom (B False)))) (do return (Atom (B False)))
                                       klIf kl_if_1 (do !appl_9 <- kl_V806 `pseq` tl kl_V806
                                                        !appl_10 <- appl_9 `pseq` hd appl_9
                                                        !appl_11 <- kl_V806 `pseq` tl kl_V806
                                                        !appl_12 <- appl_11 `pseq` hd appl_11
                                                        let !aw_13 = Types.Atom (Types.UnboundSym "arity")
                                                        !appl_14 <- appl_12 `pseq` applyWrapper aw_13 [appl_12]
                                                        appl_10 `pseq` (appl_14 `pseq` kl_shen_function_abstraction appl_10 appl_14)) (do klIf (Atom (B True)) (do return kl_V806) (do return (List [])))

kl_shen_function_abstraction :: Types.KLValue ->
                                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_function_abstraction (!kl_V807) (!kl_V808) = do !kl_if_0 <- kl_V808 `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_V808
                                                        klIf kl_if_0 (do return kl_V807) (do !kl_if_1 <- kl_V808 `pseq` eq (Types.Atom (Types.N (Types.KI (-1)))) kl_V808
                                                                                             klIf kl_if_1 (do let !appl_2 = List []
                                                                                                              kl_V807 `pseq` (appl_2 `pseq` kl_shen_function_abstraction_help kl_V807 (Types.Atom (Types.N (Types.KI 1))) appl_2)) (do klIf (Atom (B True)) (do let !appl_3 = List []
                                                                                                                                                                                                                                                                kl_V807 `pseq` (kl_V808 `pseq` (appl_3 `pseq` kl_shen_function_abstraction_help kl_V807 kl_V808 appl_3))) (do return (List []))))

kl_shen_function_abstraction_help :: Types.KLValue ->
                                     Types.KLValue ->
                                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_function_abstraction_help (!kl_V809) (!kl_V810) (!kl_V811) = do !kl_if_0 <- kl_V810 `pseq` eq (Types.Atom (Types.N (Types.KI 0))) kl_V810
                                                                        klIf kl_if_0 (do kl_V809 `pseq` (kl_V811 `pseq` klCons kl_V809 kl_V811)) (do klIf (Atom (B True)) (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_2 <- kl_V810 `pseq` Primitives.subtract kl_V810 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                          let !appl_3 = List []
                                                                                                                                                                                                                                          !appl_4 <- kl_X `pseq` (appl_3 `pseq` klCons kl_X appl_3)
                                                                                                                                                                                                                                          !appl_5 <- kl_V811 `pseq` (appl_4 `pseq` kl_append kl_V811 appl_4)
                                                                                                                                                                                                                                          !appl_6 <- kl_V809 `pseq` (appl_2 `pseq` (appl_5 `pseq` kl_shen_function_abstraction_help kl_V809 appl_2 appl_5))
                                                                                                                                                                                                                                          let !appl_7 = List []
                                                                                                                                                                                                                                          !appl_8 <- appl_6 `pseq` (appl_7 `pseq` klCons appl_6 appl_7)
                                                                                                                                                                                                                                          !appl_9 <- kl_X `pseq` (appl_8 `pseq` klCons kl_X appl_8)
                                                                                                                                                                                                                                          appl_9 `pseq` klCons (Types.Atom (Types.UnboundSym "/.")) appl_9)))
                                                                                                                                                                              !appl_10 <- kl_gensym (Types.Atom (Types.UnboundSym "V"))
                                                                                                                                                                              appl_10 `pseq` applyWrapper appl_1 [appl_10]) (do return (List [])))

kl_undefmacro :: Types.KLValue ->
                 Types.KLContext Types.Env Types.KLValue
kl_undefmacro (!kl_V812) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_MacroReg) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Pos) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Remove1) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Remove2) -> do return kl_V812)))
                                                                                                                                                                                                                                 !appl_4 <- value (Types.Atom (Types.UnboundSym "*macros*"))
                                                                                                                                                                                                                                 !appl_5 <- kl_Pos `pseq` (appl_4 `pseq` kl_shen_remove_nth kl_Pos appl_4)
                                                                                                                                                                                                                                 !appl_6 <- appl_5 `pseq` klSet (Types.Atom (Types.UnboundSym "*macros*")) appl_5
                                                                                                                                                                                                                                 appl_6 `pseq` applyWrapper appl_3 [appl_6])))
                                                                                                                                                               !appl_7 <- kl_V812 `pseq` (kl_MacroReg `pseq` kl_remove kl_V812 kl_MacroReg)
                                                                                                                                                               !appl_8 <- appl_7 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*macroreg*")) appl_7
                                                                                                                                                               appl_8 `pseq` applyWrapper appl_2 [appl_8])))
                                                                                                 !appl_9 <- kl_V812 `pseq` (kl_MacroReg `pseq` kl_shen_findpos kl_V812 kl_MacroReg)
                                                                                                 appl_9 `pseq` applyWrapper appl_1 [appl_9])))
                              !appl_10 <- value (Types.Atom (Types.UnboundSym "shen.*macroreg*"))
                              appl_10 `pseq` applyWrapper appl_0 [appl_10]

kl_shen_findpos :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_findpos (!kl_V820) (!kl_V821) = do let !appl_0 = List []
                                           !kl_if_1 <- appl_0 `pseq` (kl_V821 `pseq` eq appl_0 kl_V821)
                                           klIf kl_if_1 (do !appl_2 <- kl_V820 `pseq` kl_shen_app kl_V820 (Types.Atom (Types.Str " is not a macro\n")) (Types.Atom (Types.UnboundSym "shen.a"))
                                                            appl_2 `pseq` simpleError appl_2) (do !kl_if_3 <- kl_V821 `pseq` consP kl_V821
                                                                                                  !kl_if_4 <- klIf kl_if_3 (do !appl_5 <- kl_V821 `pseq` hd kl_V821
                                                                                                                               appl_5 `pseq` (kl_V820 `pseq` eq appl_5 kl_V820)) (do return (Atom (B False)))
                                                                                                  klIf kl_if_4 (do return (Types.Atom (Types.N (Types.KI 1)))) (do !kl_if_6 <- kl_V821 `pseq` consP kl_V821
                                                                                                                                                                   klIf kl_if_6 (do !appl_7 <- kl_V821 `pseq` tl kl_V821
                                                                                                                                                                                    !appl_8 <- kl_V820 `pseq` (appl_7 `pseq` kl_shen_findpos kl_V820 appl_7)
                                                                                                                                                                                    appl_8 `pseq` add (Types.Atom (Types.N (Types.KI 1))) appl_8) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.findpos" kl_shen_findpos))) (do return (List [])))))

kl_shen_remove_nth :: Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_remove_nth (!kl_V824) (!kl_V825) = do !kl_if_0 <- kl_V824 `pseq` eq (Types.Atom (Types.N (Types.KI 1))) kl_V824
                                              !kl_if_1 <- klIf kl_if_0 (do kl_V825 `pseq` consP kl_V825) (do return (Atom (B False)))
                                              klIf kl_if_1 (do kl_V825 `pseq` tl kl_V825) (do !kl_if_2 <- kl_V825 `pseq` consP kl_V825
                                                                                              klIf kl_if_2 (do !appl_3 <- kl_V825 `pseq` hd kl_V825
                                                                                                               !appl_4 <- kl_V824 `pseq` Primitives.subtract kl_V824 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                               !appl_5 <- kl_V825 `pseq` tl kl_V825
                                                                                                               !appl_6 <- appl_4 `pseq` (appl_5 `pseq` kl_shen_remove_nth appl_4 appl_5)
                                                                                                               appl_3 `pseq` (appl_6 `pseq` klCons appl_3 appl_6)) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.remove-nth" kl_shen_remove_nth))) (do return (List []))))

expr10 :: Types.KLContext Types.Env Types.KLValue
expr10 = do (return $ List [])
