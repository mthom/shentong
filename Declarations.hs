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

module Declarations where

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
import Macros

kl_shen_initialise_arity_table :: Types.KLValue ->
                                  Types.KLContext Types.Env Types.KLValue
kl_shen_initialise_arity_table (!kl_V726) = do let !appl_0 = List []
                                               !kl_if_1 <- appl_0 `pseq` (kl_V726 `pseq` eq appl_0 kl_V726)
                                               klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V726 `pseq` consP kl_V726
                                                                                      !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V726 `pseq` tl kl_V726
                                                                                                                   appl_4 `pseq` consP appl_4) (do return (Atom (B False)))
                                                                                      klIf kl_if_3 (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_DecArity) -> do !appl_6 <- kl_V726 `pseq` tl kl_V726
                                                                                                                                                                          !appl_7 <- appl_6 `pseq` tl appl_6
                                                                                                                                                                          appl_7 `pseq` kl_shen_initialise_arity_table appl_7)))
                                                                                                       !appl_8 <- kl_V726 `pseq` hd kl_V726
                                                                                                       !appl_9 <- kl_V726 `pseq` tl kl_V726
                                                                                                       !appl_10 <- appl_9 `pseq` hd appl_9
                                                                                                       !appl_11 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                                                                                       !appl_12 <- appl_8 `pseq` (appl_10 `pseq` (appl_11 `pseq` kl_put appl_8 (ApplC (wrapNamed "arity" kl_arity)) appl_10 appl_11))
                                                                                                       appl_12 `pseq` applyWrapper appl_5 [appl_12]) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.initialise_arity_table" kl_shen_initialise_arity_table))) (do return (List []))))

kl_arity :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_arity (!kl_V727) = do (do !appl_0 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                             kl_V727 `pseq` (appl_0 `pseq` kl_get kl_V727 (ApplC (wrapNamed "arity" kl_arity)) appl_0)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.N (Types.KI (-1)))))

kl_systemf :: Types.KLValue ->
              Types.KLContext Types.Env Types.KLValue
kl_systemf (!kl_V728) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Shen) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_External) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Place) -> do return kl_V728)))
                                                                                                                                                             !appl_3 <- kl_V728 `pseq` (kl_External `pseq` kl_adjoin kl_V728 kl_External)
                                                                                                                                                             !appl_4 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                                                                                                                                             !appl_5 <- kl_Shen `pseq` (appl_3 `pseq` (appl_4 `pseq` kl_put kl_Shen (Types.Atom (Types.UnboundSym "shen.external-symbols")) appl_3 appl_4))
                                                                                                                                                             appl_5 `pseq` applyWrapper appl_2 [appl_5])))
                                                                                          !appl_6 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                                                                                          !appl_7 <- kl_Shen `pseq` (appl_6 `pseq` kl_get kl_Shen (Types.Atom (Types.UnboundSym "shen.external-symbols")) appl_6)
                                                                                          appl_7 `pseq` applyWrapper appl_1 [appl_7])))
                           !appl_8 <- intern (Types.Atom (Types.Str "shen"))
                           appl_8 `pseq` applyWrapper appl_0 [appl_8]

kl_adjoin :: Types.KLValue ->
             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_adjoin (!kl_V729) (!kl_V730) = do !kl_if_0 <- kl_V729 `pseq` (kl_V730 `pseq` kl_elementP kl_V729 kl_V730)
                                     klIf kl_if_0 (do return kl_V730) (do kl_V729 `pseq` (kl_V730 `pseq` klCons kl_V729 kl_V730))

kl_specialise :: Types.KLValue ->
                 Types.KLContext Types.Env Types.KLValue
kl_specialise (!kl_V731) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*special*"))
                              !appl_1 <- kl_V731 `pseq` (appl_0 `pseq` klCons kl_V731 appl_0)
                              !appl_2 <- appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*special*")) appl_1
                              appl_2 `pseq` (kl_V731 `pseq` kl_do appl_2 kl_V731)

kl_unspecialise :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_unspecialise (!kl_V732) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*special*"))
                                !appl_1 <- kl_V732 `pseq` (appl_0 `pseq` kl_remove kl_V732 appl_0)
                                !appl_2 <- appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*special*")) appl_1
                                appl_2 `pseq` (kl_V732 `pseq` kl_do appl_2 kl_V732)

expr11 :: Types.KLContext Types.Env Types.KLValue
expr11 = do (do klSet (Types.Atom (Types.UnboundSym "shen.*installing-kl*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_0 = List []
                appl_0 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*history*")) appl_0) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*tc*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_1 <- kl_vector (Types.Atom (Types.N (Types.KI 20000)))
                appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "*property-vector*")) appl_1) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*process-counter*")) (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_2 <- kl_vector (Types.Atom (Types.N (Types.KI 1000)))
                appl_2 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*varcounter*")) appl_2) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_3 <- kl_vector (Types.Atom (Types.N (Types.KI 1000)))
                appl_3 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*prologvectors*")) appl_3) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_4 = List []
                !appl_5 <- appl_4 `pseq` klCons (ApplC (wrapNamed "shen.function-macro" kl_shen_function_macro)) appl_4
                !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "shen.defprolog-macro" kl_shen_defprolog_macro)) appl_5
                !appl_7 <- appl_6 `pseq` klCons (ApplC (wrapNamed "shen.@s-macro" kl_shen_Ats_macro)) appl_6
                !appl_8 <- appl_7 `pseq` klCons (ApplC (wrapNamed "shen.nl-macro" kl_shen_nl_macro)) appl_7
                !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "shen.synonyms-macro" kl_shen_synonyms_macro)) appl_8
                !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "shen.prolog-macro" kl_shen_prolog_macro)) appl_9
                !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "shen.error-macro" kl_shen_error_macro)) appl_10
                !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "shen.input-macro" kl_shen_input_macro)) appl_11
                !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "shen.output-macro" kl_shen_output_macro)) appl_12
                !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "shen.make-string-macro" kl_shen_make_string_macro)) appl_13
                !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "shen.assoc-macro" kl_shen_assoc_macro)) appl_14
                !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "shen.let-macro" kl_shen_let_macro)) appl_15
                !appl_17 <- appl_16 `pseq` klCons (ApplC (wrapNamed "shen.datatype-macro" kl_shen_datatype_macro)) appl_16
                !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "shen.compile-macro" kl_shen_compile_macro)) appl_17
                !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "shen.put/get-macro" kl_shen_putDivget_macro)) appl_18
                !appl_20 <- appl_19 `pseq` klCons (ApplC (wrapNamed "shen.abs-macro" kl_shen_abs_macro)) appl_19
                !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "shen.cases-macro" kl_shen_cases_macro)) appl_20
                !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "shen.timer-macro" kl_shen_timer_macro)) appl_21
                appl_22 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*macroreg*")) appl_22) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_23 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_timer_macro kl_X)))
                let !appl_24 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_cases_macro kl_X)))
                let !appl_25 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_abs_macro kl_X)))
                let !appl_26 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_putDivget_macro kl_X)))
                let !appl_27 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_compile_macro kl_X)))
                let !appl_28 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_datatype_macro kl_X)))
                let !appl_29 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_let_macro kl_X)))
                let !appl_30 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_assoc_macro kl_X)))
                let !appl_31 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_make_string_macro kl_X)))
                let !appl_32 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_output_macro kl_X)))
                let !appl_33 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_input_macro kl_X)))
                let !appl_34 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_error_macro kl_X)))
                let !appl_35 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_prolog_macro kl_X)))
                let !appl_36 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_synonyms_macro kl_X)))
                let !appl_37 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_nl_macro kl_X)))
                let !appl_38 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_Ats_macro kl_X)))
                let !appl_39 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_defprolog_macro kl_X)))
                let !appl_40 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_function_macro kl_X)))
                let !appl_41 = List []
                !appl_42 <- appl_40 `pseq` (appl_41 `pseq` klCons appl_40 appl_41)
                !appl_43 <- appl_39 `pseq` (appl_42 `pseq` klCons appl_39 appl_42)
                !appl_44 <- appl_38 `pseq` (appl_43 `pseq` klCons appl_38 appl_43)
                !appl_45 <- appl_37 `pseq` (appl_44 `pseq` klCons appl_37 appl_44)
                !appl_46 <- appl_36 `pseq` (appl_45 `pseq` klCons appl_36 appl_45)
                !appl_47 <- appl_35 `pseq` (appl_46 `pseq` klCons appl_35 appl_46)
                !appl_48 <- appl_34 `pseq` (appl_47 `pseq` klCons appl_34 appl_47)
                !appl_49 <- appl_33 `pseq` (appl_48 `pseq` klCons appl_33 appl_48)
                !appl_50 <- appl_32 `pseq` (appl_49 `pseq` klCons appl_32 appl_49)
                !appl_51 <- appl_31 `pseq` (appl_50 `pseq` klCons appl_31 appl_50)
                !appl_52 <- appl_30 `pseq` (appl_51 `pseq` klCons appl_30 appl_51)
                !appl_53 <- appl_29 `pseq` (appl_52 `pseq` klCons appl_29 appl_52)
                !appl_54 <- appl_28 `pseq` (appl_53 `pseq` klCons appl_28 appl_53)
                !appl_55 <- appl_27 `pseq` (appl_54 `pseq` klCons appl_27 appl_54)
                !appl_56 <- appl_26 `pseq` (appl_55 `pseq` klCons appl_26 appl_55)
                !appl_57 <- appl_25 `pseq` (appl_56 `pseq` klCons appl_25 appl_56)
                !appl_58 <- appl_24 `pseq` (appl_57 `pseq` klCons appl_24 appl_57)
                !appl_59 <- appl_23 `pseq` (appl_58 `pseq` klCons appl_23 appl_58)
                appl_59 `pseq` klSet (Types.Atom (Types.UnboundSym "*macros*")) appl_59) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_60 = List []
                appl_60 `pseq` klSet (Types.Atom (Types.UnboundSym "*home-directory*")) appl_60) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*gensym*")) (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_61 = List []
                appl_61 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*tracking*")) appl_61) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*home-directory*")) (Types.Atom (Types.Str ""))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_62 = List []
                !appl_63 <- appl_62 `pseq` klCons (Types.Atom (Types.UnboundSym "Z")) appl_62
                !appl_64 <- appl_63 `pseq` klCons (Types.Atom (Types.UnboundSym "Y")) appl_63
                !appl_65 <- appl_64 `pseq` klCons (Types.Atom (Types.UnboundSym "X")) appl_64
                !appl_66 <- appl_65 `pseq` klCons (Types.Atom (Types.UnboundSym "W")) appl_65
                !appl_67 <- appl_66 `pseq` klCons (Types.Atom (Types.UnboundSym "V")) appl_66
                !appl_68 <- appl_67 `pseq` klCons (Types.Atom (Types.UnboundSym "U")) appl_67
                !appl_69 <- appl_68 `pseq` klCons (Types.Atom (Types.UnboundSym "T")) appl_68
                !appl_70 <- appl_69 `pseq` klCons (Types.Atom (Types.UnboundSym "S")) appl_69
                !appl_71 <- appl_70 `pseq` klCons (Types.Atom (Types.UnboundSym "R")) appl_70
                !appl_72 <- appl_71 `pseq` klCons (Types.Atom (Types.UnboundSym "Q")) appl_71
                !appl_73 <- appl_72 `pseq` klCons (Types.Atom (Types.UnboundSym "P")) appl_72
                !appl_74 <- appl_73 `pseq` klCons (Types.Atom (Types.UnboundSym "O")) appl_73
                !appl_75 <- appl_74 `pseq` klCons (Types.Atom (Types.UnboundSym "N")) appl_74
                !appl_76 <- appl_75 `pseq` klCons (Types.Atom (Types.UnboundSym "M")) appl_75
                !appl_77 <- appl_76 `pseq` klCons (Types.Atom (Types.UnboundSym "L")) appl_76
                !appl_78 <- appl_77 `pseq` klCons (Types.Atom (Types.UnboundSym "K")) appl_77
                !appl_79 <- appl_78 `pseq` klCons (Types.Atom (Types.UnboundSym "J")) appl_78
                !appl_80 <- appl_79 `pseq` klCons (Types.Atom (Types.UnboundSym "I")) appl_79
                !appl_81 <- appl_80 `pseq` klCons (Types.Atom (Types.UnboundSym "H")) appl_80
                !appl_82 <- appl_81 `pseq` klCons (Types.Atom (Types.UnboundSym "G")) appl_81
                !appl_83 <- appl_82 `pseq` klCons (Types.Atom (Types.UnboundSym "F")) appl_82
                !appl_84 <- appl_83 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_83
                !appl_85 <- appl_84 `pseq` klCons (Types.Atom (Types.UnboundSym "D")) appl_84
                !appl_86 <- appl_85 `pseq` klCons (Types.Atom (Types.UnboundSym "C")) appl_85
                !appl_87 <- appl_86 `pseq` klCons (Types.Atom (Types.UnboundSym "B")) appl_86
                !appl_88 <- appl_87 `pseq` klCons (Types.Atom (Types.UnboundSym "A")) appl_87
                appl_88 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*alphabet*")) appl_88) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_89 = List []
                !appl_90 <- appl_89 `pseq` klCons (ApplC (wrapNamed "open" openStream)) appl_89
                !appl_91 <- appl_90 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_90
                !appl_92 <- appl_91 `pseq` klCons (Types.Atom (Types.UnboundSym "where")) appl_91
                !appl_93 <- appl_92 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_92
                !appl_94 <- appl_93 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_93
                !appl_95 <- appl_94 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_94
                !appl_96 <- appl_95 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_95
                !appl_97 <- appl_96 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_96
                !appl_98 <- appl_97 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_97
                appl_98 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*special*")) appl_98) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_99 = List []
                !appl_100 <- appl_99 `pseq` klCons (Types.Atom (Types.UnboundSym "defmacro")) appl_99
                !appl_101 <- appl_100 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.read+")) appl_100
                !appl_102 <- appl_101 `pseq` klCons (Types.Atom (Types.UnboundSym "defcc")) appl_101
                !appl_103 <- appl_102 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_102
                !appl_104 <- appl_103 `pseq` klCons (ApplC (wrapNamed "shen.process-datatype" kl_shen_process_datatype)) appl_103
                !appl_105 <- appl_104 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_104
                appl_105 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*extraspecial*")) appl_105) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*spy*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_106 = List []
                appl_106 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*datatypes*")) appl_106) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_107 = List []
                appl_107 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*alldatatypes*")) appl_107) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*shen-type-theory-enabled?*")) (Atom (B True))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_108 = List []
                appl_108 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*synonyms*")) appl_108) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_109 = List []
                appl_109 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*system*")) appl_109) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_110 = List []
                appl_110 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*signedfuncs*")) appl_110) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*maxcomplexity*")) (Types.Atom (Types.N (Types.KI 128)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*occurs*")) (Atom (B True))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*maxinferences*")) (Types.Atom (Types.N (Types.KI 1000000)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*maximum-print-sequence-size*")) (Types.Atom (Types.N (Types.KI 20)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*catch*")) (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*call*")) (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*infs*")) (Types.Atom (Types.N (Types.KI 0)))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*hush*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "shen.*optimise*")) (Atom (B False))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do klSet (Types.Atom (Types.UnboundSym "*version*")) (Types.Atom (Types.Str "Shen 17.3"))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do let !appl_111 = List []
                !appl_112 <- appl_111 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_111
                !appl_113 <- appl_112 `pseq` klCons (Types.Atom (Types.UnboundSym "where")) appl_112
                !appl_114 <- appl_113 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_113
                !appl_115 <- appl_114 `pseq` klCons (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_114
                !appl_116 <- appl_115 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_115
                !appl_117 <- appl_116 `pseq` klCons (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_116
                !appl_118 <- appl_117 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_117
                !appl_119 <- appl_118 `pseq` klCons (ApplC (wrapNamed "include" kl_include)) appl_118
                !appl_120 <- appl_119 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_119
                !appl_121 <- appl_120 `pseq` klCons (ApplC (wrapNamed "preclude" kl_preclude)) appl_120
                !appl_122 <- appl_121 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_121
                !appl_123 <- appl_122 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_122
                !appl_124 <- appl_123 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_123
                !appl_125 <- appl_124 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_124
                !appl_126 <- appl_125 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_125
                !appl_127 <- appl_126 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_126
                !appl_128 <- appl_127 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_127
                !appl_129 <- appl_128 `pseq` klCons (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_128
                !appl_130 <- appl_129 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_129
                !appl_131 <- appl_130 `pseq` klCons (ApplC (wrapNamed "==" kl_EqEq)) appl_130
                !appl_132 <- appl_131 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_131
                !appl_133 <- appl_132 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_132
                !appl_134 <- appl_133 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_133
                !appl_135 <- appl_134 `pseq` klCons (ApplC (wrapNamed "/" divide)) appl_134
                !appl_136 <- appl_135 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_135
                !appl_137 <- appl_136 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_136
                !appl_138 <- appl_137 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_137
                !appl_139 <- appl_138 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_138
                !appl_140 <- appl_139 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_139
                !appl_141 <- appl_140 `pseq` klCons (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_140
                !appl_142 <- appl_141 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_141
                !appl_143 <- appl_142 `pseq` klCons (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_142
                !appl_144 <- appl_143 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_143
                !appl_145 <- appl_144 `pseq` klCons (ApplC (wrapNamed "write-byte" writeByte)) appl_144
                !appl_146 <- appl_145 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_145
                !appl_147 <- appl_146 `pseq` klCons (ApplC (PL "version" kl_version)) appl_146
                !appl_148 <- appl_147 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_147
                !appl_149 <- appl_148 `pseq` klCons (ApplC (wrapNamed "variable?" kl_variableP)) appl_148
                !appl_150 <- appl_149 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_149
                !appl_151 <- appl_150 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_150
                !appl_152 <- appl_151 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_151
                !appl_153 <- appl_152 `pseq` klCons (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_152
                !appl_154 <- appl_153 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_153
                !appl_155 <- appl_154 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_154
                !appl_156 <- appl_155 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_155
                !appl_157 <- appl_156 `pseq` klCons (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_156
                !appl_158 <- appl_157 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_157
                !appl_159 <- appl_158 `pseq` klCons (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_158
                !appl_160 <- appl_159 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_159
                !appl_161 <- appl_160 `pseq` klCons (ApplC (wrapNamed "untrack" kl_untrack)) appl_160
                !appl_162 <- appl_161 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_161
                !appl_163 <- appl_162 `pseq` klCons (ApplC (wrapNamed "union" kl_union)) appl_162
                !appl_164 <- appl_163 `pseq` klCons (Types.Atom (Types.N (Types.KI 4))) appl_163
                !appl_165 <- appl_164 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_164
                !appl_166 <- appl_165 `pseq` klCons (Types.Atom (Types.N (Types.KI 4))) appl_165
                !appl_167 <- appl_166 `pseq` klCons (ApplC (wrapNamed "unify" kl_unify)) appl_166
                !appl_168 <- appl_167 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_167
                !appl_169 <- appl_168 `pseq` klCons (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_168
                !appl_170 <- appl_169 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_169
                !appl_171 <- appl_170 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_170
                !appl_172 <- appl_171 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_171
                !appl_173 <- appl_172 `pseq` klCons (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_172
                !appl_174 <- appl_173 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_173
                !appl_175 <- appl_174 `pseq` klCons (ApplC (wrapNamed "return" kl_return)) appl_174
                !appl_176 <- appl_175 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_175
                !appl_177 <- appl_176 `pseq` klCons (ApplC (wrapNamed "type" typeA)) appl_176
                !appl_178 <- appl_177 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_177
                !appl_179 <- appl_178 `pseq` klCons (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_178
                !appl_180 <- appl_179 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_179
                !appl_181 <- appl_180 `pseq` klCons (Types.Atom (Types.UnboundSym "trap-error")) appl_180
                !appl_182 <- appl_181 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_181
                !appl_183 <- appl_182 `pseq` klCons (ApplC (wrapNamed "track" kl_track)) appl_182
                !appl_184 <- appl_183 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_183
                !appl_185 <- appl_184 `pseq` klCons (ApplC (wrapNamed "tlstr" tlstr)) appl_184
                !appl_186 <- appl_185 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_185
                !appl_187 <- appl_186 `pseq` klCons (ApplC (wrapNamed "thaw" kl_thaw)) appl_186
                !appl_188 <- appl_187 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_187
                !appl_189 <- appl_188 `pseq` klCons (ApplC (PL "tc?" kl_tcP)) appl_188
                !appl_190 <- appl_189 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_189
                !appl_191 <- appl_190 `pseq` klCons (ApplC (wrapNamed "tc" kl_tc)) appl_190
                !appl_192 <- appl_191 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_191
                !appl_193 <- appl_192 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_192
                !appl_194 <- appl_193 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_193
                !appl_195 <- appl_194 `pseq` klCons (ApplC (wrapNamed "tail" kl_tail)) appl_194
                !appl_196 <- appl_195 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_195
                !appl_197 <- appl_196 `pseq` klCons (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_196
                !appl_198 <- appl_197 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_197
                !appl_199 <- appl_198 `pseq` klCons (ApplC (wrapNamed "sum" kl_sum)) appl_198
                !appl_200 <- appl_199 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_199
                !appl_201 <- appl_200 `pseq` klCons (ApplC (wrapNamed "subst" kl_subst)) appl_200
                !appl_202 <- appl_201 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_201
                !appl_203 <- appl_202 `pseq` klCons (ApplC (wrapNamed "string?" stringP)) appl_202
                !appl_204 <- appl_203 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_203
                !appl_205 <- appl_204 `pseq` klCons (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_204
                !appl_206 <- appl_205 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_205
                !appl_207 <- appl_206 `pseq` klCons (ApplC (wrapNamed "string->n" stringToN)) appl_206
                !appl_208 <- appl_207 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_207
                !appl_209 <- appl_208 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_208
                !appl_210 <- appl_209 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_209
                !appl_211 <- appl_210 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_210
                !appl_212 <- appl_211 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_211
                !appl_213 <- appl_212 `pseq` klCons (ApplC (wrapNamed "step" kl_step)) appl_212
                !appl_214 <- appl_213 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_213
                !appl_215 <- appl_214 `pseq` klCons (ApplC (wrapNamed "spy" kl_spy)) appl_214
                !appl_216 <- appl_215 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_215
                !appl_217 <- appl_216 `pseq` klCons (ApplC (wrapNamed "specialise" kl_specialise)) appl_216
                !appl_218 <- appl_217 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_217
                !appl_219 <- appl_218 `pseq` klCons (ApplC (wrapNamed "snd" kl_snd)) appl_218
                !appl_220 <- appl_219 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_219
                !appl_221 <- appl_220 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_220
                !appl_222 <- appl_221 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_221
                !appl_223 <- appl_222 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_222
                !appl_224 <- appl_223 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_223
                !appl_225 <- appl_224 `pseq` klCons (ApplC (wrapNamed "reverse" kl_reverse)) appl_224
                !appl_226 <- appl_225 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_225
                !appl_227 <- appl_226 `pseq` klCons (Types.Atom (Types.UnboundSym "require")) appl_226
                !appl_228 <- appl_227 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_227
                !appl_229 <- appl_228 `pseq` klCons (ApplC (wrapNamed "remove" kl_remove)) appl_228
                !appl_230 <- appl_229 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_229
                !appl_231 <- appl_230 `pseq` klCons (ApplC (PL "release" kl_release)) appl_230
                !appl_232 <- appl_231 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_231
                !appl_233 <- appl_232 `pseq` klCons (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_232
                !appl_234 <- appl_233 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_233
                !appl_235 <- appl_234 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_234
                !appl_236 <- appl_235 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_235
                !appl_237 <- appl_236 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_236
                !appl_238 <- appl_237 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_237
                !appl_239 <- appl_238 `pseq` klCons (ApplC (wrapNamed "read-file" kl_read_file)) appl_238
                !appl_240 <- appl_239 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_239
                !appl_241 <- appl_240 `pseq` klCons (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_240
                !appl_242 <- appl_241 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_241
                !appl_243 <- appl_242 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.reassemble")) appl_242
                !appl_244 <- appl_243 `pseq` klCons (Types.Atom (Types.N (Types.KI 4))) appl_243
                !appl_245 <- appl_244 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_244
                !appl_246 <- appl_245 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_245
                !appl_247 <- appl_246 `pseq` klCons (ApplC (wrapNamed "address->" addressTo)) appl_246
                !appl_248 <- appl_247 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_247
                !appl_249 <- appl_248 `pseq` klCons (ApplC (wrapNamed "protect" kl_protect)) appl_248
                !appl_250 <- appl_249 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_249
                !appl_251 <- appl_250 `pseq` klCons (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_250
                !appl_252 <- appl_251 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_251
                !appl_253 <- appl_252 `pseq` klCons (ApplC (wrapNamed "preclude" kl_preclude)) appl_252
                !appl_254 <- appl_253 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_253
                !appl_255 <- appl_254 `pseq` klCons (ApplC (wrapNamed "ps" kl_ps)) appl_254
                !appl_256 <- appl_255 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_255
                !appl_257 <- appl_256 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_256
                !appl_258 <- appl_257 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_257
                !appl_259 <- appl_258 `pseq` klCons (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_258
                !appl_260 <- appl_259 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_259
                !appl_261 <- appl_260 `pseq` klCons (ApplC (wrapNamed "profile" kl_profile)) appl_260
                !appl_262 <- appl_261 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_261
                !appl_263 <- appl_262 `pseq` klCons (ApplC (wrapNamed "print" kl_print)) appl_262
                !appl_264 <- appl_263 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_263
                !appl_265 <- appl_264 `pseq` klCons (ApplC (wrapNamed "pos" pos)) appl_264
                !appl_266 <- appl_265 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_265
                !appl_267 <- appl_266 `pseq` klCons (ApplC (PL "porters" kl_porters)) appl_266
                !appl_268 <- appl_267 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_267
                !appl_269 <- appl_268 `pseq` klCons (ApplC (PL "port" kl_port)) appl_268
                !appl_270 <- appl_269 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_269
                !appl_271 <- appl_270 `pseq` klCons (ApplC (wrapNamed "package?" kl_packageP)) appl_270
                !appl_272 <- appl_271 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_271
                !appl_273 <- appl_272 `pseq` klCons (Types.Atom (Types.UnboundSym "package")) appl_272
                !appl_274 <- appl_273 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_273
                !appl_275 <- appl_274 `pseq` klCons (ApplC (PL "os" kl_os)) appl_274
                !appl_276 <- appl_275 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_275
                !appl_277 <- appl_276 `pseq` klCons (Types.Atom (Types.UnboundSym "or")) appl_276
                !appl_278 <- appl_277 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_277
                !appl_279 <- appl_278 `pseq` klCons (ApplC (wrapNamed "optimise" kl_optimise)) appl_278
                !appl_280 <- appl_279 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_279
                !appl_281 <- appl_280 `pseq` klCons (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_280
                !appl_282 <- appl_281 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_281
                !appl_283 <- appl_282 `pseq` klCons (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_282
                !appl_284 <- appl_283 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_283
                !appl_285 <- appl_284 `pseq` klCons (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_284
                !appl_286 <- appl_285 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_285
                !appl_287 <- appl_286 `pseq` klCons (ApplC (wrapNamed "number?" numberP)) appl_286
                !appl_288 <- appl_287 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_287
                !appl_289 <- appl_288 `pseq` klCons (ApplC (wrapNamed "n->string" nToString)) appl_288
                !appl_290 <- appl_289 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_289
                !appl_291 <- appl_290 `pseq` klCons (ApplC (wrapNamed "nth" kl_nth)) appl_290
                !appl_292 <- appl_291 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_291
                !appl_293 <- appl_292 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_292
                !appl_294 <- appl_293 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_293
                !appl_295 <- appl_294 `pseq` klCons (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_294
                !appl_296 <- appl_295 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_295
                !appl_297 <- appl_296 `pseq` klCons (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_296
                !appl_298 <- appl_297 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_297
                !appl_299 <- appl_298 `pseq` klCons (ApplC (wrapNamed "map" kl_map)) appl_298
                !appl_300 <- appl_299 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_299
                !appl_301 <- appl_300 `pseq` klCons (ApplC (wrapNamed "macroexpand" kl_macroexpand)) appl_300
                !appl_302 <- appl_301 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_301
                !appl_303 <- appl_302 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_302
                !appl_304 <- appl_303 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_303
                !appl_305 <- appl_304 `pseq` klCons (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_304
                !appl_306 <- appl_305 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_305
                !appl_307 <- appl_306 `pseq` klCons (ApplC (wrapNamed "<" lessThan)) appl_306
                !appl_308 <- appl_307 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_307
                !appl_309 <- appl_308 `pseq` klCons (ApplC (wrapNamed "load" kl_load)) appl_308
                !appl_310 <- appl_309 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_309
                !appl_311 <- appl_310 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_310
                !appl_312 <- appl_311 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_311
                !appl_313 <- appl_312 `pseq` klCons (ApplC (wrapNamed "length" kl_length)) appl_312
                !appl_314 <- appl_313 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_313
                !appl_315 <- appl_314 `pseq` klCons (ApplC (PL "language" kl_language)) appl_314
                !appl_316 <- appl_315 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_315
                !appl_317 <- appl_316 `pseq` klCons (ApplC (PL "kill" kl_kill)) appl_316
                !appl_318 <- appl_317 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_317
                !appl_319 <- appl_318 `pseq` klCons (ApplC (PL "it" kl_it)) appl_318
                !appl_320 <- appl_319 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_319
                !appl_321 <- appl_320 `pseq` klCons (ApplC (wrapNamed "intersection" kl_intersection)) appl_320
                !appl_322 <- appl_321 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_321
                !appl_323 <- appl_322 `pseq` klCons (ApplC (PL "implementation" kl_implementation)) appl_322
                !appl_324 <- appl_323 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_323
                !appl_325 <- appl_324 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_324
                !appl_326 <- appl_325 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_325
                !appl_327 <- appl_326 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_326
                !appl_328 <- appl_327 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_327
                !appl_329 <- appl_328 `pseq` klCons (ApplC (PL "inferences" kl_inferences)) appl_328
                !appl_330 <- appl_329 `pseq` klCons (Types.Atom (Types.N (Types.KI 4))) appl_329
                !appl_331 <- appl_330 `pseq` klCons (ApplC (wrapNamed "identical" kl_identical)) appl_330
                !appl_332 <- appl_331 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_331
                !appl_333 <- appl_332 `pseq` klCons (ApplC (wrapNamed "intern" intern)) appl_332
                !appl_334 <- appl_333 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_333
                !appl_335 <- appl_334 `pseq` klCons (ApplC (wrapNamed "integer?" kl_integerP)) appl_334
                !appl_336 <- appl_335 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_335
                !appl_337 <- appl_336 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_336
                !appl_338 <- appl_337 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_337
                !appl_339 <- appl_338 `pseq` klCons (ApplC (wrapNamed "head" kl_head)) appl_338
                !appl_340 <- appl_339 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_339
                !appl_341 <- appl_340 `pseq` klCons (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_340
                !appl_342 <- appl_341 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_341
                !appl_343 <- appl_342 `pseq` klCons (ApplC (wrapNamed "hdv" kl_hdv)) appl_342
                !appl_344 <- appl_343 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_343
                !appl_345 <- appl_344 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_344
                !appl_346 <- appl_345 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_345
                !appl_347 <- appl_346 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_346
                !appl_348 <- appl_347 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_347
                !appl_349 <- appl_348 `pseq` klCons (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_348
                !appl_350 <- appl_349 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_349
                !appl_351 <- appl_350 `pseq` klCons (ApplC (wrapNamed ">" greaterThan)) appl_350
                !appl_352 <- appl_351 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_351
                !appl_353 <- appl_352 `pseq` klCons (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_352
                !appl_354 <- appl_353 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_353
                !appl_355 <- appl_354 `pseq` klCons (ApplC (wrapNamed "<-address" addressFrom)) appl_354
                !appl_356 <- appl_355 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_355
                !appl_357 <- appl_356 `pseq` klCons (ApplC (wrapNamed "address->" addressTo)) appl_356
                !appl_358 <- appl_357 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_357
                !appl_359 <- appl_358 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_358
                !appl_360 <- appl_359 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_359
                !appl_361 <- appl_360 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_360
                !appl_362 <- appl_361 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_361
                !appl_363 <- appl_362 `pseq` klCons (ApplC (wrapNamed "gensym" kl_gensym)) appl_362
                !appl_364 <- appl_363 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_363
                !appl_365 <- appl_364 `pseq` klCons (ApplC (wrapNamed "fst" kl_fst)) appl_364
                !appl_366 <- appl_365 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_365
                !appl_367 <- appl_366 `pseq` klCons (Types.Atom (Types.UnboundSym "freeze")) appl_366
                !appl_368 <- appl_367 `pseq` klCons (Types.Atom (Types.N (Types.KI 5))) appl_367
                !appl_369 <- appl_368 `pseq` klCons (Types.Atom (Types.UnboundSym "findall")) appl_368
                !appl_370 <- appl_369 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_369
                !appl_371 <- appl_370 `pseq` klCons (ApplC (wrapNamed "fix" kl_fix)) appl_370
                !appl_372 <- appl_371 `pseq` klCons (Types.Atom (Types.N (Types.KI 0))) appl_371
                !appl_373 <- appl_372 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_372
                !appl_374 <- appl_373 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_373
                !appl_375 <- appl_374 `pseq` klCons (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_374
                !appl_376 <- appl_375 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_375
                !appl_377 <- appl_376 `pseq` klCons (ApplC (wrapNamed "external" kl_external)) appl_376
                !appl_378 <- appl_377 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_377
                !appl_379 <- appl_378 `pseq` klCons (ApplC (wrapNamed "explode" kl_explode)) appl_378
                !appl_380 <- appl_379 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_379
                !appl_381 <- appl_380 `pseq` klCons (ApplC (wrapNamed "eval-kl" evalKL)) appl_380
                !appl_382 <- appl_381 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_381
                !appl_383 <- appl_382 `pseq` klCons (ApplC (wrapNamed "eval" kl_eval)) appl_382
                !appl_384 <- appl_383 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_383
                !appl_385 <- appl_384 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.interror")) appl_384
                !appl_386 <- appl_385 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_385
                !appl_387 <- appl_386 `pseq` klCons (Types.Atom (Types.UnboundSym "enable-type-theory")) appl_386
                !appl_388 <- appl_387 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_387
                !appl_389 <- appl_388 `pseq` klCons (ApplC (wrapNamed "empty?" kl_emptyP)) appl_388
                !appl_390 <- appl_389 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_389
                !appl_391 <- appl_390 `pseq` klCons (ApplC (wrapNamed "element?" kl_elementP)) appl_390
                !appl_392 <- appl_391 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_391
                !appl_393 <- appl_392 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_392
                !appl_394 <- appl_393 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_393
                !appl_395 <- appl_394 `pseq` klCons (ApplC (wrapNamed "difference" kl_difference)) appl_394
                !appl_396 <- appl_395 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_395
                !appl_397 <- appl_396 `pseq` klCons (ApplC (wrapNamed "destroy" kl_destroy)) appl_396
                !appl_398 <- appl_397 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_397
                !appl_399 <- appl_398 `pseq` klCons (Types.Atom (Types.UnboundSym "declare")) appl_398
                !appl_400 <- appl_399 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_399
                !appl_401 <- appl_400 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_400
                !appl_402 <- appl_401 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_401
                !appl_403 <- appl_402 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_402
                !appl_404 <- appl_403 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_403
                !appl_405 <- appl_404 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_404
                !appl_406 <- appl_405 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_405
                !appl_407 <- appl_406 `pseq` klCons (ApplC (wrapNamed "concat" kl_concat)) appl_406
                !appl_408 <- appl_407 `pseq` klCons (Types.Atom (Types.N (Types.KI 3))) appl_407
                !appl_409 <- appl_408 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_408
                !appl_410 <- appl_409 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_409
                !appl_411 <- appl_410 `pseq` klCons (ApplC (wrapNamed "cd" kl_cd)) appl_410
                !appl_412 <- appl_411 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_411
                !appl_413 <- appl_412 `pseq` klCons (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_412
                !appl_414 <- appl_413 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_413
                !appl_415 <- appl_414 `pseq` klCons (ApplC (wrapNamed "assoc" kl_assoc)) appl_414
                !appl_416 <- appl_415 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_415
                !appl_417 <- appl_416 `pseq` klCons (ApplC (wrapNamed "arity" kl_arity)) appl_416
                !appl_418 <- appl_417 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_417
                !appl_419 <- appl_418 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_418
                !appl_420 <- appl_419 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_419
                !appl_421 <- appl_420 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_420
                !appl_422 <- appl_421 `pseq` klCons (Types.Atom (Types.N (Types.KI 2))) appl_421
                !appl_423 <- appl_422 `pseq` klCons (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_422
                !appl_424 <- appl_423 `pseq` klCons (Types.Atom (Types.N (Types.KI 1))) appl_423
                !appl_425 <- appl_424 `pseq` klCons (ApplC (wrapNamed "absvector" absvector)) appl_424
                appl_425 `pseq` kl_shen_initialise_arity_table appl_425) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
            (do !appl_426 <- intern (Types.Atom (Types.Str "shen"))
                !appl_427 <- kl_vector (Types.Atom (Types.N (Types.KI 0)))
                let !appl_428 = List []
                !appl_429 <- appl_428 `pseq` klCons (ApplC (PL "abort" kl_abort)) appl_428
                !appl_430 <- appl_429 `pseq` klCons (ApplC (wrapNamed "absvector" absvector)) appl_429
                !appl_431 <- appl_430 `pseq` klCons (ApplC (wrapNamed "absvector?" absvectorP)) appl_430
                !appl_432 <- appl_431 `pseq` klCons (ApplC (wrapNamed "address->" addressTo)) appl_431
                !appl_433 <- appl_432 `pseq` klCons (ApplC (wrapNamed "<-address" addressFrom)) appl_432
                !appl_434 <- appl_433 `pseq` klCons (ApplC (wrapNamed "adjoin" kl_adjoin)) appl_433
                !appl_435 <- appl_434 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_434
                !appl_436 <- appl_435 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_435
                !appl_437 <- appl_436 `pseq` klCons (ApplC (wrapNamed "arity" kl_arity)) appl_436
                !appl_438 <- appl_437 `pseq` klCons (ApplC (wrapNamed "assoc" kl_assoc)) appl_437
                !appl_439 <- appl_438 `pseq` klCons (Types.Atom (Types.UnboundSym "bar!")) appl_438
                !appl_440 <- appl_439 `pseq` klCons (Types.Atom (Types.UnboundSym "boolean")) appl_439
                !appl_441 <- appl_440 `pseq` klCons (ApplC (wrapNamed "boolean?" kl_booleanP)) appl_440
                !appl_442 <- appl_441 `pseq` klCons (ApplC (wrapNamed "bound?" kl_boundP)) appl_441
                !appl_443 <- appl_442 `pseq` klCons (ApplC (wrapNamed "bind" kl_bind)) appl_442
                !appl_444 <- appl_443 `pseq` klCons (ApplC (wrapNamed "close" closeStream)) appl_443
                !appl_445 <- appl_444 `pseq` klCons (ApplC (wrapNamed "call" kl_call)) appl_444
                !appl_446 <- appl_445 `pseq` klCons (Types.Atom (Types.UnboundSym "cases")) appl_445
                !appl_447 <- appl_446 `pseq` klCons (ApplC (wrapNamed "cd" kl_cd)) appl_446
                !appl_448 <- appl_447 `pseq` klCons (ApplC (wrapNamed "compile" kl_compile)) appl_447
                !appl_449 <- appl_448 `pseq` klCons (ApplC (wrapNamed "concat" kl_concat)) appl_448
                !appl_450 <- appl_449 `pseq` klCons (Types.Atom (Types.UnboundSym "cond")) appl_449
                !appl_451 <- appl_450 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_450
                !appl_452 <- appl_451 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_451
                !appl_453 <- appl_452 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_452
                !appl_454 <- appl_453 `pseq` klCons (ApplC (wrapNamed "cut" kl_cut)) appl_453
                !appl_455 <- appl_454 `pseq` klCons (Types.Atom (Types.UnboundSym "datatype")) appl_454
                !appl_456 <- appl_455 `pseq` klCons (Types.Atom (Types.UnboundSym "declare")) appl_455
                !appl_457 <- appl_456 `pseq` klCons (Types.Atom (Types.UnboundSym "defprolog")) appl_456
                !appl_458 <- appl_457 `pseq` klCons (Types.Atom (Types.UnboundSym "defcc")) appl_457
                !appl_459 <- appl_458 `pseq` klCons (Types.Atom (Types.UnboundSym "defmacro")) appl_458
                !appl_460 <- appl_459 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_459
                !appl_461 <- appl_460 `pseq` klCons (Types.Atom (Types.UnboundSym "defun")) appl_460
                !appl_462 <- appl_461 `pseq` klCons (ApplC (wrapNamed "destroy" kl_destroy)) appl_461
                !appl_463 <- appl_462 `pseq` klCons (ApplC (wrapNamed "difference" kl_difference)) appl_462
                !appl_464 <- appl_463 `pseq` klCons (ApplC (wrapNamed "do" kl_do)) appl_463
                !appl_465 <- appl_464 `pseq` klCons (ApplC (wrapNamed "element?" kl_elementP)) appl_464
                !appl_466 <- appl_465 `pseq` klCons (ApplC (wrapNamed "empty?" kl_emptyP)) appl_465
                !appl_467 <- appl_466 `pseq` klCons (Types.Atom (Types.UnboundSym "error")) appl_466
                !appl_468 <- appl_467 `pseq` klCons (ApplC (wrapNamed "error-to-string" errorToString)) appl_467
                !appl_469 <- appl_468 `pseq` klCons (ApplC (wrapNamed "eval" kl_eval)) appl_468
                !appl_470 <- appl_469 `pseq` klCons (ApplC (wrapNamed "eval-kl" evalKL)) appl_469
                !appl_471 <- appl_470 `pseq` klCons (Types.Atom (Types.UnboundSym "exception")) appl_470
                !appl_472 <- appl_471 `pseq` klCons (ApplC (wrapNamed "external" kl_external)) appl_471
                !appl_473 <- appl_472 `pseq` klCons (ApplC (wrapNamed "explode" kl_explode)) appl_472
                !appl_474 <- appl_473 `pseq` klCons (Types.Atom (Types.UnboundSym "enable-type-theory")) appl_473
                !appl_475 <- appl_474 `pseq` klCons (Atom (B False)) appl_474
                !appl_476 <- appl_475 `pseq` klCons (Types.Atom (Types.UnboundSym "findall")) appl_475
                !appl_477 <- appl_476 `pseq` klCons (ApplC (wrapNamed "fwhen" kl_fwhen)) appl_476
                !appl_478 <- appl_477 `pseq` klCons (ApplC (wrapNamed "fail-if" kl_fail_if)) appl_477
                !appl_479 <- appl_478 `pseq` klCons (ApplC (PL "fail" kl_fail)) appl_478
                !appl_480 <- appl_479 `pseq` klCons (Types.Atom (Types.UnboundSym "file")) appl_479
                !appl_481 <- appl_480 `pseq` klCons (ApplC (wrapNamed "fix" kl_fix)) appl_480
                !appl_482 <- appl_481 `pseq` klCons (Types.Atom (Types.UnboundSym "freeze")) appl_481
                !appl_483 <- appl_482 `pseq` klCons (ApplC (wrapNamed "fst" kl_fst)) appl_482
                !appl_484 <- appl_483 `pseq` klCons (Types.Atom (Types.UnboundSym "function")) appl_483
                !appl_485 <- appl_484 `pseq` klCons (ApplC (wrapNamed "gensym" kl_gensym)) appl_484
                !appl_486 <- appl_485 `pseq` klCons (ApplC (wrapNamed "get-time" getTime)) appl_485
                !appl_487 <- appl_486 `pseq` klCons (ApplC (wrapNamed "get" kl_get)) appl_486
                !appl_488 <- appl_487 `pseq` klCons (ApplC (wrapNamed "hash" kl_hash)) appl_487
                !appl_489 <- appl_488 `pseq` klCons (ApplC (wrapNamed "hdstr" kl_hdstr)) appl_488
                !appl_490 <- appl_489 `pseq` klCons (ApplC (wrapNamed "hdv" kl_hdv)) appl_489
                !appl_491 <- appl_490 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_490
                !appl_492 <- appl_491 `pseq` klCons (ApplC (wrapNamed "head" kl_head)) appl_491
                !appl_493 <- appl_492 `pseq` klCons (ApplC (wrapNamed "identical" kl_identical)) appl_492
                !appl_494 <- appl_493 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_493
                !appl_495 <- appl_494 `pseq` klCons (ApplC (PL "implementation" kl_implementation)) appl_494
                !appl_496 <- appl_495 `pseq` klCons (Types.Atom (Types.UnboundSym "in")) appl_495
                !appl_497 <- appl_496 `pseq` klCons (ApplC (PL "it" kl_it)) appl_496
                !appl_498 <- appl_497 `pseq` klCons (ApplC (wrapNamed "include-all-but" kl_include_all_but)) appl_497
                !appl_499 <- appl_498 `pseq` klCons (ApplC (wrapNamed "include" kl_include)) appl_498
                !appl_500 <- appl_499 `pseq` klCons (ApplC (wrapNamed "input+" kl_inputPlus)) appl_499
                !appl_501 <- appl_500 `pseq` klCons (ApplC (wrapNamed "input" kl_input)) appl_500
                !appl_502 <- appl_501 `pseq` klCons (ApplC (wrapNamed "integer?" kl_integerP)) appl_501
                !appl_503 <- appl_502 `pseq` klCons (ApplC (wrapNamed "intern" intern)) appl_502
                !appl_504 <- appl_503 `pseq` klCons (ApplC (PL "inferences" kl_inferences)) appl_503
                !appl_505 <- appl_504 `pseq` klCons (ApplC (wrapNamed "intersection" kl_intersection)) appl_504
                !appl_506 <- appl_505 `pseq` klCons (Types.Atom (Types.UnboundSym "is")) appl_505
                !appl_507 <- appl_506 `pseq` klCons (ApplC (PL "kill" kl_kill)) appl_506
                !appl_508 <- appl_507 `pseq` klCons (ApplC (PL "language" kl_language)) appl_507
                !appl_509 <- appl_508 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_508
                !appl_510 <- appl_509 `pseq` klCons (Types.Atom (Types.UnboundSym "lazy")) appl_509
                !appl_511 <- appl_510 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_510
                !appl_512 <- appl_511 `pseq` klCons (ApplC (wrapNamed "length" kl_length)) appl_511
                !appl_513 <- appl_512 `pseq` klCons (ApplC (wrapNamed "limit" kl_limit)) appl_512
                !appl_514 <- appl_513 `pseq` klCons (ApplC (wrapNamed "lineread" kl_lineread)) appl_513
                !appl_515 <- appl_514 `pseq` klCons (Types.Atom (Types.UnboundSym "list")) appl_514
                !appl_516 <- appl_515 `pseq` klCons (Types.Atom (Types.UnboundSym "loaded")) appl_515
                !appl_517 <- appl_516 `pseq` klCons (ApplC (wrapNamed "load" kl_load)) appl_516
                !appl_518 <- appl_517 `pseq` klCons (Types.Atom (Types.UnboundSym "make-string")) appl_517
                !appl_519 <- appl_518 `pseq` klCons (ApplC (wrapNamed "map" kl_map)) appl_518
                !appl_520 <- appl_519 `pseq` klCons (ApplC (wrapNamed "mapcan" kl_mapcan)) appl_519
                !appl_521 <- appl_520 `pseq` klCons (ApplC (wrapNamed "maxinferences" kl_maxinferences)) appl_520
                !appl_522 <- appl_521 `pseq` klCons (ApplC (wrapNamed "macroexpand" kl_macroexpand)) appl_521
                !appl_523 <- appl_522 `pseq` klCons (Types.Atom (Types.UnboundSym "mode")) appl_522
                !appl_524 <- appl_523 `pseq` klCons (ApplC (wrapNamed "nl" kl_nl)) appl_523
                !appl_525 <- appl_524 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_524
                !appl_526 <- appl_525 `pseq` klCons (ApplC (wrapNamed "nth" kl_nth)) appl_525
                !appl_527 <- appl_526 `pseq` klCons (Types.Atom (Types.UnboundSym "null")) appl_526
                !appl_528 <- appl_527 `pseq` klCons (Types.Atom (Types.UnboundSym "number")) appl_527
                !appl_529 <- appl_528 `pseq` klCons (ApplC (wrapNamed "number?" numberP)) appl_528
                !appl_530 <- appl_529 `pseq` klCons (ApplC (wrapNamed "n->string" nToString)) appl_529
                !appl_531 <- appl_530 `pseq` klCons (ApplC (wrapNamed "occurs-check" kl_occurs_check)) appl_530
                !appl_532 <- appl_531 `pseq` klCons (ApplC (wrapNamed "occurrences" kl_occurrences)) appl_531
                !appl_533 <- appl_532 `pseq` klCons (ApplC (wrapNamed "open" openStream)) appl_532
                !appl_534 <- appl_533 `pseq` klCons (ApplC (wrapNamed "optimise" kl_optimise)) appl_533
                !appl_535 <- appl_534 `pseq` klCons (Types.Atom (Types.UnboundSym "or")) appl_534
                !appl_536 <- appl_535 `pseq` klCons (ApplC (PL "os" kl_os)) appl_535
                !appl_537 <- appl_536 `pseq` klCons (Types.Atom (Types.UnboundSym "out")) appl_536
                !appl_538 <- appl_537 `pseq` klCons (Types.Atom (Types.UnboundSym "output")) appl_537
                !appl_539 <- appl_538 `pseq` klCons (Types.Atom (Types.UnboundSym "package")) appl_538
                !appl_540 <- appl_539 `pseq` klCons (ApplC (PL "port" kl_port)) appl_539
                !appl_541 <- appl_540 `pseq` klCons (ApplC (PL "porters" kl_porters)) appl_540
                !appl_542 <- appl_541 `pseq` klCons (ApplC (wrapNamed "pos" pos)) appl_541
                !appl_543 <- appl_542 `pseq` klCons (ApplC (wrapNamed "pr" kl_pr)) appl_542
                !appl_544 <- appl_543 `pseq` klCons (ApplC (wrapNamed "print" kl_print)) appl_543
                !appl_545 <- appl_544 `pseq` klCons (ApplC (wrapNamed "profile" kl_profile)) appl_544
                !appl_546 <- appl_545 `pseq` klCons (ApplC (wrapNamed "profile-results" kl_profile_results)) appl_545
                !appl_547 <- appl_546 `pseq` klCons (ApplC (wrapNamed "protect" kl_protect)) appl_546
                !appl_548 <- appl_547 `pseq` klCons (Types.Atom (Types.UnboundSym "prolog?")) appl_547
                !appl_549 <- appl_548 `pseq` klCons (ApplC (wrapNamed "ps" kl_ps)) appl_548
                !appl_550 <- appl_549 `pseq` klCons (ApplC (wrapNamed "preclude-all-but" kl_preclude_all_but)) appl_549
                !appl_551 <- appl_550 `pseq` klCons (ApplC (wrapNamed "preclude" kl_preclude)) appl_550
                !appl_552 <- appl_551 `pseq` klCons (ApplC (wrapNamed "put" kl_put)) appl_551
                !appl_553 <- appl_552 `pseq` klCons (ApplC (wrapNamed "package?" kl_packageP)) appl_552
                !appl_554 <- appl_553 `pseq` klCons (ApplC (wrapNamed "read-from-string" kl_read_from_string)) appl_553
                !appl_555 <- appl_554 `pseq` klCons (ApplC (wrapNamed "read-byte" readByte)) appl_554
                !appl_556 <- appl_555 `pseq` klCons (ApplC (wrapNamed "read-file-as-string" kl_read_file_as_string)) appl_555
                !appl_557 <- appl_556 `pseq` klCons (ApplC (wrapNamed "read-file-as-bytelist" kl_read_file_as_bytelist)) appl_556
                !appl_558 <- appl_557 `pseq` klCons (Types.Atom (Types.UnboundSym "require")) appl_557
                !appl_559 <- appl_558 `pseq` klCons (ApplC (wrapNamed "read-file" kl_read_file)) appl_558
                !appl_560 <- appl_559 `pseq` klCons (ApplC (wrapNamed "read" kl_read)) appl_559
                !appl_561 <- appl_560 `pseq` klCons (ApplC (PL "release" kl_release)) appl_560
                !appl_562 <- appl_561 `pseq` klCons (ApplC (wrapNamed "remove" kl_remove)) appl_561
                !appl_563 <- appl_562 `pseq` klCons (ApplC (wrapNamed "reverse" kl_reverse)) appl_562
                !appl_564 <- appl_563 `pseq` klCons (Types.Atom (Types.UnboundSym "run")) appl_563
                !appl_565 <- appl_564 `pseq` klCons (ApplC (wrapNamed "str" str)) appl_564
                !appl_566 <- appl_565 `pseq` klCons (Types.Atom (Types.UnboundSym "save")) appl_565
                !appl_567 <- appl_566 `pseq` klCons (ApplC (wrapNamed "set" klSet)) appl_566
                !appl_568 <- appl_567 `pseq` klCons (ApplC (wrapNamed "simple-error" simpleError)) appl_567
                !appl_569 <- appl_568 `pseq` klCons (ApplC (wrapNamed "snd" kl_snd)) appl_568
                !appl_570 <- appl_569 `pseq` klCons (ApplC (wrapNamed "specialise" kl_specialise)) appl_569
                !appl_571 <- appl_570 `pseq` klCons (ApplC (wrapNamed "spy" kl_spy)) appl_570
                !appl_572 <- appl_571 `pseq` klCons (ApplC (wrapNamed "step" kl_step)) appl_571
                !appl_573 <- appl_572 `pseq` klCons (ApplC (PL "stoutput" kl_stoutput)) appl_572
                !appl_574 <- appl_573 `pseq` klCons (ApplC (PL "stinput" kl_stinput)) appl_573
                !appl_575 <- appl_574 `pseq` klCons (Types.Atom (Types.UnboundSym "string")) appl_574
                !appl_576 <- appl_575 `pseq` klCons (Types.Atom (Types.UnboundSym "stream")) appl_575
                !appl_577 <- appl_576 `pseq` klCons (ApplC (wrapNamed "string->n" stringToN)) appl_576
                !appl_578 <- appl_577 `pseq` klCons (ApplC (wrapNamed "string?" stringP)) appl_577
                !appl_579 <- appl_578 `pseq` klCons (ApplC (wrapNamed "subst" kl_subst)) appl_578
                !appl_580 <- appl_579 `pseq` klCons (ApplC (wrapNamed "sum" kl_sum)) appl_579
                !appl_581 <- appl_580 `pseq` klCons (ApplC (wrapNamed "string->symbol" kl_string_RBsymbol)) appl_580
                !appl_582 <- appl_581 `pseq` klCons (ApplC (wrapNamed "symbol?" kl_symbolP)) appl_581
                !appl_583 <- appl_582 `pseq` klCons (Types.Atom (Types.UnboundSym "symbol")) appl_582
                !appl_584 <- appl_583 `pseq` klCons (Types.Atom (Types.UnboundSym "synonyms")) appl_583
                !appl_585 <- appl_584 `pseq` klCons (ApplC (wrapNamed "systemf" kl_systemf)) appl_584
                !appl_586 <- appl_585 `pseq` klCons (ApplC (wrapNamed "tail" kl_tail)) appl_585
                !appl_587 <- appl_586 `pseq` klCons (ApplC (wrapNamed "tlv" kl_tlv)) appl_586
                !appl_588 <- appl_587 `pseq` klCons (ApplC (wrapNamed "tlstr" tlstr)) appl_587
                !appl_589 <- appl_588 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_588
                !appl_590 <- appl_589 `pseq` klCons (ApplC (wrapNamed "tc" kl_tc)) appl_589
                !appl_591 <- appl_590 `pseq` klCons (ApplC (PL "tc?" kl_tcP)) appl_590
                !appl_592 <- appl_591 `pseq` klCons (ApplC (wrapNamed "thaw" kl_thaw)) appl_591
                !appl_593 <- appl_592 `pseq` klCons (Types.Atom (Types.UnboundSym "time")) appl_592
                !appl_594 <- appl_593 `pseq` klCons (ApplC (wrapNamed "track" kl_track)) appl_593
                !appl_595 <- appl_594 `pseq` klCons (Types.Atom (Types.UnboundSym "trap-error")) appl_594
                !appl_596 <- appl_595 `pseq` klCons (Atom (B True)) appl_595
                !appl_597 <- appl_596 `pseq` klCons (ApplC (wrapNamed "tuple?" kl_tupleP)) appl_596
                !appl_598 <- appl_597 `pseq` klCons (ApplC (wrapNamed "type" typeA)) appl_597
                !appl_599 <- appl_598 `pseq` klCons (ApplC (wrapNamed "return" kl_return)) appl_598
                !appl_600 <- appl_599 `pseq` klCons (ApplC (wrapNamed "undefmacro" kl_undefmacro)) appl_599
                !appl_601 <- appl_600 `pseq` klCons (ApplC (wrapNamed "unprofile" kl_unprofile)) appl_600
                !appl_602 <- appl_601 `pseq` klCons (ApplC (wrapNamed "unput" kl_unput)) appl_601
                !appl_603 <- appl_602 `pseq` klCons (ApplC (wrapNamed "unify!" kl_unifyExcl)) appl_602
                !appl_604 <- appl_603 `pseq` klCons (ApplC (wrapNamed "unify" kl_unify)) appl_603
                !appl_605 <- appl_604 `pseq` klCons (ApplC (wrapNamed "union" kl_union)) appl_604
                !appl_606 <- appl_605 `pseq` klCons (Types.Atom (Types.UnboundSym "shen.unix")) appl_605
                !appl_607 <- appl_606 `pseq` klCons (Types.Atom (Types.UnboundSym "unit")) appl_606
                !appl_608 <- appl_607 `pseq` klCons (ApplC (wrapNamed "untrack" kl_untrack)) appl_607
                !appl_609 <- appl_608 `pseq` klCons (ApplC (wrapNamed "unspecialise" kl_unspecialise)) appl_608
                !appl_610 <- appl_609 `pseq` klCons (ApplC (wrapNamed "vector?" kl_vectorP)) appl_609
                !appl_611 <- appl_610 `pseq` klCons (ApplC (wrapNamed "vector" kl_vector)) appl_610
                !appl_612 <- appl_611 `pseq` klCons (ApplC (wrapNamed "<-vector" kl_LB_vector)) appl_611
                !appl_613 <- appl_612 `pseq` klCons (ApplC (wrapNamed "vector->" kl_vector_RB)) appl_612
                !appl_614 <- appl_613 `pseq` klCons (ApplC (wrapNamed "value" value)) appl_613
                !appl_615 <- appl_614 `pseq` klCons (ApplC (wrapNamed "variable?" kl_variableP)) appl_614
                !appl_616 <- appl_615 `pseq` klCons (Types.Atom (Types.UnboundSym "verified")) appl_615
                !appl_617 <- appl_616 `pseq` klCons (ApplC (PL "version" kl_version)) appl_616
                !appl_618 <- appl_617 `pseq` klCons (Types.Atom (Types.UnboundSym "warn")) appl_617
                !appl_619 <- appl_618 `pseq` klCons (Types.Atom (Types.UnboundSym "when")) appl_618
                !appl_620 <- appl_619 `pseq` klCons (Types.Atom (Types.UnboundSym "where")) appl_619
                !appl_621 <- appl_620 `pseq` klCons (ApplC (wrapNamed "write-byte" writeByte)) appl_620
                !appl_622 <- appl_621 `pseq` klCons (ApplC (wrapNamed "write-to-file" kl_write_to_file)) appl_621
                !appl_623 <- appl_622 `pseq` klCons (ApplC (wrapNamed "y-or-n?" kl_y_or_nP)) appl_622
                !appl_624 <- appl_427 `pseq` (appl_623 `pseq` klCons appl_427 appl_623)
                !appl_625 <- appl_624 `pseq` klCons (Types.Atom (Types.UnboundSym ">>")) appl_624
                !appl_626 <- appl_625 `pseq` klCons (ApplC (wrapNamed "<" lessThan)) appl_625
                !appl_627 <- appl_626 `pseq` klCons (ApplC (wrapNamed "<=" lessThanOrEqualTo)) appl_626
                !appl_628 <- appl_627 `pseq` klCons (ApplC (wrapNamed "+" add)) appl_627
                !appl_629 <- appl_628 `pseq` klCons (ApplC (wrapNamed "*" multiply)) appl_628
                !appl_630 <- appl_629 `pseq` klCons (ApplC (wrapNamed "/" divide)) appl_629
                !appl_631 <- appl_630 `pseq` klCons (ApplC (wrapNamed "-" Primitives.subtract)) appl_630
                !appl_632 <- appl_631 `pseq` klCons (Types.Atom (Types.UnboundSym "$")) appl_631
                !appl_633 <- appl_632 `pseq` klCons (Types.Atom (Types.UnboundSym "=!")) appl_632
                !appl_634 <- appl_633 `pseq` klCons (Types.Atom (Types.UnboundSym "/.")) appl_633
                !appl_635 <- appl_634 `pseq` klCons (ApplC (wrapNamed ">" greaterThan)) appl_634
                !appl_636 <- appl_635 `pseq` klCons (ApplC (wrapNamed ">=" greaterThanOrEqualTo)) appl_635
                !appl_637 <- appl_636 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_636
                !appl_638 <- appl_637 `pseq` klCons (ApplC (wrapNamed "==" kl_EqEq)) appl_637
                !appl_639 <- appl_638 `pseq` klCons (ApplC (wrapNamed "<e>" kl_LBeRB)) appl_638
                !appl_640 <- appl_639 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_639
                !appl_641 <- appl_640 `pseq` klCons (Types.Atom (Types.UnboundSym "<-")) appl_640
                !appl_642 <- appl_641 `pseq` klCons (Types.Atom (Types.UnboundSym "*hush*")) appl_641
                !appl_643 <- appl_642 `pseq` klCons (Types.Atom (Types.UnboundSym "*porters*")) appl_642
                !appl_644 <- appl_643 `pseq` klCons (Types.Atom (Types.UnboundSym "*port*")) appl_643
                !appl_645 <- appl_644 `pseq` klCons (ApplC (wrapNamed "@s" kl_Ats)) appl_644
                !appl_646 <- appl_645 `pseq` klCons (ApplC (wrapNamed "@p" kl_Atp)) appl_645
                !appl_647 <- appl_646 `pseq` klCons (ApplC (wrapNamed "@v" kl_Atv)) appl_646
                !appl_648 <- appl_647 `pseq` klCons (Types.Atom (Types.UnboundSym "*property-vector*")) appl_647
                !appl_649 <- appl_648 `pseq` klCons (Types.Atom (Types.UnboundSym "*release*")) appl_648
                !appl_650 <- appl_649 `pseq` klCons (Types.Atom (Types.UnboundSym "*os*")) appl_649
                !appl_651 <- appl_650 `pseq` klCons (Types.Atom (Types.UnboundSym "*macros*")) appl_650
                !appl_652 <- appl_651 `pseq` klCons (Types.Atom (Types.UnboundSym "*maximum-print-sequence-size*")) appl_651
                !appl_653 <- appl_652 `pseq` klCons (Types.Atom (Types.UnboundSym "*version*")) appl_652
                !appl_654 <- appl_653 `pseq` klCons (Types.Atom (Types.UnboundSym "*home-directory*")) appl_653
                !appl_655 <- appl_654 `pseq` klCons (Types.Atom (Types.UnboundSym "*stoutput*")) appl_654
                !appl_656 <- appl_655 `pseq` klCons (Types.Atom (Types.UnboundSym "*stinput*")) appl_655
                !appl_657 <- appl_656 `pseq` klCons (Types.Atom (Types.UnboundSym "*implementation*")) appl_656
                !appl_658 <- appl_657 `pseq` klCons (Types.Atom (Types.UnboundSym "*language*")) appl_657
                !appl_659 <- appl_658 `pseq` klCons (Types.Atom (Types.UnboundSym "_")) appl_658
                !appl_660 <- appl_659 `pseq` klCons (Types.Atom (Types.UnboundSym ":=")) appl_659
                !appl_661 <- appl_660 `pseq` klCons (Types.Atom (Types.UnboundSym ":-")) appl_660
                !appl_662 <- appl_661 `pseq` klCons (Types.Atom (Types.UnboundSym ";")) appl_661
                !appl_663 <- appl_662 `pseq` klCons (Types.Atom (Types.UnboundSym ":")) appl_662
                !appl_664 <- appl_663 `pseq` klCons (Types.Atom (Types.UnboundSym "&&")) appl_663
                !appl_665 <- appl_664 `pseq` klCons (Types.Atom (Types.UnboundSym "<--")) appl_664
                !appl_666 <- appl_665 `pseq` klCons (Types.Atom (Types.UnboundSym "-->")) appl_665
                !appl_667 <- appl_666 `pseq` klCons (Types.Atom (Types.UnboundSym "{")) appl_666
                !appl_668 <- appl_667 `pseq` klCons (Types.Atom (Types.UnboundSym "}")) appl_667
                !appl_669 <- appl_668 `pseq` klCons (Types.Atom (Types.UnboundSym "!")) appl_668
                !appl_670 <- value (Types.Atom (Types.UnboundSym "*property-vector*"))
                appl_426 `pseq` (appl_669 `pseq` (appl_670 `pseq` kl_put appl_426 (Types.Atom (Types.UnboundSym "shen.external-symbols")) appl_669 appl_670))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
