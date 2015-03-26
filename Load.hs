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

module Load where

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

kl_load :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_load (!kl_V738) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Load) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Infs) -> do return (Types.Atom (Types.UnboundSym "loaded")))))
                                                                                       !kl_if_2 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                                                                                       !appl_3 <- klIf kl_if_2 (do !appl_4 <- kl_inferences
                                                                                                                   let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                   !appl_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4,
                                                                                                                                                               Types.Atom (Types.Str " inferences\n"),
                                                                                                                                                               Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                   !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str "\ntypechecked in ")) appl_6
                                                                                                                   !appl_8 <- kl_stoutput
                                                                                                                   let !aw_9 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                   appl_7 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_7,
                                                                                                                                                                   appl_8])) (do return (Types.Atom (Types.UnboundSym "shen.skip")))
                                                                                       appl_3 `pseq` applyWrapper appl_1 [appl_3])))
                        let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_Start) -> do let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_Result) -> do let !appl_12 = ApplC (Func "lambda" (Context (\(!kl_Finish) -> do let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_Time) -> do let !appl_14 = ApplC (Func "lambda" (Context (\(!kl_Message) -> do return kl_Result)))
                                                                                                                                                                                                                                                                                             !appl_15 <- kl_Time `pseq` str kl_Time
                                                                                                                                                                                                                                                                                             !appl_16 <- appl_15 `pseq` cn appl_15 (Types.Atom (Types.Str " secs\n"))
                                                                                                                                                                                                                                                                                             !appl_17 <- appl_16 `pseq` cn (Types.Atom (Types.Str "\nrun time: ")) appl_16
                                                                                                                                                                                                                                                                                             !appl_18 <- kl_stoutput
                                                                                                                                                                                                                                                                                             let !aw_19 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                                                                                                                                                             !appl_20 <- appl_17 `pseq` (appl_18 `pseq` applyWrapper aw_19 [appl_17,
                                                                                                                                                                                                                                                                                                                                                            appl_18])
                                                                                                                                                                                                                                                                                             appl_20 `pseq` applyWrapper appl_14 [appl_20])))
                                                                                                                                                                                                                             !appl_21 <- kl_Finish `pseq` (kl_Start `pseq` Primitives.subtract kl_Finish kl_Start)
                                                                                                                                                                                                                             appl_21 `pseq` applyWrapper appl_13 [appl_21])))
                                                                                                                                                           !appl_22 <- getTime (Types.Atom (Types.UnboundSym "run"))
                                                                                                                                                           appl_22 `pseq` applyWrapper appl_12 [appl_22])))
                                                                                         !appl_23 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                                                                                         !appl_24 <- kl_V738 `pseq` kl_read_file kl_V738
                                                                                         !appl_25 <- appl_23 `pseq` (appl_24 `pseq` kl_shen_load_help appl_23 appl_24)
                                                                                         appl_25 `pseq` applyWrapper appl_11 [appl_25])))
                        !appl_26 <- getTime (Types.Atom (Types.UnboundSym "run"))
                        !appl_27 <- appl_26 `pseq` applyWrapper appl_10 [appl_26]
                        appl_27 `pseq` applyWrapper appl_0 [appl_27]

kl_shen_load_help :: Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_load_help (!kl_V743) (!kl_V744) = do !kl_if_0 <- kl_V743 `pseq` eq (Atom (B False)) kl_V743
                                             klIf kl_if_0 (do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_2 <- kl_X `pseq` kl_shen_eval_without_macros kl_X
                                                                                                                          let !aw_3 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                          !appl_4 <- appl_2 `pseq` applyWrapper aw_3 [appl_2,
                                                                                                                                                                      Types.Atom (Types.Str "\n"),
                                                                                                                                                                      Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                          !appl_5 <- kl_stoutput
                                                                                                                          let !aw_6 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                          appl_4 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_4,
                                                                                                                                                                          appl_5]))))
                                                              appl_1 `pseq` (kl_V744 `pseq` kl_map appl_1 kl_V744)) (do klIf (Atom (B True)) (do let !appl_7 = ApplC (Func "lambda" (Context (\(!kl_RemoveSynonyms) -> do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_Table) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Assume) -> do (do let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_V736) -> do kl_V736 `pseq` kl_shen_typecheck_and_load kl_V736)))
                                                                                                                                                                                                                                                                                                                                                               appl_10 `pseq` (kl_RemoveSynonyms `pseq` kl_map appl_10 kl_RemoveSynonyms)) `catchError` (\(!kl_E) -> do kl_E `pseq` (kl_Table `pseq` kl_shen_unwind_types (Excep kl_E) kl_Table)))))
                                                                                                                                                                                                                                                                                          let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_V735) -> do kl_V735 `pseq` kl_shen_assumetype kl_V735)))
                                                                                                                                                                                                                                                                                          !appl_12 <- appl_11 `pseq` (kl_Table `pseq` kl_map appl_11 kl_Table)
                                                                                                                                                                                                                                                                                          appl_12 `pseq` applyWrapper appl_9 [appl_12])))
                                                                                                                                                                                                                          let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_V734) -> do kl_V734 `pseq` kl_shen_typetable kl_V734)))
                                                                                                                                                                                                                          !appl_14 <- appl_13 `pseq` (kl_RemoveSynonyms `pseq` kl_mapcan appl_13 kl_RemoveSynonyms)
                                                                                                                                                                                                                          appl_14 `pseq` applyWrapper appl_8 [appl_14])))
                                                                                                                                                 let !appl_15 = ApplC (Func "lambda" (Context (\(!kl_V733) -> do kl_V733 `pseq` kl_shen_remove_synonyms kl_V733)))
                                                                                                                                                 !appl_16 <- appl_15 `pseq` (kl_V744 `pseq` kl_mapcan appl_15 kl_V744)
                                                                                                                                                 appl_16 `pseq` applyWrapper appl_7 [appl_16]) (do return (List [])))

kl_shen_remove_synonyms :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_remove_synonyms (!kl_V745) = do !kl_if_0 <- kl_V745 `pseq` consP kl_V745
                                        !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V745 `pseq` hd kl_V745
                                                                     appl_2 `pseq` eq (ApplC (wrapNamed "shen.synonyms-help" kl_shen_synonyms_help)) appl_2) (do return (Atom (B False)))
                                        klIf kl_if_1 (do !appl_3 <- kl_V745 `pseq` kl_eval kl_V745
                                                         let !appl_4 = List []
                                                         appl_3 `pseq` (appl_4 `pseq` kl_do appl_3 appl_4)) (do klIf (Atom (B True)) (do let !appl_5 = List []
                                                                                                                                         kl_V745 `pseq` (appl_5 `pseq` klCons kl_V745 appl_5)) (do return (List [])))

kl_shen_typecheck_and_load :: Types.KLValue ->
                              Types.KLContext Types.Env Types.KLValue
kl_shen_typecheck_and_load (!kl_V746) = do !appl_0 <- kl_nl (Types.Atom (Types.N (Types.KI 1)))
                                           !appl_1 <- kl_gensym (Types.Atom (Types.UnboundSym "A"))
                                           !appl_2 <- kl_V746 `pseq` (appl_1 `pseq` kl_shen_typecheck_and_evaluate kl_V746 appl_1)
                                           appl_0 `pseq` (appl_2 `pseq` kl_do appl_0 appl_2)

kl_shen_typetable :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_typetable (!kl_V751) = do !kl_if_0 <- kl_V751 `pseq` consP kl_V751
                                  !kl_if_1 <- klIf kl_if_0 (do !appl_2 <- kl_V751 `pseq` hd kl_V751
                                                               !kl_if_3 <- appl_2 `pseq` eq (Types.Atom (Types.UnboundSym "define")) appl_2
                                                               klIf kl_if_3 (do !appl_4 <- kl_V751 `pseq` tl kl_V751
                                                                                appl_4 `pseq` consP appl_4) (do return (Atom (B False)))) (do return (Atom (B False)))
                                  klIf kl_if_1 (do let !appl_5 = ApplC (Func "lambda" (Context (\(!kl_Sig) -> do !appl_6 <- kl_V751 `pseq` tl kl_V751
                                                                                                                 !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                 !appl_8 <- appl_7 `pseq` (kl_Sig `pseq` klCons appl_7 kl_Sig)
                                                                                                                 let !appl_9 = List []
                                                                                                                 appl_8 `pseq` (appl_9 `pseq` klCons appl_8 appl_9))))
                                                   let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_V737) -> do kl_V737 `pseq` kl_shen_LBsigPlusrestRB kl_V737)))
                                                   !appl_11 <- kl_V751 `pseq` tl kl_V751
                                                   !appl_12 <- appl_11 `pseq` tl appl_11
                                                   let !appl_13 = ApplC (Func "lambda" (Context (\(!kl_E) -> do !appl_14 <- kl_V751 `pseq` tl kl_V751
                                                                                                                !appl_15 <- appl_14 `pseq` hd appl_14
                                                                                                                let !aw_16 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                !appl_17 <- appl_15 `pseq` applyWrapper aw_16 [appl_15,
                                                                                                                                                               Types.Atom (Types.Str " lacks a proper signature.\n"),
                                                                                                                                                               Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                appl_17 `pseq` simpleError appl_17)))
                                                   !appl_18 <- appl_10 `pseq` (appl_12 `pseq` (appl_13 `pseq` kl_compile appl_10 appl_12 appl_13))
                                                   appl_18 `pseq` applyWrapper appl_5 [appl_18]) (do klIf (Atom (B True)) (do return (List [])) (do return (List [])))

kl_shen_assumetype :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_assumetype (!kl_V752) = do !kl_if_0 <- kl_V752 `pseq` consP kl_V752
                                   klIf kl_if_0 (do !appl_1 <- kl_V752 `pseq` hd kl_V752
                                                    !appl_2 <- kl_V752 `pseq` tl kl_V752
                                                    let !aw_3 = Types.Atom (Types.UnboundSym "declare")
                                                    appl_1 `pseq` (appl_2 `pseq` applyWrapper aw_3 [appl_1,
                                                                                                    appl_2])) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.assumetype" kl_shen_assumetype))) (do return (List [])))

kl_shen_unwind_types :: Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_unwind_types (!kl_V757) (!kl_V758) = do let !appl_0 = List []
                                                !kl_if_1 <- appl_0 `pseq` (kl_V758 `pseq` eq appl_0 kl_V758)
                                                klIf kl_if_1 (do !appl_2 <- kl_V757 `pseq` errorToString kl_V757
                                                                 appl_2 `pseq` simpleError appl_2) (do !kl_if_3 <- kl_V758 `pseq` consP kl_V758
                                                                                                       !kl_if_4 <- klIf kl_if_3 (do !appl_5 <- kl_V758 `pseq` hd kl_V758
                                                                                                                                    appl_5 `pseq` consP appl_5) (do return (Atom (B False)))
                                                                                                       klIf kl_if_4 (do !appl_6 <- kl_V758 `pseq` hd kl_V758
                                                                                                                        !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                        !appl_8 <- appl_7 `pseq` kl_shen_remtype appl_7
                                                                                                                        !appl_9 <- kl_V758 `pseq` tl kl_V758
                                                                                                                        !appl_10 <- kl_V757 `pseq` (appl_9 `pseq` kl_shen_unwind_types kl_V757 appl_9)
                                                                                                                        appl_8 `pseq` (appl_10 `pseq` kl_do appl_8 appl_10)) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.unwind-types" kl_shen_unwind_types))) (do return (List []))))

kl_shen_remtype :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_remtype (!kl_V759) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*signedfuncs*"))
                                !appl_1 <- kl_V759 `pseq` (appl_0 `pseq` kl_shen_removetype kl_V759 appl_0)
                                appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*signedfuncs*")) appl_1

kl_shen_removetype :: Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_removetype (!kl_V765) (!kl_V766) = do let !appl_0 = List []
                                              !kl_if_1 <- appl_0 `pseq` (kl_V766 `pseq` eq appl_0 kl_V766)
                                              klIf kl_if_1 (do return (List [])) (do !kl_if_2 <- kl_V766 `pseq` consP kl_V766
                                                                                     !kl_if_3 <- klIf kl_if_2 (do !appl_4 <- kl_V766 `pseq` hd kl_V766
                                                                                                                  !kl_if_5 <- appl_4 `pseq` consP appl_4
                                                                                                                  klIf kl_if_5 (do !appl_6 <- kl_V766 `pseq` hd kl_V766
                                                                                                                                   !appl_7 <- appl_6 `pseq` hd appl_6
                                                                                                                                   appl_7 `pseq` (kl_V765 `pseq` eq appl_7 kl_V765)) (do return (Atom (B False)))) (do return (Atom (B False)))
                                                                                     klIf kl_if_3 (do !appl_8 <- kl_V766 `pseq` hd kl_V766
                                                                                                      !appl_9 <- appl_8 `pseq` hd appl_8
                                                                                                      !appl_10 <- kl_V766 `pseq` tl kl_V766
                                                                                                      appl_9 `pseq` (appl_10 `pseq` kl_shen_removetype appl_9 appl_10)) (do !kl_if_11 <- kl_V766 `pseq` consP kl_V766
                                                                                                                                                                            klIf kl_if_11 (do !appl_12 <- kl_V766 `pseq` hd kl_V766
                                                                                                                                                                                              !appl_13 <- kl_V766 `pseq` tl kl_V766
                                                                                                                                                                                              !appl_14 <- kl_V765 `pseq` (appl_13 `pseq` kl_shen_removetype kl_V765 appl_13)
                                                                                                                                                                                              appl_12 `pseq` (appl_14 `pseq` klCons appl_12 appl_14)) (do klIf (Atom (B True)) (do kl_shen_f_error (ApplC (wrapNamed "shen.removetype" kl_shen_removetype))) (do return (List [])))))

kl_shen_LBsigPlusrestRB :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_LBsigPlusrestRB (!kl_V767) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Parse_shen_LBsignatureRB) -> do !appl_1 <- kl_fail
                                                                                                                           !appl_2 <- appl_1 `pseq` (kl_Parse_shen_LBsignatureRB `pseq` eq appl_1 kl_Parse_shen_LBsignatureRB)
                                                                                                                           !kl_if_3 <- appl_2 `pseq` kl_not appl_2
                                                                                                                           klIf kl_if_3 (do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parse_shen_LBExclRB) -> do !appl_5 <- kl_fail
                                                                                                                                                                                                                          !appl_6 <- appl_5 `pseq` (kl_Parse_shen_LBExclRB `pseq` eq appl_5 kl_Parse_shen_LBExclRB)
                                                                                                                                                                                                                          !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                                                                                                                                                                                                          klIf kl_if_7 (do !appl_8 <- kl_Parse_shen_LBExclRB `pseq` hd kl_Parse_shen_LBExclRB
                                                                                                                                                                                                                                           !appl_9 <- kl_Parse_shen_LBsignatureRB `pseq` kl_shen_hdtl kl_Parse_shen_LBsignatureRB
                                                                                                                                                                                                                                           appl_8 `pseq` (appl_9 `pseq` kl_shen_pair appl_8 appl_9)) (do kl_fail))))
                                                                                                                                            !appl_10 <- kl_Parse_shen_LBsignatureRB `pseq` kl_shen_LBExclRB kl_Parse_shen_LBsignatureRB
                                                                                                                                            appl_10 `pseq` applyWrapper appl_4 [appl_10]) (do kl_fail))))
                                        !appl_11 <- kl_V767 `pseq` kl_shen_LBsignatureRB kl_V767
                                        appl_11 `pseq` applyWrapper appl_0 [appl_11]

kl_write_to_file :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_write_to_file (!kl_V768) (!kl_V769) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Stream) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Write) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Close) -> do return kl_V769)))
                                                                                                                                                                                                                                              !appl_4 <- kl_Stream `pseq` closeStream kl_Stream
                                                                                                                                                                                                                                              appl_4 `pseq` applyWrapper appl_3 [appl_4])))
                                                                                                                                                                              let !aw_5 = Types.Atom (Types.UnboundSym "pr")
                                                                                                                                                                              !appl_6 <- kl_String `pseq` (kl_Stream `pseq` applyWrapper aw_5 [kl_String,
                                                                                                                                                                                                                                               kl_Stream])
                                                                                                                                                                              appl_6 `pseq` applyWrapper appl_2 [appl_6])))
                                                                                                             !kl_if_7 <- kl_V769 `pseq` stringP kl_V769
                                                                                                             !appl_8 <- klIf kl_if_7 (do let !aw_9 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                         kl_V769 `pseq` applyWrapper aw_9 [kl_V769,
                                                                                                                                                                           Types.Atom (Types.Str "\n\n"),
                                                                                                                                                                           Types.Atom (Types.UnboundSym "shen.a")]) (do let !aw_10 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                        kl_V769 `pseq` applyWrapper aw_10 [kl_V769,
                                                                                                                                                                                                                                                           Types.Atom (Types.Str "\n\n"),
                                                                                                                                                                                                                                                           Types.Atom (Types.UnboundSym "shen.s")])
                                                                                                             appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                                            !appl_11 <- kl_V768 `pseq` openStream kl_V768 (Types.Atom (Types.UnboundSym "out"))
                                            appl_11 `pseq` applyWrapper appl_0 [appl_11]

expr8 :: Types.KLContext Types.Env Types.KLValue
expr8 = do (return $ List [])
