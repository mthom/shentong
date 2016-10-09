{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Backend.Load where

import Control.Monad.Except
import Control.Parallel
import Environment
import Primitives as Primitives
import Backend.Utils
import Types
import Utils
import Wrap
import Backend.Toplevel
import Backend.Core
import Backend.Sys
import Backend.Sequent
import Backend.Yacc
import Backend.Reader
import Backend.Prolog
import Backend.Track

kl_load :: Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_load (!kl_V1480) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Load) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Infs) -> do return (Types.Atom (Types.UnboundSym "loaded")))))
                                                                                        !kl_if_2 <- value (Types.Atom (Types.UnboundSym "shen.*tc*"))
                                                                                        !appl_3 <- case kl_if_2 of
                                                                                                       Atom (B (True)) -> do !appl_4 <- kl_inferences
                                                                                                                             let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                             !appl_6 <- appl_4 `pseq` applyWrapper aw_5 [appl_4,
                                                                                                                                                                         Types.Atom (Types.Str " inferences\n"),
                                                                                                                                                                         Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                             !appl_7 <- appl_6 `pseq` cn (Types.Atom (Types.Str "\ntypechecked in ")) appl_6
                                                                                                                             !appl_8 <- kl_stoutput
                                                                                                                             let !aw_9 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                             appl_7 `pseq` (appl_8 `pseq` applyWrapper aw_9 [appl_7,
                                                                                                                                                                             appl_8])
                                                                                                       Atom (B (False)) -> do do return (Types.Atom (Types.UnboundSym "shen.skip"))
                                                                                                       _ -> throwError "if: expected boolean"
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
                                                                                          !appl_24 <- kl_V1480 `pseq` kl_read_file kl_V1480
                                                                                          !appl_25 <- appl_23 `pseq` (appl_24 `pseq` kl_shen_load_help appl_23 appl_24)
                                                                                          appl_25 `pseq` applyWrapper appl_11 [appl_25])))
                         !appl_26 <- getTime (Types.Atom (Types.UnboundSym "run"))
                         !appl_27 <- appl_26 `pseq` applyWrapper appl_10 [appl_26]
                         appl_27 `pseq` applyWrapper appl_0 [appl_27]

kl_shen_load_help :: Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_load_help (!kl_V1487) (!kl_V1488) = do let pat_cond_0 = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_X) -> do !appl_2 <- kl_X `pseq` kl_shen_eval_without_macros kl_X
                                                                                                                               let !aw_3 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                               !appl_4 <- appl_2 `pseq` applyWrapper aw_3 [appl_2,
                                                                                                                                                                           Types.Atom (Types.Str "\n"),
                                                                                                                                                                           Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                               !appl_5 <- kl_stoutput
                                                                                                                               let !aw_6 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                               appl_4 `pseq` (appl_5 `pseq` applyWrapper aw_6 [appl_4,
                                                                                                                                                                               appl_5]))))
                                                                   appl_1 `pseq` (kl_V1488 `pseq` kl_map appl_1 kl_V1488)
                                                   pat_cond_7 = do do let !appl_8 = ApplC (Func "lambda" (Context (\(!kl_RemoveSynonyms) -> do let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_Table) -> do let !appl_10 = ApplC (Func "lambda" (Context (\(!kl_Assume) -> do (do let !appl_11 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_typecheck_and_load kl_X)))
                                                                                                                                                                                                                                                                                     appl_11 `pseq` (kl_RemoveSynonyms `pseq` kl_map appl_11 kl_RemoveSynonyms)) `catchError` (\(!kl_E) -> do kl_E `pseq` (kl_Table `pseq` kl_shen_unwind_types (Excep kl_E) kl_Table)))))
                                                                                                                                                                                                               let !appl_12 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_assumetype kl_X)))
                                                                                                                                                                                                               !appl_13 <- appl_12 `pseq` (kl_Table `pseq` kl_map appl_12 kl_Table)
                                                                                                                                                                                                               appl_13 `pseq` applyWrapper appl_10 [appl_13])))
                                                                                                                                               let !appl_14 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_typetable kl_X)))
                                                                                                                                               !appl_15 <- appl_14 `pseq` (kl_RemoveSynonyms `pseq` kl_mapcan appl_14 kl_RemoveSynonyms)
                                                                                                                                               appl_15 `pseq` applyWrapper appl_9 [appl_15])))
                                                                      let !appl_16 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_remove_synonyms kl_X)))
                                                                      !appl_17 <- appl_16 `pseq` (kl_V1488 `pseq` kl_mapcan appl_16 kl_V1488)
                                                                      appl_17 `pseq` applyWrapper appl_8 [appl_17]
                                                in case kl_V1487 of
                                                       kl_V1487@(Atom (UnboundSym "false")) -> pat_cond_0
                                                       kl_V1487@(Atom (B (False))) -> pat_cond_0
                                                       _ -> pat_cond_7

kl_shen_remove_synonyms :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_remove_synonyms (!kl_V1490) = do let pat_cond_0 kl_V1490 kl_V1490t = do !appl_1 <- kl_V1490 `pseq` kl_eval kl_V1490
                                                                                appl_1 `pseq` kl_do appl_1 (Types.Atom Types.Nil)
                                             pat_cond_2 = do do kl_V1490 `pseq` klCons kl_V1490 (Types.Atom Types.Nil)
                                          in case kl_V1490 of
                                                 !(kl_V1490@(Cons (Atom (UnboundSym "shen.synonyms-help"))
                                                                  (!kl_V1490t))) -> pat_cond_0 kl_V1490 kl_V1490t
                                                 !(kl_V1490@(Cons (ApplC (PL "shen.synonyms-help"
                                                                             _))
                                                                  (!kl_V1490t))) -> pat_cond_0 kl_V1490 kl_V1490t
                                                 !(kl_V1490@(Cons (ApplC (Func "shen.synonyms-help"
                                                                               _))
                                                                  (!kl_V1490t))) -> pat_cond_0 kl_V1490 kl_V1490t
                                                 _ -> pat_cond_2

kl_shen_typecheck_and_load :: Types.KLValue ->
                              Types.KLContext Types.Env Types.KLValue
kl_shen_typecheck_and_load (!kl_V1492) = do !appl_0 <- kl_nl (Types.Atom (Types.N (Types.KI 1)))
                                            !appl_1 <- kl_gensym (Types.Atom (Types.UnboundSym "A"))
                                            !appl_2 <- kl_V1492 `pseq` (appl_1 `pseq` kl_shen_typecheck_and_evaluate kl_V1492 appl_1)
                                            appl_0 `pseq` (appl_2 `pseq` kl_do appl_0 appl_2)

kl_shen_typetable :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_typetable (!kl_V1498) = do let pat_cond_0 kl_V1498 kl_V1498t kl_V1498th kl_V1498tt = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Sig) -> do !appl_2 <- kl_V1498th `pseq` (kl_Sig `pseq` klCons kl_V1498th kl_Sig)
                                                                                                                                                              appl_2 `pseq` klCons appl_2 (Types.Atom Types.Nil))))
                                                                                                let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Y) -> do kl_Y `pseq` kl_shen_LBsigPlusrestRB kl_Y)))
                                                                                                let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_E) -> do let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                            !appl_6 <- kl_V1498th `pseq` applyWrapper aw_5 [kl_V1498th,
                                                                                                                                                                                                            Types.Atom (Types.Str " lacks a proper signature.\n"),
                                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                            appl_6 `pseq` simpleError appl_6)))
                                                                                                !appl_7 <- appl_3 `pseq` (kl_V1498tt `pseq` (appl_4 `pseq` kl_compile appl_3 kl_V1498tt appl_4))
                                                                                                appl_7 `pseq` applyWrapper appl_1 [appl_7]
                                       pat_cond_8 = do do return (Types.Atom Types.Nil)
                                    in case kl_V1498 of
                                           !(kl_V1498@(Cons (Atom (UnboundSym "define"))
                                                            (!(kl_V1498t@(Cons (!kl_V1498th)
                                                                               (!kl_V1498tt)))))) -> pat_cond_0 kl_V1498 kl_V1498t kl_V1498th kl_V1498tt
                                           !(kl_V1498@(Cons (ApplC (PL "define" _))
                                                            (!(kl_V1498t@(Cons (!kl_V1498th)
                                                                               (!kl_V1498tt)))))) -> pat_cond_0 kl_V1498 kl_V1498t kl_V1498th kl_V1498tt
                                           !(kl_V1498@(Cons (ApplC (Func "define" _))
                                                            (!(kl_V1498t@(Cons (!kl_V1498th)
                                                                               (!kl_V1498tt)))))) -> pat_cond_0 kl_V1498 kl_V1498t kl_V1498th kl_V1498tt
                                           _ -> pat_cond_8

kl_shen_assumetype :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_assumetype (!kl_V1500) = do let pat_cond_0 kl_V1500 kl_V1500h kl_V1500t = do let !aw_1 = Types.Atom (Types.UnboundSym "declare")
                                                                                     kl_V1500h `pseq` (kl_V1500t `pseq` applyWrapper aw_1 [kl_V1500h,
                                                                                                                                           kl_V1500t])
                                        pat_cond_2 = do do kl_shen_f_error (ApplC (wrapNamed "shen.assumetype" kl_shen_assumetype))
                                     in case kl_V1500 of
                                            !(kl_V1500@(Cons (!kl_V1500h)
                                                             (!kl_V1500t))) -> pat_cond_0 kl_V1500 kl_V1500h kl_V1500t
                                            _ -> pat_cond_2

kl_shen_unwind_types :: Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_unwind_types (!kl_V1507) (!kl_V1508) = do let pat_cond_0 = do !appl_1 <- kl_V1507 `pseq` errorToString kl_V1507
                                                                      appl_1 `pseq` simpleError appl_1
                                                      pat_cond_2 kl_V1508 kl_V1508h kl_V1508hh kl_V1508ht kl_V1508t = do !appl_3 <- kl_V1508hh `pseq` kl_shen_remtype kl_V1508hh
                                                                                                                         !appl_4 <- kl_V1507 `pseq` (kl_V1508t `pseq` kl_shen_unwind_types kl_V1507 kl_V1508t)
                                                                                                                         appl_3 `pseq` (appl_4 `pseq` kl_do appl_3 appl_4)
                                                      pat_cond_5 = do do kl_shen_f_error (ApplC (wrapNamed "shen.unwind-types" kl_shen_unwind_types))
                                                   in case kl_V1508 of
                                                          kl_V1508@(Atom (Nil)) -> pat_cond_0
                                                          !(kl_V1508@(Cons (!(kl_V1508h@(Cons (!kl_V1508hh)
                                                                                              (!kl_V1508ht))))
                                                                           (!kl_V1508t))) -> pat_cond_2 kl_V1508 kl_V1508h kl_V1508hh kl_V1508ht kl_V1508t
                                                          _ -> pat_cond_5

kl_shen_remtype :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_remtype (!kl_V1510) = do !appl_0 <- value (Types.Atom (Types.UnboundSym "shen.*signedfuncs*"))
                                 !appl_1 <- kl_V1510 `pseq` (appl_0 `pseq` kl_shen_removetype kl_V1510 appl_0)
                                 appl_1 `pseq` klSet (Types.Atom (Types.UnboundSym "shen.*signedfuncs*")) appl_1

kl_shen_removetype :: Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_removetype (!kl_V1518) (!kl_V1519) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                                    pat_cond_1 kl_V1519 kl_V1519h kl_V1519hh kl_V1519ht kl_V1519t = do kl_V1519hh `pseq` (kl_V1519t `pseq` kl_shen_removetype kl_V1519hh kl_V1519t)
                                                    pat_cond_2 kl_V1519 kl_V1519h kl_V1519t = do !appl_3 <- kl_V1518 `pseq` (kl_V1519t `pseq` kl_shen_removetype kl_V1518 kl_V1519t)
                                                                                                 kl_V1519h `pseq` (appl_3 `pseq` klCons kl_V1519h appl_3)
                                                    pat_cond_4 = do do kl_shen_f_error (ApplC (wrapNamed "shen.removetype" kl_shen_removetype))
                                                 in case kl_V1519 of
                                                        kl_V1519@(Atom (Nil)) -> pat_cond_0
                                                        !(kl_V1519@(Cons (!(kl_V1519h@(Cons (!kl_V1519hh)
                                                                                            (!kl_V1519ht))))
                                                                         (!kl_V1519t))) | eqCore kl_V1519hh kl_V1518 -> pat_cond_1 kl_V1519 kl_V1519h kl_V1519hh kl_V1519ht kl_V1519t
                                                        !(kl_V1519@(Cons (!kl_V1519h)
                                                                         (!kl_V1519t))) -> pat_cond_2 kl_V1519 kl_V1519h kl_V1519t
                                                        _ -> pat_cond_4

kl_shen_LBsigPlusrestRB :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_LBsigPlusrestRB (!kl_V1521) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Parse_shen_LBsignatureRB) -> do !appl_1 <- kl_fail
                                                                                                                            !appl_2 <- appl_1 `pseq` (kl_Parse_shen_LBsignatureRB `pseq` eq appl_1 kl_Parse_shen_LBsignatureRB)
                                                                                                                            !kl_if_3 <- appl_2 `pseq` kl_not appl_2
                                                                                                                            case kl_if_3 of
                                                                                                                                Atom (B (True)) -> do let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_Parse_shen_LBExclRB) -> do !appl_5 <- kl_fail
                                                                                                                                                                                                                                    !appl_6 <- appl_5 `pseq` (kl_Parse_shen_LBExclRB `pseq` eq appl_5 kl_Parse_shen_LBExclRB)
                                                                                                                                                                                                                                    !kl_if_7 <- appl_6 `pseq` kl_not appl_6
                                                                                                                                                                                                                                    case kl_if_7 of
                                                                                                                                                                                                                                        Atom (B (True)) -> do !appl_8 <- kl_Parse_shen_LBExclRB `pseq` hd kl_Parse_shen_LBExclRB
                                                                                                                                                                                                                                                              !appl_9 <- kl_Parse_shen_LBsignatureRB `pseq` kl_shen_hdtl kl_Parse_shen_LBsignatureRB
                                                                                                                                                                                                                                                              appl_8 `pseq` (appl_9 `pseq` kl_shen_pair appl_8 appl_9)
                                                                                                                                                                                                                                        Atom (B (False)) -> do do kl_fail
                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean")))
                                                                                                                                                      !appl_10 <- kl_Parse_shen_LBsignatureRB `pseq` kl_shen_LBExclRB kl_Parse_shen_LBsignatureRB
                                                                                                                                                      appl_10 `pseq` applyWrapper appl_4 [appl_10]
                                                                                                                                Atom (B (False)) -> do do kl_fail
                                                                                                                                _ -> throwError "if: expected boolean")))
                                         !appl_11 <- kl_V1521 `pseq` kl_shen_LBsignatureRB kl_V1521
                                         appl_11 `pseq` applyWrapper appl_0 [appl_11]

kl_write_to_file :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_write_to_file (!kl_V1524) (!kl_V1525) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Stream) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Write) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Close) -> do return kl_V1525)))
                                                                                                                                                                                                                                                !appl_4 <- kl_Stream `pseq` closeStream kl_Stream
                                                                                                                                                                                                                                                appl_4 `pseq` applyWrapper appl_3 [appl_4])))
                                                                                                                                                                                let !aw_5 = Types.Atom (Types.UnboundSym "pr")
                                                                                                                                                                                !appl_6 <- kl_String `pseq` (kl_Stream `pseq` applyWrapper aw_5 [kl_String,
                                                                                                                                                                                                                                                 kl_Stream])
                                                                                                                                                                                appl_6 `pseq` applyWrapper appl_2 [appl_6])))
                                                                                                               !kl_if_7 <- kl_V1525 `pseq` stringP kl_V1525
                                                                                                               !appl_8 <- case kl_if_7 of
                                                                                                                              Atom (B (True)) -> do let !aw_9 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                    kl_V1525 `pseq` applyWrapper aw_9 [kl_V1525,
                                                                                                                                                                                       Types.Atom (Types.Str "\n\n"),
                                                                                                                                                                                       Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                              Atom (B (False)) -> do do let !aw_10 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                        kl_V1525 `pseq` applyWrapper aw_10 [kl_V1525,
                                                                                                                                                                                            Types.Atom (Types.Str "\n\n"),
                                                                                                                                                                                            Types.Atom (Types.UnboundSym "shen.s")]
                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                               appl_8 `pseq` applyWrapper appl_1 [appl_8])))
                                              !appl_11 <- kl_V1524 `pseq` openStream kl_V1524 (Types.Atom (Types.UnboundSym "out"))
                                              appl_11 `pseq` applyWrapper appl_0 [appl_11]

expr8 :: Types.KLContext Types.Env Types.KLValue
expr8 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
