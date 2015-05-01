{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Backend.Writer where

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

kl_pr :: Types.KLValue ->
         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_pr (!kl_V3878) (!kl_V3879) = do (do kl_V3878 `pseq` (kl_V3879 `pseq` kl_shen_prh kl_V3878 kl_V3879 (Types.Atom (Types.N (Types.KI 0))))) `catchError` (\(!kl_E) -> do return kl_V3878)

kl_shen_prh :: Types.KLValue ->
               Types.KLValue ->
               Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_prh (!kl_V3883) (!kl_V3884) (!kl_V3885) = do !appl_0 <- kl_V3883 `pseq` (kl_V3884 `pseq` (kl_V3885 `pseq` kl_shen_write_char_and_inc kl_V3883 kl_V3884 kl_V3885))
                                                     kl_V3883 `pseq` (kl_V3884 `pseq` (appl_0 `pseq` kl_shen_prh kl_V3883 kl_V3884 appl_0))

kl_shen_write_char_and_inc :: Types.KLValue ->
                              Types.KLValue ->
                              Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_write_char_and_inc (!kl_V3889) (!kl_V3890) (!kl_V3891) = do !appl_0 <- kl_V3889 `pseq` (kl_V3891 `pseq` pos kl_V3889 kl_V3891)
                                                                    !appl_1 <- appl_0 `pseq` stringToN appl_0
                                                                    !appl_2 <- appl_1 `pseq` (kl_V3890 `pseq` writeByte appl_1 kl_V3890)
                                                                    !appl_3 <- kl_V3891 `pseq` add kl_V3891 (Types.Atom (Types.N (Types.KI 1)))
                                                                    appl_2 `pseq` (appl_3 `pseq` kl_do appl_2 appl_3)

kl_print :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_print (!kl_V3893) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Print) -> do return kl_V3893)))
                                                                                           !appl_2 <- kl_stoutput
                                                                                           !appl_3 <- kl_String `pseq` (appl_2 `pseq` kl_shen_prhush kl_String appl_2)
                                                                                           appl_3 `pseq` applyWrapper appl_1 [appl_3])))
                          !appl_4 <- kl_V3893 `pseq` kl_shen_insert kl_V3893 (Types.Atom (Types.Str "~S"))
                          appl_4 `pseq` applyWrapper appl_0 [appl_4]

kl_shen_prhush :: Types.KLValue ->
                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_prhush (!kl_V3896) (!kl_V3897) = do !kl_if_0 <- value (Types.Atom (Types.UnboundSym "*hush*"))
                                            case kl_if_0 of
                                                Atom (B (True)) -> do return kl_V3896
                                                Atom (B (False)) -> do do kl_V3896 `pseq` (kl_V3897 `pseq` kl_pr kl_V3896 kl_V3897)
                                                _ -> throwError "if: expected boolean"

kl_shen_mkstr :: Types.KLValue ->
                 Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mkstr (!kl_V3900) (!kl_V3901) = do !kl_if_0 <- kl_V3900 `pseq` stringP kl_V3900
                                           case kl_if_0 of
                                               Atom (B (True)) -> do !appl_1 <- kl_V3900 `pseq` kl_shen_proc_nl kl_V3900
                                                                     appl_1 `pseq` (kl_V3901 `pseq` kl_shen_mkstr_l appl_1 kl_V3901)
                                               Atom (B (False)) -> do do !appl_2 <- kl_V3900 `pseq` klCons kl_V3900 (Types.Atom Types.Nil)
                                                                         !appl_3 <- appl_2 `pseq` klCons (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl)) appl_2
                                                                         appl_3 `pseq` (kl_V3901 `pseq` kl_shen_mkstr_r appl_3 kl_V3901)
                                               _ -> throwError "if: expected boolean"

kl_shen_mkstr_l :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mkstr_l (!kl_V3904) (!kl_V3905) = do let pat_cond_0 = do return kl_V3904
                                                 pat_cond_1 kl_V3905 kl_V3905h kl_V3905t = do !appl_2 <- kl_V3905h `pseq` (kl_V3904 `pseq` kl_shen_insert_l kl_V3905h kl_V3904)
                                                                                              appl_2 `pseq` (kl_V3905t `pseq` kl_shen_mkstr_l appl_2 kl_V3905t)
                                                 pat_cond_3 = do do kl_shen_f_error (ApplC (wrapNamed "shen.mkstr-l" kl_shen_mkstr_l))
                                              in case kl_V3905 of
                                                     kl_V3905@(Atom (Nil)) -> pat_cond_0
                                                     !(kl_V3905@(Cons (!kl_V3905h)
                                                                      (!kl_V3905t))) -> pat_cond_1 kl_V3905 kl_V3905h kl_V3905t
                                                     _ -> pat_cond_3

kl_shen_insert_l :: Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert_l (!kl_V3910) (!kl_V3911) = do let pat_cond_0 = do return (Types.Atom (Types.Str ""))
                                                  pat_cond_1 = do !kl_if_2 <- kl_V3911 `pseq` kl_shen_PlusstringP kl_V3911
                                                                  !kl_if_3 <- case kl_if_2 of
                                                                                  Atom (B (True)) -> do !appl_4 <- kl_V3911 `pseq` pos kl_V3911 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                        !kl_if_5 <- appl_4 `pseq` eq (Types.Atom (Types.Str "~")) appl_4
                                                                                                        !kl_if_6 <- case kl_if_5 of
                                                                                                                        Atom (B (True)) -> do !appl_7 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                              !kl_if_8 <- appl_7 `pseq` kl_shen_PlusstringP appl_7
                                                                                                                                              !kl_if_9 <- case kl_if_8 of
                                                                                                                                                              Atom (B (True)) -> do !appl_10 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                                                    !appl_11 <- appl_10 `pseq` pos appl_10 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                    !kl_if_12 <- appl_11 `pseq` eq (Types.Atom (Types.Str "A")) appl_11
                                                                                                                                                                                    case kl_if_12 of
                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                              case kl_if_9 of
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
                                                                  case kl_if_3 of
                                                                      Atom (B (True)) -> do !appl_13 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                            !appl_14 <- appl_13 `pseq` tlstr appl_13
                                                                                            !appl_15 <- klCons (Types.Atom (Types.UnboundSym "shen.a")) (Types.Atom Types.Nil)
                                                                                            !appl_16 <- appl_14 `pseq` (appl_15 `pseq` klCons appl_14 appl_15)
                                                                                            !appl_17 <- kl_V3910 `pseq` (appl_16 `pseq` klCons kl_V3910 appl_16)
                                                                                            appl_17 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_17
                                                                      Atom (B (False)) -> do !kl_if_18 <- kl_V3911 `pseq` kl_shen_PlusstringP kl_V3911
                                                                                             !kl_if_19 <- case kl_if_18 of
                                                                                                              Atom (B (True)) -> do !appl_20 <- kl_V3911 `pseq` pos kl_V3911 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                    !kl_if_21 <- appl_20 `pseq` eq (Types.Atom (Types.Str "~")) appl_20
                                                                                                                                    !kl_if_22 <- case kl_if_21 of
                                                                                                                                                     Atom (B (True)) -> do !appl_23 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                                           !kl_if_24 <- appl_23 `pseq` kl_shen_PlusstringP appl_23
                                                                                                                                                                           !kl_if_25 <- case kl_if_24 of
                                                                                                                                                                                            Atom (B (True)) -> do !appl_26 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                                                                                  !appl_27 <- appl_26 `pseq` pos appl_26 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                                                  !kl_if_28 <- appl_27 `pseq` eq (Types.Atom (Types.Str "R")) appl_27
                                                                                                                                                                                                                  case kl_if_28 of
                                                                                                                                                                                                                      Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                      Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                      _ -> throwError "if: expected boolean"
                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                           case kl_if_25 of
                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                     Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                    case kl_if_22 of
                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                              _ -> throwError "if: expected boolean"
                                                                                             case kl_if_19 of
                                                                                                 Atom (B (True)) -> do !appl_29 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                       !appl_30 <- appl_29 `pseq` tlstr appl_29
                                                                                                                       !appl_31 <- klCons (Types.Atom (Types.UnboundSym "shen.r")) (Types.Atom Types.Nil)
                                                                                                                       !appl_32 <- appl_30 `pseq` (appl_31 `pseq` klCons appl_30 appl_31)
                                                                                                                       !appl_33 <- kl_V3910 `pseq` (appl_32 `pseq` klCons kl_V3910 appl_32)
                                                                                                                       appl_33 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_33
                                                                                                 Atom (B (False)) -> do !kl_if_34 <- kl_V3911 `pseq` kl_shen_PlusstringP kl_V3911
                                                                                                                        !kl_if_35 <- case kl_if_34 of
                                                                                                                                         Atom (B (True)) -> do !appl_36 <- kl_V3911 `pseq` pos kl_V3911 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                               !kl_if_37 <- appl_36 `pseq` eq (Types.Atom (Types.Str "~")) appl_36
                                                                                                                                                               !kl_if_38 <- case kl_if_37 of
                                                                                                                                                                                Atom (B (True)) -> do !appl_39 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                                                                      !kl_if_40 <- appl_39 `pseq` kl_shen_PlusstringP appl_39
                                                                                                                                                                                                      !kl_if_41 <- case kl_if_40 of
                                                                                                                                                                                                                       Atom (B (True)) -> do !appl_42 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                                                                                                             !appl_43 <- appl_42 `pseq` pos appl_42 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                                                                             !kl_if_44 <- appl_43 `pseq` eq (Types.Atom (Types.Str "S")) appl_43
                                                                                                                                                                                                                                             case kl_if_44 of
                                                                                                                                                                                                                                                 Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                                                      case kl_if_41 of
                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                                               case kl_if_38 of
                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                        case kl_if_35 of
                                                                                                                            Atom (B (True)) -> do !appl_45 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                  !appl_46 <- appl_45 `pseq` tlstr appl_45
                                                                                                                                                  !appl_47 <- klCons (Types.Atom (Types.UnboundSym "shen.s")) (Types.Atom Types.Nil)
                                                                                                                                                  !appl_48 <- appl_46 `pseq` (appl_47 `pseq` klCons appl_46 appl_47)
                                                                                                                                                  !appl_49 <- kl_V3910 `pseq` (appl_48 `pseq` klCons kl_V3910 appl_48)
                                                                                                                                                  appl_49 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_49
                                                                                                                            Atom (B (False)) -> do !kl_if_50 <- kl_V3911 `pseq` kl_shen_PlusstringP kl_V3911
                                                                                                                                                   case kl_if_50 of
                                                                                                                                                       Atom (B (True)) -> do !appl_51 <- kl_V3911 `pseq` pos kl_V3911 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                             !appl_52 <- kl_V3911 `pseq` tlstr kl_V3911
                                                                                                                                                                             !appl_53 <- kl_V3910 `pseq` (appl_52 `pseq` kl_shen_insert_l kl_V3910 appl_52)
                                                                                                                                                                             !appl_54 <- appl_53 `pseq` klCons appl_53 (Types.Atom Types.Nil)
                                                                                                                                                                             !appl_55 <- appl_51 `pseq` (appl_54 `pseq` klCons appl_51 appl_54)
                                                                                                                                                                             !appl_56 <- appl_55 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_55
                                                                                                                                                                             appl_56 `pseq` kl_shen_factor_cn appl_56
                                                                                                                                                       Atom (B (False)) -> do let pat_cond_57 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth = do !appl_58 <- kl_V3910 `pseq` (kl_V3911tth `pseq` kl_shen_insert_l kl_V3910 kl_V3911tth)
                                                                                                                                                                                                                                                        !appl_59 <- appl_58 `pseq` klCons appl_58 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                        !appl_60 <- kl_V3911th `pseq` (appl_59 `pseq` klCons kl_V3911th appl_59)
                                                                                                                                                                                                                                                        appl_60 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_60
                                                                                                                                                                                  pat_cond_61 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth kl_V3911ttt kl_V3911ttth = do !appl_62 <- kl_V3910 `pseq` (kl_V3911tth `pseq` kl_shen_insert_l kl_V3910 kl_V3911tth)
                                                                                                                                                                                                                                                                                 !appl_63 <- appl_62 `pseq` (kl_V3911ttt `pseq` klCons appl_62 kl_V3911ttt)
                                                                                                                                                                                                                                                                                 !appl_64 <- kl_V3911th `pseq` (appl_63 `pseq` klCons kl_V3911th appl_63)
                                                                                                                                                                                                                                                                                 appl_64 `pseq` klCons (ApplC (wrapNamed "shen.app" kl_shen_app)) appl_64
                                                                                                                                                                                  pat_cond_65 = do do kl_shen_f_error (ApplC (wrapNamed "shen.insert-l" kl_shen_insert_l))
                                                                                                                                                                               in case kl_V3911 of
                                                                                                                                                                                      !(kl_V3911@(Cons (Atom (UnboundSym "cn"))
                                                                                                                                                                                                       (!(kl_V3911t@(Cons (!kl_V3911th)
                                                                                                                                                                                                                          (!(kl_V3911tt@(Cons (!kl_V3911tth)
                                                                                                                                                                                                                                              (Atom (Nil)))))))))) -> pat_cond_57 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth
                                                                                                                                                                                      !(kl_V3911@(Cons (ApplC (PL "cn"
                                                                                                                                                                                                                  _))
                                                                                                                                                                                                       (!(kl_V3911t@(Cons (!kl_V3911th)
                                                                                                                                                                                                                          (!(kl_V3911tt@(Cons (!kl_V3911tth)
                                                                                                                                                                                                                                              (Atom (Nil)))))))))) -> pat_cond_57 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth
                                                                                                                                                                                      !(kl_V3911@(Cons (ApplC (Func "cn"
                                                                                                                                                                                                                    _))
                                                                                                                                                                                                       (!(kl_V3911t@(Cons (!kl_V3911th)
                                                                                                                                                                                                                          (!(kl_V3911tt@(Cons (!kl_V3911tth)
                                                                                                                                                                                                                                              (Atom (Nil)))))))))) -> pat_cond_57 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth
                                                                                                                                                                                      !(kl_V3911@(Cons (Atom (UnboundSym "shen.app"))
                                                                                                                                                                                                       (!(kl_V3911t@(Cons (!kl_V3911th)
                                                                                                                                                                                                                          (!(kl_V3911tt@(Cons (!kl_V3911tth)
                                                                                                                                                                                                                                              (!(kl_V3911ttt@(Cons (!kl_V3911ttth)
                                                                                                                                                                                                                                                                   (Atom (Nil))))))))))))) -> pat_cond_61 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth kl_V3911ttt kl_V3911ttth
                                                                                                                                                                                      !(kl_V3911@(Cons (ApplC (PL "shen.app"
                                                                                                                                                                                                                  _))
                                                                                                                                                                                                       (!(kl_V3911t@(Cons (!kl_V3911th)
                                                                                                                                                                                                                          (!(kl_V3911tt@(Cons (!kl_V3911tth)
                                                                                                                                                                                                                                              (!(kl_V3911ttt@(Cons (!kl_V3911ttth)
                                                                                                                                                                                                                                                                   (Atom (Nil))))))))))))) -> pat_cond_61 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth kl_V3911ttt kl_V3911ttth
                                                                                                                                                                                      !(kl_V3911@(Cons (ApplC (Func "shen.app"
                                                                                                                                                                                                                    _))
                                                                                                                                                                                                       (!(kl_V3911t@(Cons (!kl_V3911th)
                                                                                                                                                                                                                          (!(kl_V3911tt@(Cons (!kl_V3911tth)
                                                                                                                                                                                                                                              (!(kl_V3911ttt@(Cons (!kl_V3911ttth)
                                                                                                                                                                                                                                                                   (Atom (Nil))))))))))))) -> pat_cond_61 kl_V3911 kl_V3911t kl_V3911th kl_V3911tt kl_V3911tth kl_V3911ttt kl_V3911ttth
                                                                                                                                                                                      _ -> pat_cond_65
                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                 _ -> throwError "if: expected boolean"
                                                                      _ -> throwError "if: expected boolean"
                                               in case kl_V3911 of
                                                      kl_V3911@(Atom (Str "")) -> pat_cond_0
                                                      _ -> pat_cond_1

kl_shen_factor_cn :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_factor_cn (!kl_V3913) = do !kl_if_0 <- let pat_cond_1 kl_V3913 kl_V3913h kl_V3913t = do !kl_if_2 <- let pat_cond_3 = do !kl_if_4 <- let pat_cond_5 kl_V3913t kl_V3913th kl_V3913tt = do !kl_if_6 <- let pat_cond_7 kl_V3913tt kl_V3913tth kl_V3913ttt = do !kl_if_8 <- let pat_cond_9 kl_V3913tth kl_V3913tthh kl_V3913ttht = do !kl_if_10 <- let pat_cond_11 = do !kl_if_12 <- let pat_cond_13 kl_V3913ttht kl_V3913tthth kl_V3913tthtt = do !kl_if_14 <- let pat_cond_15 kl_V3913tthtt kl_V3913tthtth kl_V3913tthttt = do !kl_if_16 <- let pat_cond_17 = do !kl_if_18 <- let pat_cond_19 = do !kl_if_20 <- kl_V3913th `pseq` stringP kl_V3913th
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        !kl_if_21 <- case kl_if_20 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Atom (B (True)) -> do !kl_if_22 <- kl_V3913tthth `pseq` stringP kl_V3913tthth
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               case kl_if_22 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        case kl_if_21 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       pat_cond_23 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    in case kl_V3913ttt of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           kl_V3913ttt@(Atom (Nil)) -> pat_cond_19
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           _ -> pat_cond_23
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      case kl_if_18 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     pat_cond_24 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  in case kl_V3913tthttt of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         kl_V3913tthttt@(Atom (Nil)) -> pat_cond_17
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         _ -> pat_cond_24
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    case kl_if_16 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                                                                                                       pat_cond_25 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                    in case kl_V3913tthtt of
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           !(kl_V3913tthtt@(Cons (!kl_V3913tthtth)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (!kl_V3913tthttt))) -> pat_cond_15 kl_V3913tthtt kl_V3913tthtth kl_V3913tthttt
                                                                                                                                                                                                                                                                                                                                                                                                                                                                           _ -> pat_cond_25
                                                                                                                                                                                                                                                                                                                                                                                                                                                      case kl_if_14 of
                                                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                                                            pat_cond_26 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                                         in case kl_V3913ttht of
                                                                                                                                                                                                                                                                                                                                                                                                !(kl_V3913ttht@(Cons (!kl_V3913tthth)
                                                                                                                                                                                                                                                                                                                                                                                                                     (!kl_V3913tthtt))) -> pat_cond_13 kl_V3913ttht kl_V3913tthth kl_V3913tthtt
                                                                                                                                                                                                                                                                                                                                                                                                _ -> pat_cond_26
                                                                                                                                                                                                                                                                                                                                                                           case kl_if_12 of
                                                                                                                                                                                                                                                                                                                                                                               Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                                                               Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                                               _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                                                                                          pat_cond_27 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                                       in case kl_V3913tthh of
                                                                                                                                                                                                                                                                                                                                                              kl_V3913tthh@(Atom (UnboundSym "cn")) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                                              kl_V3913tthh@(ApplC (PL "cn"
                                                                                                                                                                                                                                                                                                                                                                                      _)) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                                              kl_V3913tthh@(ApplC (Func "cn"
                                                                                                                                                                                                                                                                                                                                                                                        _)) -> pat_cond_11
                                                                                                                                                                                                                                                                                                                                                              _ -> pat_cond_27
                                                                                                                                                                                                                                                                                                                                         case kl_if_10 of
                                                                                                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                                                                   pat_cond_28 = do do return (Atom (B False))
                                                                                                                                                                                                                                                                                in case kl_V3913tth of
                                                                                                                                                                                                                                                                                       !(kl_V3913tth@(Cons (!kl_V3913tthh)
                                                                                                                                                                                                                                                                                                           (!kl_V3913ttht))) -> pat_cond_9 kl_V3913tth kl_V3913tthh kl_V3913ttht
                                                                                                                                                                                                                                                                                       _ -> pat_cond_28
                                                                                                                                                                                                                                                                   case kl_if_8 of
                                                                                                                                                                                                                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                pat_cond_29 = do do return (Atom (B False))
                                                                                                                                                                                                             in case kl_V3913tt of
                                                                                                                                                                                                                    !(kl_V3913tt@(Cons (!kl_V3913tth)
                                                                                                                                                                                                                                       (!kl_V3913ttt))) -> pat_cond_7 kl_V3913tt kl_V3913tth kl_V3913ttt
                                                                                                                                                                                                                    _ -> pat_cond_29
                                                                                                                                                                                                case kl_if_6 of
                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                pat_cond_30 = do do return (Atom (B False))
                                                                                                                                             in case kl_V3913t of
                                                                                                                                                    !(kl_V3913t@(Cons (!kl_V3913th)
                                                                                                                                                                      (!kl_V3913tt))) -> pat_cond_5 kl_V3913t kl_V3913th kl_V3913tt
                                                                                                                                                    _ -> pat_cond_30
                                                                                                                                case kl_if_4 of
                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                pat_cond_31 = do do return (Atom (B False))
                                                                                                             in case kl_V3913h of
                                                                                                                    kl_V3913h@(Atom (UnboundSym "cn")) -> pat_cond_3
                                                                                                                    kl_V3913h@(ApplC (PL "cn"
                                                                                                                                         _)) -> pat_cond_3
                                                                                                                    kl_V3913h@(ApplC (Func "cn"
                                                                                                                                           _)) -> pat_cond_3
                                                                                                                    _ -> pat_cond_31
                                                                                                case kl_if_2 of
                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                    _ -> throwError "if: expected boolean"
                                                   pat_cond_32 = do do return (Atom (B False))
                                                in case kl_V3913 of
                                                       !(kl_V3913@(Cons (!kl_V3913h)
                                                                        (!kl_V3913t))) -> pat_cond_1 kl_V3913 kl_V3913h kl_V3913t
                                                       _ -> pat_cond_32
                                   case kl_if_0 of
                                       Atom (B (True)) -> do !appl_33 <- kl_V3913 `pseq` tl kl_V3913
                                                             !appl_34 <- appl_33 `pseq` hd appl_33
                                                             !appl_35 <- kl_V3913 `pseq` tl kl_V3913
                                                             !appl_36 <- appl_35 `pseq` tl appl_35
                                                             !appl_37 <- appl_36 `pseq` hd appl_36
                                                             !appl_38 <- appl_37 `pseq` tl appl_37
                                                             !appl_39 <- appl_38 `pseq` hd appl_38
                                                             !appl_40 <- appl_34 `pseq` (appl_39 `pseq` cn appl_34 appl_39)
                                                             !appl_41 <- kl_V3913 `pseq` tl kl_V3913
                                                             !appl_42 <- appl_41 `pseq` tl appl_41
                                                             !appl_43 <- appl_42 `pseq` hd appl_42
                                                             !appl_44 <- appl_43 `pseq` tl appl_43
                                                             !appl_45 <- appl_44 `pseq` tl appl_44
                                                             !appl_46 <- appl_40 `pseq` (appl_45 `pseq` klCons appl_40 appl_45)
                                                             appl_46 `pseq` klCons (ApplC (wrapNamed "cn" cn)) appl_46
                                       Atom (B (False)) -> do do return kl_V3913
                                       _ -> throwError "if: expected boolean"

kl_shen_proc_nl :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_proc_nl (!kl_V3915) = do let pat_cond_0 = do return (Types.Atom (Types.Str ""))
                                     pat_cond_1 = do !kl_if_2 <- kl_V3915 `pseq` kl_shen_PlusstringP kl_V3915
                                                     !kl_if_3 <- case kl_if_2 of
                                                                     Atom (B (True)) -> do !appl_4 <- kl_V3915 `pseq` pos kl_V3915 (Types.Atom (Types.N (Types.KI 0)))
                                                                                           !kl_if_5 <- appl_4 `pseq` eq (Types.Atom (Types.Str "~")) appl_4
                                                                                           !kl_if_6 <- case kl_if_5 of
                                                                                                           Atom (B (True)) -> do !appl_7 <- kl_V3915 `pseq` tlstr kl_V3915
                                                                                                                                 !kl_if_8 <- appl_7 `pseq` kl_shen_PlusstringP appl_7
                                                                                                                                 !kl_if_9 <- case kl_if_8 of
                                                                                                                                                 Atom (B (True)) -> do !appl_10 <- kl_V3915 `pseq` tlstr kl_V3915
                                                                                                                                                                       !appl_11 <- appl_10 `pseq` pos appl_10 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                       !kl_if_12 <- appl_11 `pseq` eq (Types.Atom (Types.Str "%")) appl_11
                                                                                                                                                                       case kl_if_12 of
                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                 case kl_if_9 of
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
                                                     case kl_if_3 of
                                                         Atom (B (True)) -> do !appl_13 <- nToString (Types.Atom (Types.N (Types.KI 10)))
                                                                               !appl_14 <- kl_V3915 `pseq` tlstr kl_V3915
                                                                               !appl_15 <- appl_14 `pseq` tlstr appl_14
                                                                               !appl_16 <- appl_15 `pseq` kl_shen_proc_nl appl_15
                                                                               appl_13 `pseq` (appl_16 `pseq` cn appl_13 appl_16)
                                                         Atom (B (False)) -> do !kl_if_17 <- kl_V3915 `pseq` kl_shen_PlusstringP kl_V3915
                                                                                case kl_if_17 of
                                                                                    Atom (B (True)) -> do !appl_18 <- kl_V3915 `pseq` pos kl_V3915 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                          !appl_19 <- kl_V3915 `pseq` tlstr kl_V3915
                                                                                                          !appl_20 <- appl_19 `pseq` kl_shen_proc_nl appl_19
                                                                                                          appl_18 `pseq` (appl_20 `pseq` cn appl_18 appl_20)
                                                                                    Atom (B (False)) -> do do kl_shen_f_error (ApplC (wrapNamed "shen.proc-nl" kl_shen_proc_nl))
                                                                                    _ -> throwError "if: expected boolean"
                                                         _ -> throwError "if: expected boolean"
                                  in case kl_V3915 of
                                         kl_V3915@(Atom (Str "")) -> pat_cond_0
                                         _ -> pat_cond_1

kl_shen_mkstr_r :: Types.KLValue ->
                   Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_mkstr_r (!kl_V3918) (!kl_V3919) = do let pat_cond_0 = do return kl_V3918
                                                 pat_cond_1 kl_V3919 kl_V3919h kl_V3919t = do !appl_2 <- kl_V3918 `pseq` klCons kl_V3918 (Types.Atom Types.Nil)
                                                                                              !appl_3 <- kl_V3919h `pseq` (appl_2 `pseq` klCons kl_V3919h appl_2)
                                                                                              !appl_4 <- appl_3 `pseq` klCons (ApplC (wrapNamed "shen.insert" kl_shen_insert)) appl_3
                                                                                              appl_4 `pseq` (kl_V3919t `pseq` kl_shen_mkstr_r appl_4 kl_V3919t)
                                                 pat_cond_5 = do do kl_shen_f_error (ApplC (wrapNamed "shen.mkstr-r" kl_shen_mkstr_r))
                                              in case kl_V3919 of
                                                     kl_V3919@(Atom (Nil)) -> pat_cond_0
                                                     !(kl_V3919@(Cons (!kl_V3919h)
                                                                      (!kl_V3919t))) -> pat_cond_1 kl_V3919 kl_V3919h kl_V3919t
                                                     _ -> pat_cond_5

kl_shen_insert :: Types.KLValue ->
                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert (!kl_V3922) (!kl_V3923) = do kl_V3922 `pseq` (kl_V3923 `pseq` kl_shen_insert_h kl_V3922 kl_V3923 (Types.Atom (Types.Str "")))

kl_shen_insert_h :: Types.KLValue ->
                    Types.KLValue ->
                    Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert_h (!kl_V3929) (!kl_V3930) (!kl_V3931) = do let pat_cond_0 = do return kl_V3931
                                                              pat_cond_1 = do !kl_if_2 <- kl_V3930 `pseq` kl_shen_PlusstringP kl_V3930
                                                                              !kl_if_3 <- case kl_if_2 of
                                                                                              Atom (B (True)) -> do !appl_4 <- kl_V3930 `pseq` pos kl_V3930 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                    !kl_if_5 <- appl_4 `pseq` eq (Types.Atom (Types.Str "~")) appl_4
                                                                                                                    !kl_if_6 <- case kl_if_5 of
                                                                                                                                    Atom (B (True)) -> do !appl_7 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                          !kl_if_8 <- appl_7 `pseq` kl_shen_PlusstringP appl_7
                                                                                                                                                          !kl_if_9 <- case kl_if_8 of
                                                                                                                                                                          Atom (B (True)) -> do !appl_10 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                                                                !appl_11 <- appl_10 `pseq` pos appl_10 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                                !kl_if_12 <- appl_11 `pseq` eq (Types.Atom (Types.Str "A")) appl_11
                                                                                                                                                                                                case kl_if_12 of
                                                                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                                                                          case kl_if_9 of
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
                                                                              case kl_if_3 of
                                                                                  Atom (B (True)) -> do !appl_13 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                        !appl_14 <- appl_13 `pseq` tlstr appl_13
                                                                                                        !appl_15 <- kl_V3929 `pseq` (appl_14 `pseq` kl_shen_app kl_V3929 appl_14 (Types.Atom (Types.UnboundSym "shen.a")))
                                                                                                        kl_V3931 `pseq` (appl_15 `pseq` cn kl_V3931 appl_15)
                                                                                  Atom (B (False)) -> do !kl_if_16 <- kl_V3930 `pseq` kl_shen_PlusstringP kl_V3930
                                                                                                         !kl_if_17 <- case kl_if_16 of
                                                                                                                          Atom (B (True)) -> do !appl_18 <- kl_V3930 `pseq` pos kl_V3930 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                !kl_if_19 <- appl_18 `pseq` eq (Types.Atom (Types.Str "~")) appl_18
                                                                                                                                                !kl_if_20 <- case kl_if_19 of
                                                                                                                                                                 Atom (B (True)) -> do !appl_21 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                                                       !kl_if_22 <- appl_21 `pseq` kl_shen_PlusstringP appl_21
                                                                                                                                                                                       !kl_if_23 <- case kl_if_22 of
                                                                                                                                                                                                        Atom (B (True)) -> do !appl_24 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                                                                                              !appl_25 <- appl_24 `pseq` pos appl_24 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                                                              !kl_if_26 <- appl_25 `pseq` eq (Types.Atom (Types.Str "R")) appl_25
                                                                                                                                                                                                                              case kl_if_26 of
                                                                                                                                                                                                                                  Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                  Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                  _ -> throwError "if: expected boolean"
                                                                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                                                                                       case kl_if_23 of
                                                                                                                                                                                           Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                           Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                           _ -> throwError "if: expected boolean"
                                                                                                                                                                 Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                 _ -> throwError "if: expected boolean"
                                                                                                                                                case kl_if_20 of
                                                                                                                                                    Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                                          Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                          _ -> throwError "if: expected boolean"
                                                                                                         case kl_if_17 of
                                                                                                             Atom (B (True)) -> do !appl_27 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                   !appl_28 <- appl_27 `pseq` tlstr appl_27
                                                                                                                                   !appl_29 <- kl_V3929 `pseq` (appl_28 `pseq` kl_shen_app kl_V3929 appl_28 (Types.Atom (Types.UnboundSym "shen.r")))
                                                                                                                                   kl_V3931 `pseq` (appl_29 `pseq` cn kl_V3931 appl_29)
                                                                                                             Atom (B (False)) -> do !kl_if_30 <- kl_V3930 `pseq` kl_shen_PlusstringP kl_V3930
                                                                                                                                    !kl_if_31 <- case kl_if_30 of
                                                                                                                                                     Atom (B (True)) -> do !appl_32 <- kl_V3930 `pseq` pos kl_V3930 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                           !kl_if_33 <- appl_32 `pseq` eq (Types.Atom (Types.Str "~")) appl_32
                                                                                                                                                                           !kl_if_34 <- case kl_if_33 of
                                                                                                                                                                                            Atom (B (True)) -> do !appl_35 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                                                                                  !kl_if_36 <- appl_35 `pseq` kl_shen_PlusstringP appl_35
                                                                                                                                                                                                                  !kl_if_37 <- case kl_if_36 of
                                                                                                                                                                                                                                   Atom (B (True)) -> do !appl_38 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                                                                                                                         !appl_39 <- appl_38 `pseq` pos appl_38 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                                                                                         !kl_if_40 <- appl_39 `pseq` eq (Types.Atom (Types.Str "S")) appl_39
                                                                                                                                                                                                                                                         case kl_if_40 of
                                                                                                                                                                                                                                                             Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                                                                                                             Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                                             _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                                   Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                                  case kl_if_37 of
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
                                                                                                                                    case kl_if_31 of
                                                                                                                                        Atom (B (True)) -> do !appl_41 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                              !appl_42 <- appl_41 `pseq` tlstr appl_41
                                                                                                                                                              !appl_43 <- kl_V3929 `pseq` (appl_42 `pseq` kl_shen_app kl_V3929 appl_42 (Types.Atom (Types.UnboundSym "shen.s")))
                                                                                                                                                              kl_V3931 `pseq` (appl_43 `pseq` cn kl_V3931 appl_43)
                                                                                                                                        Atom (B (False)) -> do !kl_if_44 <- kl_V3930 `pseq` kl_shen_PlusstringP kl_V3930
                                                                                                                                                               case kl_if_44 of
                                                                                                                                                                   Atom (B (True)) -> do !appl_45 <- kl_V3930 `pseq` tlstr kl_V3930
                                                                                                                                                                                         !appl_46 <- kl_V3930 `pseq` pos kl_V3930 (Types.Atom (Types.N (Types.KI 0)))
                                                                                                                                                                                         !appl_47 <- kl_V3931 `pseq` (appl_46 `pseq` cn kl_V3931 appl_46)
                                                                                                                                                                                         kl_V3929 `pseq` (appl_45 `pseq` (appl_47 `pseq` kl_shen_insert_h kl_V3929 appl_45 appl_47))
                                                                                                                                                                   Atom (B (False)) -> do do kl_shen_f_error (ApplC (wrapNamed "shen.insert-h" kl_shen_insert_h))
                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                             _ -> throwError "if: expected boolean"
                                                                                  _ -> throwError "if: expected boolean"
                                                           in case kl_V3930 of
                                                                  kl_V3930@(Atom (Str "")) -> pat_cond_0
                                                                  _ -> pat_cond_1

kl_shen_app :: Types.KLValue ->
               Types.KLValue ->
               Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_app (!kl_V3935) (!kl_V3936) (!kl_V3937) = do !appl_0 <- kl_V3935 `pseq` (kl_V3937 `pseq` kl_shen_arg_RBstr kl_V3935 kl_V3937)
                                                     appl_0 `pseq` (kl_V3936 `pseq` cn appl_0 kl_V3936)

kl_shen_arg_RBstr :: Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_arg_RBstr (!kl_V3945) (!kl_V3946) = do !appl_0 <- kl_fail
                                               !kl_if_1 <- kl_V3945 `pseq` (appl_0 `pseq` eq kl_V3945 appl_0)
                                               case kl_if_1 of
                                                   Atom (B (True)) -> do return (Types.Atom (Types.Str "..."))
                                                   Atom (B (False)) -> do !kl_if_2 <- kl_V3945 `pseq` kl_shen_listP kl_V3945
                                                                          case kl_if_2 of
                                                                              Atom (B (True)) -> do kl_V3945 `pseq` (kl_V3946 `pseq` kl_shen_list_RBstr kl_V3945 kl_V3946)
                                                                              Atom (B (False)) -> do !kl_if_3 <- kl_V3945 `pseq` stringP kl_V3945
                                                                                                     case kl_if_3 of
                                                                                                         Atom (B (True)) -> do kl_V3945 `pseq` (kl_V3946 `pseq` kl_shen_str_RBstr kl_V3945 kl_V3946)
                                                                                                         Atom (B (False)) -> do !kl_if_4 <- kl_V3945 `pseq` absvectorP kl_V3945
                                                                                                                                case kl_if_4 of
                                                                                                                                    Atom (B (True)) -> do kl_V3945 `pseq` (kl_V3946 `pseq` kl_shen_vector_RBstr kl_V3945 kl_V3946)
                                                                                                                                    Atom (B (False)) -> do do kl_V3945 `pseq` kl_shen_atom_RBstr kl_V3945
                                                                                                                                    _ -> throwError "if: expected boolean"
                                                                                                         _ -> throwError "if: expected boolean"
                                                                              _ -> throwError "if: expected boolean"
                                                   _ -> throwError "if: expected boolean"

kl_shen_list_RBstr :: Types.KLValue ->
                      Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_list_RBstr (!kl_V3949) (!kl_V3950) = do let pat_cond_0 = do !appl_1 <- kl_shen_maxseq
                                                                    !appl_2 <- kl_V3949 `pseq` (appl_1 `pseq` kl_shen_iter_list kl_V3949 (Types.Atom (Types.UnboundSym "shen.r")) appl_1)
                                                                    !appl_3 <- appl_2 `pseq` kl_Ats appl_2 (Types.Atom (Types.Str ")"))
                                                                    appl_3 `pseq` kl_Ats (Types.Atom (Types.Str "(")) appl_3
                                                    pat_cond_4 = do do !appl_5 <- kl_shen_maxseq
                                                                       !appl_6 <- kl_V3949 `pseq` (kl_V3950 `pseq` (appl_5 `pseq` kl_shen_iter_list kl_V3949 kl_V3950 appl_5))
                                                                       !appl_7 <- appl_6 `pseq` kl_Ats appl_6 (Types.Atom (Types.Str "]"))
                                                                       appl_7 `pseq` kl_Ats (Types.Atom (Types.Str "[")) appl_7
                                                 in case kl_V3950 of
                                                        kl_V3950@(Atom (UnboundSym "shen.r")) -> pat_cond_0
                                                        kl_V3950@(ApplC (PL "shen.r"
                                                                            _)) -> pat_cond_0
                                                        kl_V3950@(ApplC (Func "shen.r"
                                                                              _)) -> pat_cond_0
                                                        _ -> pat_cond_4

kl_shen_maxseq :: Types.KLContext Types.Env Types.KLValue
kl_shen_maxseq = do value (Types.Atom (Types.UnboundSym "*maximum-print-sequence-size*"))

kl_shen_iter_list :: Types.KLValue ->
                     Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_iter_list (!kl_V3964) (!kl_V3965) (!kl_V3966) = do let pat_cond_0 = do return (Types.Atom (Types.Str ""))
                                                               pat_cond_1 = do let pat_cond_2 = do return (Types.Atom (Types.Str "... etc"))
                                                                                   pat_cond_3 = do let pat_cond_4 kl_V3964 kl_V3964h = do kl_V3964h `pseq` (kl_V3965 `pseq` kl_shen_arg_RBstr kl_V3964h kl_V3965)
                                                                                                       pat_cond_5 kl_V3964 kl_V3964h kl_V3964t = do !appl_6 <- kl_V3964h `pseq` (kl_V3965 `pseq` kl_shen_arg_RBstr kl_V3964h kl_V3965)
                                                                                                                                                    !appl_7 <- kl_V3966 `pseq` Primitives.subtract kl_V3966 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                    !appl_8 <- kl_V3964t `pseq` (kl_V3965 `pseq` (appl_7 `pseq` kl_shen_iter_list kl_V3964t kl_V3965 appl_7))
                                                                                                                                                    !appl_9 <- appl_8 `pseq` kl_Ats (Types.Atom (Types.Str " ")) appl_8
                                                                                                                                                    appl_6 `pseq` (appl_9 `pseq` kl_Ats appl_6 appl_9)
                                                                                                       pat_cond_10 = do do !appl_11 <- kl_V3964 `pseq` (kl_V3965 `pseq` kl_shen_arg_RBstr kl_V3964 kl_V3965)
                                                                                                                           !appl_12 <- appl_11 `pseq` kl_Ats (Types.Atom (Types.Str " ")) appl_11
                                                                                                                           appl_12 `pseq` kl_Ats (Types.Atom (Types.Str "|")) appl_12
                                                                                                    in case kl_V3964 of
                                                                                                           !(kl_V3964@(Cons (!kl_V3964h)
                                                                                                                            (Atom (Nil)))) -> pat_cond_4 kl_V3964 kl_V3964h
                                                                                                           !(kl_V3964@(Cons (!kl_V3964h)
                                                                                                                            (!kl_V3964t))) -> pat_cond_5 kl_V3964 kl_V3964h kl_V3964t
                                                                                                           _ -> pat_cond_10
                                                                                in case kl_V3966 of
                                                                                       kl_V3966@(Atom (N (KI 0))) -> pat_cond_2
                                                                                       _ -> pat_cond_3
                                                            in case kl_V3964 of
                                                                   kl_V3964@(Atom (Nil)) -> pat_cond_0
                                                                   _ -> pat_cond_1

kl_shen_str_RBstr :: Types.KLValue ->
                     Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_str_RBstr (!kl_V3973) (!kl_V3974) = do let pat_cond_0 = do return kl_V3973
                                                   pat_cond_1 = do do !appl_2 <- nToString (Types.Atom (Types.N (Types.KI 34)))
                                                                      !appl_3 <- nToString (Types.Atom (Types.N (Types.KI 34)))
                                                                      !appl_4 <- kl_V3973 `pseq` (appl_3 `pseq` kl_Ats kl_V3973 appl_3)
                                                                      appl_2 `pseq` (appl_4 `pseq` kl_Ats appl_2 appl_4)
                                                in case kl_V3974 of
                                                       kl_V3974@(Atom (UnboundSym "shen.a")) -> pat_cond_0
                                                       kl_V3974@(ApplC (PL "shen.a"
                                                                           _)) -> pat_cond_0
                                                       kl_V3974@(ApplC (Func "shen.a"
                                                                             _)) -> pat_cond_0
                                                       _ -> pat_cond_1

kl_shen_vector_RBstr :: Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_vector_RBstr (!kl_V3977) (!kl_V3978) = do !kl_if_0 <- kl_V3977 `pseq` kl_shen_print_vectorP kl_V3977
                                                  case kl_if_0 of
                                                      Atom (B (True)) -> do !appl_1 <- kl_V3977 `pseq` addressFrom kl_V3977 (Types.Atom (Types.N (Types.KI 0)))
                                                                            !appl_2 <- appl_1 `pseq` kl_function appl_1
                                                                            kl_V3977 `pseq` applyWrapper appl_2 [kl_V3977]
                                                      Atom (B (False)) -> do do !kl_if_3 <- kl_V3977 `pseq` kl_vectorP kl_V3977
                                                                                case kl_if_3 of
                                                                                    Atom (B (True)) -> do !appl_4 <- kl_shen_maxseq
                                                                                                          !appl_5 <- kl_V3977 `pseq` (kl_V3978 `pseq` (appl_4 `pseq` kl_shen_iter_vector kl_V3977 (Types.Atom (Types.N (Types.KI 1))) kl_V3978 appl_4))
                                                                                                          !appl_6 <- appl_5 `pseq` kl_Ats appl_5 (Types.Atom (Types.Str ">"))
                                                                                                          appl_6 `pseq` kl_Ats (Types.Atom (Types.Str "<")) appl_6
                                                                                    Atom (B (False)) -> do do !appl_7 <- kl_shen_maxseq
                                                                                                              !appl_8 <- kl_V3977 `pseq` (kl_V3978 `pseq` (appl_7 `pseq` kl_shen_iter_vector kl_V3977 (Types.Atom (Types.N (Types.KI 0))) kl_V3978 appl_7))
                                                                                                              !appl_9 <- appl_8 `pseq` kl_Ats appl_8 (Types.Atom (Types.Str ">>"))
                                                                                                              !appl_10 <- appl_9 `pseq` kl_Ats (Types.Atom (Types.Str "<")) appl_9
                                                                                                              appl_10 `pseq` kl_Ats (Types.Atom (Types.Str "<")) appl_10
                                                                                    _ -> throwError "if: expected boolean"
                                                      _ -> throwError "if: expected boolean"

kl_shen_print_vectorP :: Types.KLValue ->
                         Types.KLContext Types.Env Types.KLValue
kl_shen_print_vectorP (!kl_V3980) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Zero) -> do let pat_cond_1 = do return (Atom (B True))
                                                                                                          pat_cond_2 = do do let pat_cond_3 = do return (Atom (B True))
                                                                                                                                 pat_cond_4 = do do !appl_5 <- kl_Zero `pseq` numberP kl_Zero
                                                                                                                                                    !kl_if_6 <- appl_5 `pseq` kl_not appl_5
                                                                                                                                                    case kl_if_6 of
                                                                                                                                                        Atom (B (True)) -> do kl_Zero `pseq` kl_shen_fboundP kl_Zero
                                                                                                                                                        Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                        _ -> throwError "if: expected boolean"
                                                                                                                              in case kl_Zero of
                                                                                                                                     kl_Zero@(Atom (UnboundSym "shen.pvar")) -> pat_cond_3
                                                                                                                                     kl_Zero@(ApplC (PL "shen.pvar"
                                                                                                                                                        _)) -> pat_cond_3
                                                                                                                                     kl_Zero@(ApplC (Func "shen.pvar"
                                                                                                                                                          _)) -> pat_cond_3
                                                                                                                                     _ -> pat_cond_4
                                                                                                       in case kl_Zero of
                                                                                                              kl_Zero@(Atom (UnboundSym "shen.tuple")) -> pat_cond_1
                                                                                                              kl_Zero@(ApplC (PL "shen.tuple"
                                                                                                                                 _)) -> pat_cond_1
                                                                                                              kl_Zero@(ApplC (Func "shen.tuple"
                                                                                                                                   _)) -> pat_cond_1
                                                                                                              _ -> pat_cond_2)))
                                       !appl_7 <- kl_V3980 `pseq` addressFrom kl_V3980 (Types.Atom (Types.N (Types.KI 0)))
                                       appl_7 `pseq` applyWrapper appl_0 [appl_7]

kl_shen_fboundP :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_fboundP (!kl_V3982) = do (do !appl_0 <- kl_V3982 `pseq` kl_ps kl_V3982
                                     appl_0 `pseq` kl_do appl_0 (Atom (B True))) `catchError` (\(!kl_E) -> do return (Atom (B False)))

kl_shen_tuple :: Types.KLValue ->
                 Types.KLContext Types.Env Types.KLValue
kl_shen_tuple (!kl_V3984) = do !appl_0 <- kl_V3984 `pseq` addressFrom kl_V3984 (Types.Atom (Types.N (Types.KI 1)))
                               !appl_1 <- kl_V3984 `pseq` addressFrom kl_V3984 (Types.Atom (Types.N (Types.KI 2)))
                               !appl_2 <- appl_1 `pseq` kl_shen_app appl_1 (Types.Atom (Types.Str ")")) (Types.Atom (Types.UnboundSym "shen.s"))
                               !appl_3 <- appl_2 `pseq` cn (Types.Atom (Types.Str " ")) appl_2
                               !appl_4 <- appl_0 `pseq` (appl_3 `pseq` kl_shen_app appl_0 appl_3 (Types.Atom (Types.UnboundSym "shen.s")))
                               appl_4 `pseq` cn (Types.Atom (Types.Str "(@p ")) appl_4

kl_shen_iter_vector :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_iter_vector (!kl_V3995) (!kl_V3996) (!kl_V3997) (!kl_V3998) = do let pat_cond_0 = do return (Types.Atom (Types.Str "... etc"))
                                                                             pat_cond_1 = do do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Item) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Next) -> do let pat_cond_4 = do return (Types.Atom (Types.Str ""))
                                                                                                                                                                                                                                  pat_cond_5 = do do let pat_cond_6 = do kl_Item `pseq` (kl_V3997 `pseq` kl_shen_arg_RBstr kl_Item kl_V3997)
                                                                                                                                                                                                                                                         pat_cond_7 = do do !appl_8 <- kl_Item `pseq` (kl_V3997 `pseq` kl_shen_arg_RBstr kl_Item kl_V3997)
                                                                                                                                                                                                                                                                            !appl_9 <- kl_V3996 `pseq` add kl_V3996 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                            !appl_10 <- kl_V3998 `pseq` Primitives.subtract kl_V3998 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                                                                                                                            !appl_11 <- kl_V3995 `pseq` (appl_9 `pseq` (kl_V3997 `pseq` (appl_10 `pseq` kl_shen_iter_vector kl_V3995 appl_9 kl_V3997 appl_10)))
                                                                                                                                                                                                                                                                            !appl_12 <- appl_11 `pseq` kl_Ats (Types.Atom (Types.Str " ")) appl_11
                                                                                                                                                                                                                                                                            appl_8 `pseq` (appl_12 `pseq` kl_Ats appl_8 appl_12)
                                                                                                                                                                                                                                                      in case kl_Next of
                                                                                                                                                                                                                                                             kl_Next@(Atom (UnboundSym "shen.out-of-bounds")) -> pat_cond_6
                                                                                                                                                                                                                                                             kl_Next@(ApplC (PL "shen.out-of-bounds"
                                                                                                                                                                                                                                                                                _)) -> pat_cond_6
                                                                                                                                                                                                                                                             kl_Next@(ApplC (Func "shen.out-of-bounds"
                                                                                                                                                                                                                                                                                  _)) -> pat_cond_6
                                                                                                                                                                                                                                                             _ -> pat_cond_7
                                                                                                                                                                                                                               in case kl_Item of
                                                                                                                                                                                                                                      kl_Item@(Atom (UnboundSym "shen.out-of-bounds")) -> pat_cond_4
                                                                                                                                                                                                                                      kl_Item@(ApplC (PL "shen.out-of-bounds"
                                                                                                                                                                                                                                                         _)) -> pat_cond_4
                                                                                                                                                                                                                                      kl_Item@(ApplC (Func "shen.out-of-bounds"
                                                                                                                                                                                                                                                           _)) -> pat_cond_4
                                                                                                                                                                                                                                      _ -> pat_cond_5)))
                                                                                                                                                               !appl_13 <- (do !appl_14 <- kl_V3996 `pseq` add kl_V3996 (Types.Atom (Types.N (Types.KI 1)))
                                                                                                                                                                               kl_V3995 `pseq` (appl_14 `pseq` addressFrom kl_V3995 appl_14)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.out-of-bounds")))
                                                                                                                                                               appl_13 `pseq` applyWrapper appl_3 [appl_13])))
                                                                                                !appl_15 <- (do kl_V3995 `pseq` (kl_V3996 `pseq` addressFrom kl_V3995 kl_V3996)) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.UnboundSym "shen.out-of-bounds")))
                                                                                                appl_15 `pseq` applyWrapper appl_2 [appl_15]
                                                                          in case kl_V3998 of
                                                                                 kl_V3998@(Atom (N (KI 0))) -> pat_cond_0
                                                                                 _ -> pat_cond_1

kl_shen_atom_RBstr :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_atom_RBstr (!kl_V4000) = do (do kl_V4000 `pseq` str kl_V4000) `catchError` (\(!kl_E) -> do kl_shen_funexstring)

kl_shen_funexstring :: Types.KLContext Types.Env Types.KLValue
kl_shen_funexstring = do !appl_0 <- intern (Types.Atom (Types.Str "x"))
                         !appl_1 <- appl_0 `pseq` kl_gensym appl_0
                         !appl_2 <- appl_1 `pseq` kl_shen_arg_RBstr appl_1 (Types.Atom (Types.UnboundSym "shen.a"))
                         !appl_3 <- appl_2 `pseq` kl_Ats appl_2 (Types.Atom (Types.Str "\\DC1"))
                         !appl_4 <- appl_3 `pseq` kl_Ats (Types.Atom (Types.Str "e")) appl_3
                         !appl_5 <- appl_4 `pseq` kl_Ats (Types.Atom (Types.Str "n")) appl_4
                         !appl_6 <- appl_5 `pseq` kl_Ats (Types.Atom (Types.Str "u")) appl_5
                         !appl_7 <- appl_6 `pseq` kl_Ats (Types.Atom (Types.Str "f")) appl_6
                         appl_7 `pseq` kl_Ats (Types.Atom (Types.Str "\\DLE")) appl_7

kl_shen_listP :: Types.KLValue ->
                 Types.KLContext Types.Env Types.KLValue
kl_shen_listP (!kl_V4002) = do !kl_if_0 <- kl_V4002 `pseq` kl_emptyP kl_V4002
                               case kl_if_0 of
                                   Atom (B (True)) -> do return (Atom (B True))
                                   Atom (B (False)) -> do do let pat_cond_1 kl_V4002 kl_V4002h kl_V4002t = do return (Atom (B True))
                                                                 pat_cond_2 = do do return (Atom (B False))
                                                              in case kl_V4002 of
                                                                     !(kl_V4002@(Cons (!kl_V4002h)
                                                                                      (!kl_V4002t))) -> pat_cond_1 kl_V4002 kl_V4002h kl_V4002t
                                                                     _ -> pat_cond_2
                                   _ -> throwError "if: expected boolean"

expr9 :: Types.KLContext Types.Env Types.KLValue
expr9 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
