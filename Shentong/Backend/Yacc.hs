{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Backend.Yacc where

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

kl_shen_yacc :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_shen_yacc (!kl_V4004) = do let pat_cond_0 kl_V4004 kl_V4004t kl_V4004th kl_V4004tt = do kl_V4004th `pseq` (kl_V4004tt `pseq` kl_shen_yacc_RBshen kl_V4004th kl_V4004tt)
                                  pat_cond_1 = do do let !aw_2 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                     applyWrapper aw_2 [ApplC (wrapNamed "shen.yacc" kl_shen_yacc)]
                               in case kl_V4004 of
                                      !(kl_V4004@(Cons (Atom (UnboundSym "defcc"))
                                                       (!(kl_V4004t@(Cons (!kl_V4004th)
                                                                          (!kl_V4004tt)))))) -> pat_cond_0 kl_V4004 kl_V4004t kl_V4004th kl_V4004tt
                                      !(kl_V4004@(Cons (ApplC (PL "defcc" _))
                                                       (!(kl_V4004t@(Cons (!kl_V4004th)
                                                                          (!kl_V4004tt)))))) -> pat_cond_0 kl_V4004 kl_V4004t kl_V4004th kl_V4004tt
                                      !(kl_V4004@(Cons (ApplC (Func "defcc" _))
                                                       (!(kl_V4004t@(Cons (!kl_V4004th)
                                                                          (!kl_V4004tt)))))) -> pat_cond_0 kl_V4004 kl_V4004t kl_V4004th kl_V4004tt
                                      _ -> pat_cond_1

kl_shen_yacc_RBshen :: Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_yacc_RBshen (!kl_V4007) (!kl_V4008) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_CCRules) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_CCBody) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_YaccCases) -> do !appl_3 <- kl_YaccCases `pseq` kl_shen_kill_code kl_YaccCases
                                                                                                                                                                                                                                                        !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                        !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "->")) appl_4
                                                                                                                                                                                                                                                        !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "Stream")) appl_5
                                                                                                                                                                                                                                                        !appl_7 <- kl_V4007 `pseq` (appl_6 `pseq` klCons kl_V4007 appl_6)
                                                                                                                                                                                                                                                        appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "define")) appl_7)))
                                                                                                                                                                                    !appl_8 <- kl_CCBody `pseq` kl_shen_yacc_cases kl_CCBody
                                                                                                                                                                                    appl_8 `pseq` applyWrapper appl_2 [appl_8])))
                                                                                                                   let !appl_9 = ApplC (Func "lambda" (Context (\(!kl_X) -> do kl_X `pseq` kl_shen_cc_body kl_X)))
                                                                                                                   !appl_10 <- appl_9 `pseq` (kl_CCRules `pseq` kl_map appl_9 kl_CCRules)
                                                                                                                   appl_10 `pseq` applyWrapper appl_1 [appl_10])))
                                                 !appl_11 <- kl_V4008 `pseq` kl_shen_split_cc_rules (Atom (B True)) kl_V4008 (Types.Atom Types.Nil)
                                                 appl_11 `pseq` applyWrapper appl_0 [appl_11]

kl_shen_kill_code :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_kill_code (!kl_V4010) = do !appl_0 <- kl_V4010 `pseq` kl_occurrences (ApplC (PL "kill" kl_kill)) kl_V4010
                                   !kl_if_1 <- appl_0 `pseq` greaterThan appl_0 (Types.Atom (Types.N (Types.KI 0)))
                                   case kl_if_1 of
                                       Atom (B (True)) -> do !appl_2 <- klCons (Types.Atom (Types.UnboundSym "E")) (Types.Atom Types.Nil)
                                                             !appl_3 <- appl_2 `pseq` klCons (ApplC (wrapNamed "shen.analyse-kill" kl_shen_analyse_kill)) appl_2
                                                             !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                             !appl_5 <- appl_4 `pseq` klCons (Types.Atom (Types.UnboundSym "E")) appl_4
                                                             !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "lambda")) appl_5
                                                             !appl_7 <- appl_6 `pseq` klCons appl_6 (Types.Atom Types.Nil)
                                                             !appl_8 <- kl_V4010 `pseq` (appl_7 `pseq` klCons kl_V4010 appl_7)
                                                             appl_8 `pseq` klCons (Types.Atom (Types.UnboundSym "trap-error")) appl_8
                                       Atom (B (False)) -> do do return kl_V4010
                                       _ -> throwError "if: expected boolean"

kl_kill :: Types.KLContext Types.Env Types.KLValue
kl_kill = do simpleError (Types.Atom (Types.Str "yacc kill"))

kl_shen_analyse_kill :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_analyse_kill (!kl_V4012) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_String) -> do let pat_cond_1 = do kl_fail
                                                                                                           pat_cond_2 = do do return kl_V4012
                                                                                                        in case kl_String of
                                                                                                               kl_String@(Atom (Str "yacc kill")) -> pat_cond_1
                                                                                                               _ -> pat_cond_2)))
                                      !appl_3 <- kl_V4012 `pseq` errorToString kl_V4012
                                      appl_3 `pseq` applyWrapper appl_0 [appl_3]

kl_shen_split_cc_rules :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_split_cc_rules (!kl_V4018) (!kl_V4019) (!kl_V4020) = do !kl_if_0 <- let pat_cond_1 = do let pat_cond_2 = do return (Atom (B True))
                                                                                                    pat_cond_3 = do do return (Atom (B False))
                                                                                                 in case kl_V4020 of
                                                                                                        kl_V4020@(Atom (Nil)) -> pat_cond_2
                                                                                                        _ -> pat_cond_3
                                                                                pat_cond_4 = do do return (Atom (B False))
                                                                             in case kl_V4019 of
                                                                                    kl_V4019@(Atom (Nil)) -> pat_cond_1
                                                                                    _ -> pat_cond_4
                                                                case kl_if_0 of
                                                                    Atom (B (True)) -> do return (Types.Atom Types.Nil)
                                                                    Atom (B (False)) -> do let pat_cond_5 = do !appl_6 <- kl_V4020 `pseq` kl_reverse kl_V4020
                                                                                                               !appl_7 <- kl_V4018 `pseq` (appl_6 `pseq` kl_shen_split_cc_rule kl_V4018 appl_6 (Types.Atom Types.Nil))
                                                                                                               appl_7 `pseq` klCons appl_7 (Types.Atom Types.Nil)
                                                                                               pat_cond_8 kl_V4019 kl_V4019t = do !appl_9 <- kl_V4020 `pseq` kl_reverse kl_V4020
                                                                                                                                  !appl_10 <- kl_V4018 `pseq` (appl_9 `pseq` kl_shen_split_cc_rule kl_V4018 appl_9 (Types.Atom Types.Nil))
                                                                                                                                  !appl_11 <- kl_V4018 `pseq` (kl_V4019t `pseq` kl_shen_split_cc_rules kl_V4018 kl_V4019t (Types.Atom Types.Nil))
                                                                                                                                  appl_10 `pseq` (appl_11 `pseq` klCons appl_10 appl_11)
                                                                                               pat_cond_12 kl_V4019 kl_V4019h kl_V4019t = do !appl_13 <- kl_V4019h `pseq` (kl_V4020 `pseq` klCons kl_V4019h kl_V4020)
                                                                                                                                             kl_V4018 `pseq` (kl_V4019t `pseq` (appl_13 `pseq` kl_shen_split_cc_rules kl_V4018 kl_V4019t appl_13))
                                                                                               pat_cond_14 = do do let !aw_15 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                   applyWrapper aw_15 [ApplC (wrapNamed "shen.split_cc_rules" kl_shen_split_cc_rules)]
                                                                                            in case kl_V4019 of
                                                                                                   kl_V4019@(Atom (Nil)) -> pat_cond_5
                                                                                                   !(kl_V4019@(Cons (Atom (UnboundSym ";"))
                                                                                                                    (!kl_V4019t))) -> pat_cond_8 kl_V4019 kl_V4019t
                                                                                                   !(kl_V4019@(Cons (ApplC (PL ";"
                                                                                                                               _))
                                                                                                                    (!kl_V4019t))) -> pat_cond_8 kl_V4019 kl_V4019t
                                                                                                   !(kl_V4019@(Cons (ApplC (Func ";"
                                                                                                                                 _))
                                                                                                                    (!kl_V4019t))) -> pat_cond_8 kl_V4019 kl_V4019t
                                                                                                   !(kl_V4019@(Cons (!kl_V4019h)
                                                                                                                    (!kl_V4019t))) -> pat_cond_12 kl_V4019 kl_V4019h kl_V4019t
                                                                                                   _ -> pat_cond_14
                                                                    _ -> throwError "if: expected boolean"

kl_shen_split_cc_rule :: Types.KLValue ->
                         Types.KLValue ->
                         Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_split_cc_rule (!kl_V4028) (!kl_V4029) (!kl_V4030) = do let pat_cond_0 kl_V4029 kl_V4029t kl_V4029th = do !appl_1 <- kl_V4030 `pseq` kl_reverse kl_V4030
                                                                                                                 appl_1 `pseq` (kl_V4029t `pseq` klCons appl_1 kl_V4029t)
                                                                   pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth = do !appl_3 <- kl_V4030 `pseq` kl_reverse kl_V4030
                                                                                                                                                     !appl_4 <- kl_V4029th `pseq` klCons kl_V4029th (Types.Atom Types.Nil)
                                                                                                                                                     !appl_5 <- kl_V4029ttth `pseq` (appl_4 `pseq` klCons kl_V4029ttth appl_4)
                                                                                                                                                     !appl_6 <- appl_5 `pseq` klCons (Types.Atom (Types.UnboundSym "where")) appl_5
                                                                                                                                                     !appl_7 <- appl_6 `pseq` klCons appl_6 (Types.Atom Types.Nil)
                                                                                                                                                     appl_3 `pseq` (appl_7 `pseq` klCons appl_3 appl_7)
                                                                   pat_cond_8 = do !appl_9 <- kl_V4028 `pseq` (kl_V4030 `pseq` kl_shen_semantic_completion_warning kl_V4028 kl_V4030)
                                                                                   !appl_10 <- kl_V4030 `pseq` kl_reverse kl_V4030
                                                                                   !appl_11 <- appl_10 `pseq` kl_shen_default_semantics appl_10
                                                                                   !appl_12 <- appl_11 `pseq` klCons appl_11 (Types.Atom Types.Nil)
                                                                                   !appl_13 <- appl_12 `pseq` klCons (Types.Atom (Types.UnboundSym ":=")) appl_12
                                                                                   !appl_14 <- kl_V4028 `pseq` (appl_13 `pseq` (kl_V4030 `pseq` kl_shen_split_cc_rule kl_V4028 appl_13 kl_V4030))
                                                                                   appl_9 `pseq` (appl_14 `pseq` kl_do appl_9 appl_14)
                                                                   pat_cond_15 kl_V4029 kl_V4029h kl_V4029t = do !appl_16 <- kl_V4029h `pseq` (kl_V4030 `pseq` klCons kl_V4029h kl_V4030)
                                                                                                                 kl_V4028 `pseq` (kl_V4029t `pseq` (appl_16 `pseq` kl_shen_split_cc_rule kl_V4028 kl_V4029t appl_16))
                                                                   pat_cond_17 = do do let !aw_18 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                       applyWrapper aw_18 [ApplC (wrapNamed "shen.split_cc_rule" kl_shen_split_cc_rule)]
                                                                in case kl_V4029 of
                                                                       !(kl_V4029@(Cons (Atom (UnboundSym ":="))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (Atom (Nil))))))) -> pat_cond_0 kl_V4029 kl_V4029t kl_V4029th
                                                                       !(kl_V4029@(Cons (ApplC (PL ":="
                                                                                                   _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (Atom (Nil))))))) -> pat_cond_0 kl_V4029 kl_V4029t kl_V4029th
                                                                       !(kl_V4029@(Cons (ApplC (Func ":="
                                                                                                     _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (Atom (Nil))))))) -> pat_cond_0 kl_V4029 kl_V4029t kl_V4029th
                                                                       !(kl_V4029@(Cons (Atom (UnboundSym ":="))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (Atom (UnboundSym "where"))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (Atom (UnboundSym ":="))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (ApplC (PL "where"
                                                                                                                                          _))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (Atom (UnboundSym ":="))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (ApplC (Func "where"
                                                                                                                                            _))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (ApplC (PL ":="
                                                                                                   _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (Atom (UnboundSym "where"))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (ApplC (PL ":="
                                                                                                   _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (ApplC (PL "where"
                                                                                                                                          _))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (ApplC (PL ":="
                                                                                                   _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (ApplC (Func "where"
                                                                                                                                            _))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (ApplC (Func ":="
                                                                                                     _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (Atom (UnboundSym "where"))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (ApplC (Func ":="
                                                                                                     _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (ApplC (PL "where"
                                                                                                                                          _))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       !(kl_V4029@(Cons (ApplC (Func ":="
                                                                                                     _))
                                                                                        (!(kl_V4029t@(Cons (!kl_V4029th)
                                                                                                           (!(kl_V4029tt@(Cons (ApplC (Func "where"
                                                                                                                                            _))
                                                                                                                               (!(kl_V4029ttt@(Cons (!kl_V4029ttth)
                                                                                                                                                    (Atom (Nil))))))))))))) -> pat_cond_2 kl_V4029 kl_V4029t kl_V4029th kl_V4029tt kl_V4029ttt kl_V4029ttth
                                                                       kl_V4029@(Atom (Nil)) -> pat_cond_8
                                                                       !(kl_V4029@(Cons (!kl_V4029h)
                                                                                        (!kl_V4029t))) -> pat_cond_15 kl_V4029 kl_V4029h kl_V4029t
                                                                       _ -> pat_cond_17

kl_shen_semantic_completion_warning :: Types.KLValue ->
                                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_semantic_completion_warning (!kl_V4041) (!kl_V4042) = do let pat_cond_0 = do !appl_1 <- kl_stoutput
                                                                                     let !aw_2 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                     !appl_3 <- appl_1 `pseq` applyWrapper aw_2 [Types.Atom (Types.Str "warning: "),
                                                                                                                                 appl_1]
                                                                                     let !appl_4 = ApplC (Func "lambda" (Context (\(!kl_X) -> do let !aw_5 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                 !appl_6 <- kl_X `pseq` applyWrapper aw_5 [kl_X,
                                                                                                                                                                                           Types.Atom (Types.Str " "),
                                                                                                                                                                                           Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                 !appl_7 <- kl_stoutput
                                                                                                                                                 let !aw_8 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                                                                                 appl_6 `pseq` (appl_7 `pseq` applyWrapper aw_8 [appl_6,
                                                                                                                                                                                                 appl_7]))))
                                                                                     !appl_9 <- kl_V4042 `pseq` kl_reverse kl_V4042
                                                                                     !appl_10 <- appl_4 `pseq` (appl_9 `pseq` kl_map appl_4 appl_9)
                                                                                     !appl_11 <- kl_stoutput
                                                                                     let !aw_12 = Types.Atom (Types.UnboundSym "shen.prhush")
                                                                                     !appl_13 <- appl_11 `pseq` applyWrapper aw_12 [Types.Atom (Types.Str "has no semantics.\n"),
                                                                                                                                    appl_11]
                                                                                     !appl_14 <- appl_10 `pseq` (appl_13 `pseq` kl_do appl_10 appl_13)
                                                                                     appl_3 `pseq` (appl_14 `pseq` kl_do appl_3 appl_14)
                                                                     pat_cond_15 = do do return (Types.Atom (Types.UnboundSym "shen.skip"))
                                                                  in case kl_V4041 of
                                                                         kl_V4041@(Atom (UnboundSym "true")) -> pat_cond_0
                                                                         kl_V4041@(Atom (B (True))) -> pat_cond_0
                                                                         _ -> pat_cond_15

kl_shen_default_semantics :: Types.KLValue ->
                             Types.KLContext Types.Env Types.KLValue
kl_shen_default_semantics (!kl_V4044) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                               pat_cond_1 = do !kl_if_2 <- let pat_cond_3 kl_V4044 kl_V4044h kl_V4044t = do !kl_if_4 <- let pat_cond_5 = do !kl_if_6 <- kl_V4044h `pseq` kl_shen_grammar_symbolP kl_V4044h
                                                                                                                                                            case kl_if_6 of
                                                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                                _ -> throwError "if: expected boolean"
                                                                                                                                            pat_cond_7 = do do return (Atom (B False))
                                                                                                                                         in case kl_V4044t of
                                                                                                                                                kl_V4044t@(Atom (Nil)) -> pat_cond_5
                                                                                                                                                _ -> pat_cond_7
                                                                                                                            case kl_if_4 of
                                                                                                                                Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                _ -> throwError "if: expected boolean"
                                                                               pat_cond_8 = do do return (Atom (B False))
                                                                            in case kl_V4044 of
                                                                                   !(kl_V4044@(Cons (!kl_V4044h)
                                                                                                    (!kl_V4044t))) -> pat_cond_3 kl_V4044 kl_V4044h kl_V4044t
                                                                                   _ -> pat_cond_8
                                                               case kl_if_2 of
                                                                   Atom (B (True)) -> do kl_V4044 `pseq` hd kl_V4044
                                                                   Atom (B (False)) -> do !kl_if_9 <- let pat_cond_10 kl_V4044 kl_V4044h kl_V4044t = do !kl_if_11 <- kl_V4044h `pseq` kl_shen_grammar_symbolP kl_V4044h
                                                                                                                                                        case kl_if_11 of
                                                                                                                                                            Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                            Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                            _ -> throwError "if: expected boolean"
                                                                                                          pat_cond_12 = do do return (Atom (B False))
                                                                                                       in case kl_V4044 of
                                                                                                              !(kl_V4044@(Cons (!kl_V4044h)
                                                                                                                               (!kl_V4044t))) -> pat_cond_10 kl_V4044 kl_V4044h kl_V4044t
                                                                                                              _ -> pat_cond_12
                                                                                          case kl_if_9 of
                                                                                              Atom (B (True)) -> do !appl_13 <- kl_V4044 `pseq` hd kl_V4044
                                                                                                                    !appl_14 <- kl_V4044 `pseq` tl kl_V4044
                                                                                                                    !appl_15 <- appl_14 `pseq` kl_shen_default_semantics appl_14
                                                                                                                    !appl_16 <- appl_15 `pseq` klCons appl_15 (Types.Atom Types.Nil)
                                                                                                                    !appl_17 <- appl_13 `pseq` (appl_16 `pseq` klCons appl_13 appl_16)
                                                                                                                    appl_17 `pseq` klCons (ApplC (wrapNamed "append" kl_append)) appl_17
                                                                                              Atom (B (False)) -> do let pat_cond_18 kl_V4044 kl_V4044h kl_V4044t = do !appl_19 <- kl_V4044t `pseq` kl_shen_default_semantics kl_V4044t
                                                                                                                                                                       !appl_20 <- appl_19 `pseq` klCons appl_19 (Types.Atom Types.Nil)
                                                                                                                                                                       !appl_21 <- kl_V4044h `pseq` (appl_20 `pseq` klCons kl_V4044h appl_20)
                                                                                                                                                                       appl_21 `pseq` klCons (ApplC (wrapNamed "cons" klCons)) appl_21
                                                                                                                         pat_cond_22 = do do let !aw_23 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                                                             applyWrapper aw_23 [ApplC (wrapNamed "shen.default_semantics" kl_shen_default_semantics)]
                                                                                                                      in case kl_V4044 of
                                                                                                                             !(kl_V4044@(Cons (!kl_V4044h)
                                                                                                                                              (!kl_V4044t))) -> pat_cond_18 kl_V4044 kl_V4044h kl_V4044t
                                                                                                                             _ -> pat_cond_22
                                                                                              _ -> throwError "if: expected boolean"
                                                                   _ -> throwError "if: expected boolean"
                                            in case kl_V4044 of
                                                   kl_V4044@(Atom (Nil)) -> pat_cond_0
                                                   _ -> pat_cond_1

kl_shen_grammar_symbolP :: Types.KLValue ->
                           Types.KLContext Types.Env Types.KLValue
kl_shen_grammar_symbolP (!kl_V4046) = do !kl_if_0 <- kl_V4046 `pseq` kl_symbolP kl_V4046
                                         case kl_if_0 of
                                             Atom (B (True)) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Cs) -> do !appl_2 <- kl_Cs `pseq` hd kl_Cs
                                                                                                                                !kl_if_3 <- appl_2 `pseq` eq appl_2 (Types.Atom (Types.Str "<"))
                                                                                                                                case kl_if_3 of
                                                                                                                                    Atom (B (True)) -> do !appl_4 <- kl_Cs `pseq` kl_reverse kl_Cs
                                                                                                                                                          !appl_5 <- appl_4 `pseq` hd appl_4
                                                                                                                                                          !kl_if_6 <- appl_5 `pseq` eq appl_5 (Types.Atom (Types.Str ">"))
                                                                                                                                                          case kl_if_6 of
                                                                                                                                                              Atom (B (True)) -> do return (Atom (B True))
                                                                                                                                                              Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                                              _ -> throwError "if: expected boolean"
                                                                                                                                    Atom (B (False)) -> do do return (Atom (B False))
                                                                                                                                    _ -> throwError "if: expected boolean")))
                                                                   !appl_7 <- kl_V4046 `pseq` kl_explode kl_V4046
                                                                   !appl_8 <- appl_7 `pseq` kl_shen_strip_pathname appl_7
                                                                   !kl_if_9 <- appl_8 `pseq` applyWrapper appl_1 [appl_8]
                                                                   case kl_if_9 of
                                                                       Atom (B (True)) -> do return (Atom (B True))
                                                                       Atom (B (False)) -> do do return (Atom (B False))
                                                                       _ -> throwError "if: expected boolean"
                                             Atom (B (False)) -> do do return (Atom (B False))
                                             _ -> throwError "if: expected boolean"

kl_shen_yacc_cases :: Types.KLValue ->
                      Types.KLContext Types.Env Types.KLValue
kl_shen_yacc_cases (!kl_V4048) = do let pat_cond_0 kl_V4048 kl_V4048h = do return kl_V4048h
                                        pat_cond_1 kl_V4048 kl_V4048h kl_V4048t = do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_P) -> do !appl_3 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                 !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                                                                                 !appl_5 <- kl_P `pseq` (appl_4 `pseq` klCons kl_P appl_4)
                                                                                                                                                 !appl_6 <- appl_5 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_5
                                                                                                                                                 !appl_7 <- kl_V4048t `pseq` kl_shen_yacc_cases kl_V4048t
                                                                                                                                                 !appl_8 <- kl_P `pseq` klCons kl_P (Types.Atom Types.Nil)
                                                                                                                                                 !appl_9 <- appl_7 `pseq` (appl_8 `pseq` klCons appl_7 appl_8)
                                                                                                                                                 !appl_10 <- appl_6 `pseq` (appl_9 `pseq` klCons appl_6 appl_9)
                                                                                                                                                 !appl_11 <- appl_10 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_10
                                                                                                                                                 !appl_12 <- appl_11 `pseq` klCons appl_11 (Types.Atom Types.Nil)
                                                                                                                                                 !appl_13 <- kl_V4048h `pseq` (appl_12 `pseq` klCons kl_V4048h appl_12)
                                                                                                                                                 !appl_14 <- kl_P `pseq` (appl_13 `pseq` klCons kl_P appl_13)
                                                                                                                                                 appl_14 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_14)))
                                                                                     applyWrapper appl_2 [Types.Atom (Types.UnboundSym "YaccParse")]
                                        pat_cond_15 = do do let !aw_16 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                            applyWrapper aw_16 [ApplC (wrapNamed "shen.yacc_cases" kl_shen_yacc_cases)]
                                     in case kl_V4048 of
                                            !(kl_V4048@(Cons (!kl_V4048h)
                                                             (Atom (Nil)))) -> pat_cond_0 kl_V4048 kl_V4048h
                                            !(kl_V4048@(Cons (!kl_V4048h)
                                                             (!kl_V4048t))) -> pat_cond_1 kl_V4048 kl_V4048h kl_V4048t
                                            _ -> pat_cond_15

kl_shen_cc_body :: Types.KLValue ->
                   Types.KLContext Types.Env Types.KLValue
kl_shen_cc_body (!kl_V4050) = do let pat_cond_0 kl_V4050 kl_V4050h kl_V4050t kl_V4050th = do kl_V4050h `pseq` (kl_V4050th `pseq` kl_shen_syntax kl_V4050h (Types.Atom (Types.UnboundSym "Stream")) kl_V4050th)
                                     pat_cond_1 = do do let !aw_2 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                        applyWrapper aw_2 [ApplC (wrapNamed "shen.cc_body" kl_shen_cc_body)]
                                  in case kl_V4050 of
                                         !(kl_V4050@(Cons (!kl_V4050h)
                                                          (!(kl_V4050t@(Cons (!kl_V4050th)
                                                                             (Atom (Nil))))))) -> pat_cond_0 kl_V4050 kl_V4050h kl_V4050t kl_V4050th
                                         _ -> pat_cond_1

kl_shen_syntax :: Types.KLValue ->
                  Types.KLValue ->
                  Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_syntax (!kl_V4054) (!kl_V4055) (!kl_V4056) = do !kl_if_0 <- let pat_cond_1 = do let pat_cond_2 kl_V4056 kl_V4056t kl_V4056th kl_V4056tt kl_V4056tth = do return (Atom (B True))
                                                                                            pat_cond_3 = do do return (Atom (B False))
                                                                                         in case kl_V4056 of
                                                                                                !(kl_V4056@(Cons (Atom (UnboundSym "where"))
                                                                                                                 (!(kl_V4056t@(Cons (!kl_V4056th)
                                                                                                                                    (!(kl_V4056tt@(Cons (!kl_V4056tth)
                                                                                                                                                        (Atom (Nil)))))))))) -> pat_cond_2 kl_V4056 kl_V4056t kl_V4056th kl_V4056tt kl_V4056tth
                                                                                                !(kl_V4056@(Cons (ApplC (PL "where"
                                                                                                                            _))
                                                                                                                 (!(kl_V4056t@(Cons (!kl_V4056th)
                                                                                                                                    (!(kl_V4056tt@(Cons (!kl_V4056tth)
                                                                                                                                                        (Atom (Nil)))))))))) -> pat_cond_2 kl_V4056 kl_V4056t kl_V4056th kl_V4056tt kl_V4056tth
                                                                                                !(kl_V4056@(Cons (ApplC (Func "where"
                                                                                                                              _))
                                                                                                                 (!(kl_V4056t@(Cons (!kl_V4056th)
                                                                                                                                    (!(kl_V4056tt@(Cons (!kl_V4056tth)
                                                                                                                                                        (Atom (Nil)))))))))) -> pat_cond_2 kl_V4056 kl_V4056t kl_V4056th kl_V4056tt kl_V4056tth
                                                                                                _ -> pat_cond_3
                                                                        pat_cond_4 = do do return (Atom (B False))
                                                                     in case kl_V4054 of
                                                                            kl_V4054@(Atom (Nil)) -> pat_cond_1
                                                                            _ -> pat_cond_4
                                                        case kl_if_0 of
                                                            Atom (B (True)) -> do !appl_5 <- kl_V4056 `pseq` tl kl_V4056
                                                                                  !appl_6 <- appl_5 `pseq` hd appl_5
                                                                                  !appl_7 <- appl_6 `pseq` kl_shen_semantics appl_6
                                                                                  !appl_8 <- kl_V4055 `pseq` klCons kl_V4055 (Types.Atom Types.Nil)
                                                                                  !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_8
                                                                                  !appl_10 <- kl_V4056 `pseq` tl kl_V4056
                                                                                  !appl_11 <- appl_10 `pseq` tl appl_10
                                                                                  !appl_12 <- appl_11 `pseq` hd appl_11
                                                                                  !appl_13 <- appl_12 `pseq` kl_shen_semantics appl_12
                                                                                  !appl_14 <- appl_13 `pseq` klCons appl_13 (Types.Atom Types.Nil)
                                                                                  !appl_15 <- appl_9 `pseq` (appl_14 `pseq` klCons appl_9 appl_14)
                                                                                  !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_15
                                                                                  !appl_17 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                  !appl_18 <- appl_17 `pseq` klCons appl_17 (Types.Atom Types.Nil)
                                                                                  !appl_19 <- appl_16 `pseq` (appl_18 `pseq` klCons appl_16 appl_18)
                                                                                  !appl_20 <- appl_7 `pseq` (appl_19 `pseq` klCons appl_7 appl_19)
                                                                                  appl_20 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_20
                                                            Atom (B (False)) -> do let pat_cond_21 = do !appl_22 <- kl_V4055 `pseq` klCons kl_V4055 (Types.Atom Types.Nil)
                                                                                                        !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_22
                                                                                                        !appl_24 <- kl_V4056 `pseq` kl_shen_semantics kl_V4056
                                                                                                        !appl_25 <- appl_24 `pseq` klCons appl_24 (Types.Atom Types.Nil)
                                                                                                        !appl_26 <- appl_23 `pseq` (appl_25 `pseq` klCons appl_23 appl_25)
                                                                                                        appl_26 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_26
                                                                                       pat_cond_27 kl_V4054 kl_V4054h kl_V4054t = do !kl_if_28 <- kl_V4054h `pseq` kl_shen_grammar_symbolP kl_V4054h
                                                                                                                                     case kl_if_28 of
                                                                                                                                         Atom (B (True)) -> do kl_V4054 `pseq` (kl_V4055 `pseq` (kl_V4056 `pseq` kl_shen_recursive_descent kl_V4054 kl_V4055 kl_V4056))
                                                                                                                                         Atom (B (False)) -> do do !kl_if_29 <- kl_V4054h `pseq` kl_variableP kl_V4054h
                                                                                                                                                                   case kl_if_29 of
                                                                                                                                                                       Atom (B (True)) -> do kl_V4054 `pseq` (kl_V4055 `pseq` (kl_V4056 `pseq` kl_shen_variable_match kl_V4054 kl_V4055 kl_V4056))
                                                                                                                                                                       Atom (B (False)) -> do do !kl_if_30 <- kl_V4054h `pseq` kl_shen_jump_streamP kl_V4054h
                                                                                                                                                                                                 case kl_if_30 of
                                                                                                                                                                                                     Atom (B (True)) -> do kl_V4054 `pseq` (kl_V4055 `pseq` (kl_V4056 `pseq` kl_shen_jump_stream kl_V4054 kl_V4055 kl_V4056))
                                                                                                                                                                                                     Atom (B (False)) -> do do !kl_if_31 <- kl_V4054h `pseq` kl_shen_terminalP kl_V4054h
                                                                                                                                                                                                                               case kl_if_31 of
                                                                                                                                                                                                                                   Atom (B (True)) -> do kl_V4054 `pseq` (kl_V4055 `pseq` (kl_V4056 `pseq` kl_shen_check_stream kl_V4054 kl_V4055 kl_V4056))
                                                                                                                                                                                                                                   Atom (B (False)) -> do do let pat_cond_32 kl_V4054h kl_V4054hh kl_V4054ht = do !appl_33 <- kl_V4054h `pseq` kl_shen_decons kl_V4054h
                                                                                                                                                                                                                                                                                                                  appl_33 `pseq` (kl_V4054t `pseq` (kl_V4055 `pseq` (kl_V4056 `pseq` kl_shen_list_stream appl_33 kl_V4054t kl_V4055 kl_V4056)))
                                                                                                                                                                                                                                                                 pat_cond_34 = do do let !aw_35 = Types.Atom (Types.UnboundSym "shen.app")
                                                                                                                                                                                                                                                                                     !appl_36 <- kl_V4054h `pseq` applyWrapper aw_35 [kl_V4054h,
                                                                                                                                                                                                                                                                                                                                      Types.Atom (Types.Str " is not legal syntax\n"),
                                                                                                                                                                                                                                                                                                                                      Types.Atom (Types.UnboundSym "shen.a")]
                                                                                                                                                                                                                                                                                     appl_36 `pseq` simpleError appl_36
                                                                                                                                                                                                                                                              in case kl_V4054h of
                                                                                                                                                                                                                                                                     !(kl_V4054h@(Cons (!kl_V4054hh)
                                                                                                                                                                                                                                                                                       (!kl_V4054ht))) -> pat_cond_32 kl_V4054h kl_V4054hh kl_V4054ht
                                                                                                                                                                                                                                                                     _ -> pat_cond_34
                                                                                                                                                                                                                                   _ -> throwError "if: expected boolean"
                                                                                                                                                                                                     _ -> throwError "if: expected boolean"
                                                                                                                                                                       _ -> throwError "if: expected boolean"
                                                                                                                                         _ -> throwError "if: expected boolean"
                                                                                       pat_cond_37 = do do let !aw_38 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                                           applyWrapper aw_38 [ApplC (wrapNamed "shen.syntax" kl_shen_syntax)]
                                                                                    in case kl_V4054 of
                                                                                           kl_V4054@(Atom (Nil)) -> pat_cond_21
                                                                                           !(kl_V4054@(Cons (!kl_V4054h)
                                                                                                            (!kl_V4054t))) -> pat_cond_27 kl_V4054 kl_V4054h kl_V4054t
                                                                                           _ -> pat_cond_37
                                                            _ -> throwError "if: expected boolean"

kl_shen_list_stream :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_list_stream (!kl_V4061) (!kl_V4062) (!kl_V4063) (!kl_V4064) = do let !appl_0 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Placeholder) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_RunOn) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do !appl_4 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                               !appl_5 <- appl_4 `pseq` klCons appl_4 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                                               !appl_6 <- kl_Action `pseq` (appl_5 `pseq` klCons kl_Action appl_5)
                                                                                                                                                                                                                                                                                                                                               !appl_7 <- kl_Test `pseq` (appl_6 `pseq` klCons kl_Test appl_6)
                                                                                                                                                                                                                                                                                                                                               appl_7 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_7)))
                                                                                                                                                                                                                                                                              !appl_8 <- kl_V4063 `pseq` klCons kl_V4063 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                              !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_8
                                                                                                                                                                                                                                                                              !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                              !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_10
                                                                                                                                                                                                                                                                              !appl_12 <- kl_V4063 `pseq` klCons kl_V4063 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                              !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_12
                                                                                                                                                                                                                                                                              !appl_14 <- appl_13 `pseq` klCons appl_13 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                              !appl_15 <- appl_14 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_14
                                                                                                                                                                                                                                                                              !appl_16 <- appl_15 `pseq` klCons appl_15 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                              !appl_17 <- appl_11 `pseq` (appl_16 `pseq` klCons appl_11 appl_16)
                                                                                                                                                                                                                                                                              !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_17
                                                                                                                                                                                                                                                                              !appl_19 <- kl_V4061 `pseq` (appl_18 `pseq` (kl_Placeholder `pseq` kl_shen_syntax kl_V4061 appl_18 kl_Placeholder))
                                                                                                                                                                                                                                                                              !appl_20 <- kl_RunOn `pseq` (kl_Placeholder `pseq` (appl_19 `pseq` kl_shen_insert_runon kl_RunOn kl_Placeholder appl_19))
                                                                                                                                                                                                                                                                              appl_20 `pseq` applyWrapper appl_3 [appl_20])))
                                                                                                                                                                                                              !appl_21 <- kl_V4063 `pseq` klCons kl_V4063 (Types.Atom Types.Nil)
                                                                                                                                                                                                              !appl_22 <- appl_21 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_21
                                                                                                                                                                                                              !appl_23 <- appl_22 `pseq` klCons appl_22 (Types.Atom Types.Nil)
                                                                                                                                                                                                              !appl_24 <- appl_23 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_23
                                                                                                                                                                                                              !appl_25 <- kl_V4063 `pseq` klCons kl_V4063 (Types.Atom Types.Nil)
                                                                                                                                                                                                              !appl_26 <- appl_25 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_25
                                                                                                                                                                                                              !appl_27 <- appl_26 `pseq` klCons appl_26 (Types.Atom Types.Nil)
                                                                                                                                                                                                              !appl_28 <- appl_27 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_27
                                                                                                                                                                                                              !appl_29 <- appl_28 `pseq` klCons appl_28 (Types.Atom Types.Nil)
                                                                                                                                                                                                              !appl_30 <- appl_24 `pseq` (appl_29 `pseq` klCons appl_24 appl_29)
                                                                                                                                                                                                              !appl_31 <- appl_30 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_30
                                                                                                                                                                                                              !appl_32 <- kl_V4062 `pseq` (appl_31 `pseq` (kl_V4064 `pseq` kl_shen_syntax kl_V4062 appl_31 kl_V4064))
                                                                                                                                                                                                              appl_32 `pseq` applyWrapper appl_2 [appl_32])))
                                                                                                                                        !appl_33 <- kl_gensym (Types.Atom (Types.UnboundSym "shen.place"))
                                                                                                                                        appl_33 `pseq` applyWrapper appl_1 [appl_33])))
                                                                         !appl_34 <- kl_V4063 `pseq` klCons kl_V4063 (Types.Atom Types.Nil)
                                                                         !appl_35 <- appl_34 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_34
                                                                         !appl_36 <- appl_35 `pseq` klCons appl_35 (Types.Atom Types.Nil)
                                                                         !appl_37 <- appl_36 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_36
                                                                         !appl_38 <- kl_V4063 `pseq` klCons kl_V4063 (Types.Atom Types.Nil)
                                                                         !appl_39 <- appl_38 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_38
                                                                         !appl_40 <- appl_39 `pseq` klCons appl_39 (Types.Atom Types.Nil)
                                                                         !appl_41 <- appl_40 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_40
                                                                         !appl_42 <- appl_41 `pseq` klCons appl_41 (Types.Atom Types.Nil)
                                                                         !appl_43 <- appl_42 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_42
                                                                         !appl_44 <- appl_43 `pseq` klCons appl_43 (Types.Atom Types.Nil)
                                                                         !appl_45 <- appl_37 `pseq` (appl_44 `pseq` klCons appl_37 appl_44)
                                                                         !appl_46 <- appl_45 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_45
                                                                         appl_46 `pseq` applyWrapper appl_0 [appl_46]

kl_shen_decons :: Types.KLValue ->
                  Types.KLContext Types.Env Types.KLValue
kl_shen_decons (!kl_V4066) = do let pat_cond_0 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt = do kl_V4066th `pseq` klCons kl_V4066th (Types.Atom Types.Nil)
                                    pat_cond_1 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt kl_V4066tth = do !appl_2 <- kl_V4066tth `pseq` kl_shen_decons kl_V4066tth
                                                                                                         kl_V4066th `pseq` (appl_2 `pseq` klCons kl_V4066th appl_2)
                                    pat_cond_3 = do do return kl_V4066
                                 in case kl_V4066 of
                                        !(kl_V4066@(Cons (Atom (UnboundSym "cons"))
                                                         (!(kl_V4066t@(Cons (!kl_V4066th)
                                                                            (!(kl_V4066tt@(Cons (Atom (Nil))
                                                                                                (Atom (Nil)))))))))) -> pat_cond_0 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt
                                        !(kl_V4066@(Cons (ApplC (PL "cons" _))
                                                         (!(kl_V4066t@(Cons (!kl_V4066th)
                                                                            (!(kl_V4066tt@(Cons (Atom (Nil))
                                                                                                (Atom (Nil)))))))))) -> pat_cond_0 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt
                                        !(kl_V4066@(Cons (ApplC (Func "cons" _))
                                                         (!(kl_V4066t@(Cons (!kl_V4066th)
                                                                            (!(kl_V4066tt@(Cons (Atom (Nil))
                                                                                                (Atom (Nil)))))))))) -> pat_cond_0 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt
                                        !(kl_V4066@(Cons (Atom (UnboundSym "cons"))
                                                         (!(kl_V4066t@(Cons (!kl_V4066th)
                                                                            (!(kl_V4066tt@(Cons (!kl_V4066tth)
                                                                                                (Atom (Nil)))))))))) -> pat_cond_1 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt kl_V4066tth
                                        !(kl_V4066@(Cons (ApplC (PL "cons" _))
                                                         (!(kl_V4066t@(Cons (!kl_V4066th)
                                                                            (!(kl_V4066tt@(Cons (!kl_V4066tth)
                                                                                                (Atom (Nil)))))))))) -> pat_cond_1 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt kl_V4066tth
                                        !(kl_V4066@(Cons (ApplC (Func "cons" _))
                                                         (!(kl_V4066t@(Cons (!kl_V4066th)
                                                                            (!(kl_V4066tt@(Cons (!kl_V4066tth)
                                                                                                (Atom (Nil)))))))))) -> pat_cond_1 kl_V4066 kl_V4066t kl_V4066th kl_V4066tt kl_V4066tth
                                        _ -> pat_cond_3

kl_shen_insert_runon :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_insert_runon (!kl_V4081) (!kl_V4082) (!kl_V4083) = do let pat_cond_0 kl_V4083 kl_V4083t kl_V4083th kl_V4083tt kl_V4083tth = do return kl_V4081
                                                                  pat_cond_1 kl_V4083 kl_V4083h kl_V4083t = do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_V4081 `pseq` (kl_V4082 `pseq` (kl_Z `pseq` kl_shen_insert_runon kl_V4081 kl_V4082 kl_Z)))))
                                                                                                               appl_2 `pseq` (kl_V4083 `pseq` kl_map appl_2 kl_V4083)
                                                                  pat_cond_3 = do do return kl_V4083
                                                               in case kl_V4083 of
                                                                      !(kl_V4083@(Cons (Atom (UnboundSym "shen.pair"))
                                                                                       (!(kl_V4083t@(Cons (!kl_V4083th)
                                                                                                          (!(kl_V4083tt@(Cons (!kl_V4083tth)
                                                                                                                              (Atom (Nil)))))))))) | eqCore kl_V4083tth kl_V4082 -> pat_cond_0 kl_V4083 kl_V4083t kl_V4083th kl_V4083tt kl_V4083tth
                                                                      !(kl_V4083@(Cons (ApplC (PL "shen.pair"
                                                                                                  _))
                                                                                       (!(kl_V4083t@(Cons (!kl_V4083th)
                                                                                                          (!(kl_V4083tt@(Cons (!kl_V4083tth)
                                                                                                                              (Atom (Nil)))))))))) | eqCore kl_V4083tth kl_V4082 -> pat_cond_0 kl_V4083 kl_V4083t kl_V4083th kl_V4083tt kl_V4083tth
                                                                      !(kl_V4083@(Cons (ApplC (Func "shen.pair"
                                                                                                    _))
                                                                                       (!(kl_V4083t@(Cons (!kl_V4083th)
                                                                                                          (!(kl_V4083tt@(Cons (!kl_V4083tth)
                                                                                                                              (Atom (Nil)))))))))) | eqCore kl_V4083tth kl_V4082 -> pat_cond_0 kl_V4083 kl_V4083t kl_V4083th kl_V4083tt kl_V4083tth
                                                                      !(kl_V4083@(Cons (!kl_V4083h)
                                                                                       (!kl_V4083t))) -> pat_cond_1 kl_V4083 kl_V4083h kl_V4083t
                                                                      _ -> pat_cond_3

kl_shen_strip_pathname :: Types.KLValue ->
                          Types.KLContext Types.Env Types.KLValue
kl_shen_strip_pathname (!kl_V4089) = do !appl_0 <- kl_V4089 `pseq` kl_elementP (Types.Atom (Types.Str ".")) kl_V4089
                                        !kl_if_1 <- appl_0 `pseq` kl_not appl_0
                                        case kl_if_1 of
                                            Atom (B (True)) -> do return kl_V4089
                                            Atom (B (False)) -> do let pat_cond_2 kl_V4089 kl_V4089h kl_V4089t = do kl_V4089t `pseq` kl_shen_strip_pathname kl_V4089t
                                                                       pat_cond_3 = do do let !aw_4 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                          applyWrapper aw_4 [ApplC (wrapNamed "shen.strip-pathname" kl_shen_strip_pathname)]
                                                                    in case kl_V4089 of
                                                                           !(kl_V4089@(Cons (!kl_V4089h)
                                                                                            (!kl_V4089t))) -> pat_cond_2 kl_V4089 kl_V4089h kl_V4089t
                                                                           _ -> pat_cond_3
                                            _ -> throwError "if: expected boolean"

kl_shen_recursive_descent :: Types.KLValue ->
                             Types.KLValue ->
                             Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_recursive_descent (!kl_V4093) (!kl_V4094) (!kl_V4095) = do let pat_cond_0 kl_V4093 kl_V4093h kl_V4093t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do !appl_4 <- kl_V4093h `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V4093h
                                                                                                                                                                                                                                                                                                                   !appl_5 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                   !appl_6 <- kl_V4093h `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V4093h
                                                                                                                                                                                                                                                                                                                   !appl_7 <- appl_6 `pseq` klCons appl_6 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                   !appl_8 <- appl_5 `pseq` (appl_7 `pseq` klCons appl_5 appl_7)
                                                                                                                                                                                                                                                                                                                   !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_8
                                                                                                                                                                                                                                                                                                                   !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                   !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "not" kl_not)) appl_10
                                                                                                                                                                                                                                                                                                                   !appl_12 <- kl_Else `pseq` klCons kl_Else (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                   !appl_13 <- kl_Action `pseq` (appl_12 `pseq` klCons kl_Action appl_12)
                                                                                                                                                                                                                                                                                                                   !appl_14 <- appl_11 `pseq` (appl_13 `pseq` klCons appl_11 appl_13)
                                                                                                                                                                                                                                                                                                                   !appl_15 <- appl_14 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_14
                                                                                                                                                                                                                                                                                                                   !appl_16 <- appl_15 `pseq` klCons appl_15 (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                   !appl_17 <- kl_Test `pseq` (appl_16 `pseq` klCons kl_Test appl_16)
                                                                                                                                                                                                                                                                                                                   !appl_18 <- appl_4 `pseq` (appl_17 `pseq` klCons appl_4 appl_17)
                                                                                                                                                                                                                                                                                                                   appl_18 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_18)))
                                                                                                                                                                                                                                                    !appl_19 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                    appl_19 `pseq` applyWrapper appl_3 [appl_19])))
                                                                                                                                                                                   !appl_20 <- kl_V4093h `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V4093h
                                                                                                                                                                                   !appl_21 <- kl_V4093t `pseq` (appl_20 `pseq` (kl_V4095 `pseq` kl_shen_syntax kl_V4093t appl_20 kl_V4095))
                                                                                                                                                                                   appl_21 `pseq` applyWrapper appl_2 [appl_21])))
                                                                                                                    !appl_22 <- kl_V4094 `pseq` klCons kl_V4094 (Types.Atom Types.Nil)
                                                                                                                    !appl_23 <- kl_V4093h `pseq` (appl_22 `pseq` klCons kl_V4093h appl_22)
                                                                                                                    appl_23 `pseq` applyWrapper appl_1 [appl_23]
                                                                       pat_cond_24 = do do let !aw_25 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                           applyWrapper aw_25 [ApplC (wrapNamed "shen.recursive_descent" kl_shen_recursive_descent)]
                                                                    in case kl_V4093 of
                                                                           !(kl_V4093@(Cons (!kl_V4093h)
                                                                                            (!kl_V4093t))) -> pat_cond_0 kl_V4093 kl_V4093h kl_V4093t
                                                                           _ -> pat_cond_24

kl_shen_variable_match :: Types.KLValue ->
                          Types.KLValue ->
                          Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_variable_match (!kl_V4099) (!kl_V4100) (!kl_V4101) = do let pat_cond_0 kl_V4099 kl_V4099h kl_V4099t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do !appl_4 <- kl_Else `pseq` klCons kl_Else (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                                !appl_5 <- kl_Action `pseq` (appl_4 `pseq` klCons kl_Action appl_4)
                                                                                                                                                                                                                                                                                                                !appl_6 <- kl_Test `pseq` (appl_5 `pseq` klCons kl_Test appl_5)
                                                                                                                                                                                                                                                                                                                appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_6)))
                                                                                                                                                                                                                                                 !appl_7 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                 appl_7 `pseq` applyWrapper appl_3 [appl_7])))
                                                                                                                                                                                !appl_8 <- kl_V4099h `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V4099h
                                                                                                                                                                                !appl_9 <- kl_V4100 `pseq` klCons kl_V4100 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_10 <- appl_9 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_9
                                                                                                                                                                                !appl_11 <- appl_10 `pseq` klCons appl_10 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_12 <- appl_11 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_11
                                                                                                                                                                                !appl_13 <- kl_V4100 `pseq` klCons kl_V4100 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_14 <- appl_13 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_13
                                                                                                                                                                                !appl_15 <- appl_14 `pseq` klCons appl_14 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_15
                                                                                                                                                                                !appl_17 <- kl_V4100 `pseq` klCons kl_V4100 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_18 <- appl_17 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_17
                                                                                                                                                                                !appl_19 <- appl_18 `pseq` klCons appl_18 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_20 <- appl_16 `pseq` (appl_19 `pseq` klCons appl_16 appl_19)
                                                                                                                                                                                !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_20
                                                                                                                                                                                !appl_22 <- kl_V4099t `pseq` (appl_21 `pseq` (kl_V4101 `pseq` kl_shen_syntax kl_V4099t appl_21 kl_V4101))
                                                                                                                                                                                !appl_23 <- appl_22 `pseq` klCons appl_22 (Types.Atom Types.Nil)
                                                                                                                                                                                !appl_24 <- appl_12 `pseq` (appl_23 `pseq` klCons appl_12 appl_23)
                                                                                                                                                                                !appl_25 <- appl_8 `pseq` (appl_24 `pseq` klCons appl_8 appl_24)
                                                                                                                                                                                !appl_26 <- appl_25 `pseq` klCons (Types.Atom (Types.UnboundSym "let")) appl_25
                                                                                                                                                                                appl_26 `pseq` applyWrapper appl_2 [appl_26])))
                                                                                                                 !appl_27 <- kl_V4100 `pseq` klCons kl_V4100 (Types.Atom Types.Nil)
                                                                                                                 !appl_28 <- appl_27 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_27
                                                                                                                 !appl_29 <- appl_28 `pseq` klCons appl_28 (Types.Atom Types.Nil)
                                                                                                                 !appl_30 <- appl_29 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_29
                                                                                                                 appl_30 `pseq` applyWrapper appl_1 [appl_30]
                                                                    pat_cond_31 = do do let !aw_32 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                        applyWrapper aw_32 [ApplC (wrapNamed "shen.variable-match" kl_shen_variable_match)]
                                                                 in case kl_V4099 of
                                                                        !(kl_V4099@(Cons (!kl_V4099h)
                                                                                         (!kl_V4099t))) -> pat_cond_0 kl_V4099 kl_V4099h kl_V4099t
                                                                        _ -> pat_cond_31

kl_shen_terminalP :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_terminalP (!kl_V4111) = do let pat_cond_0 kl_V4111 kl_V4111h kl_V4111t = do return (Atom (B False))
                                       pat_cond_1 = do !kl_if_2 <- kl_V4111 `pseq` kl_variableP kl_V4111
                                                       case kl_if_2 of
                                                           Atom (B (True)) -> do return (Atom (B False))
                                                           Atom (B (False)) -> do do return (Atom (B True))
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V4111 of
                                           !(kl_V4111@(Cons (!kl_V4111h)
                                                            (!kl_V4111t))) -> pat_cond_0 kl_V4111 kl_V4111h kl_V4111t
                                           _ -> pat_cond_1

kl_shen_jump_streamP :: Types.KLValue ->
                        Types.KLContext Types.Env Types.KLValue
kl_shen_jump_streamP (!kl_V4117) = do let pat_cond_0 = do return (Atom (B True))
                                          pat_cond_1 = do do return (Atom (B False))
                                       in case kl_V4117 of
                                              kl_V4117@(Atom (UnboundSym "_")) -> pat_cond_0
                                              kl_V4117@(ApplC (PL "_" _)) -> pat_cond_0
                                              kl_V4117@(ApplC (Func "_" _)) -> pat_cond_0
                                              _ -> pat_cond_1

kl_shen_check_stream :: Types.KLValue ->
                        Types.KLValue ->
                        Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_check_stream (!kl_V4121) (!kl_V4122) (!kl_V4123) = do let pat_cond_0 kl_V4121 kl_V4121h kl_V4121t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do !appl_4 <- kl_Else `pseq` klCons kl_Else (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                              !appl_5 <- kl_Action `pseq` (appl_4 `pseq` klCons kl_Action appl_4)
                                                                                                                                                                                                                                                                                                              !appl_6 <- kl_Test `pseq` (appl_5 `pseq` klCons kl_Test appl_5)
                                                                                                                                                                                                                                                                                                              appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_6)))
                                                                                                                                                                                                                                               !appl_7 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                               appl_7 `pseq` applyWrapper appl_3 [appl_7])))
                                                                                                                                                                              !appl_8 <- kl_V4122 `pseq` klCons kl_V4122 (Types.Atom Types.Nil)
                                                                                                                                                                              !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_8
                                                                                                                                                                              !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                                                                                              !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_10
                                                                                                                                                                              !appl_12 <- kl_V4122 `pseq` klCons kl_V4122 (Types.Atom Types.Nil)
                                                                                                                                                                              !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_12
                                                                                                                                                                              !appl_14 <- appl_13 `pseq` klCons appl_13 (Types.Atom Types.Nil)
                                                                                                                                                                              !appl_15 <- appl_11 `pseq` (appl_14 `pseq` klCons appl_11 appl_14)
                                                                                                                                                                              !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_15
                                                                                                                                                                              !appl_17 <- kl_V4121t `pseq` (appl_16 `pseq` (kl_V4123 `pseq` kl_shen_syntax kl_V4121t appl_16 kl_V4123))
                                                                                                                                                                              appl_17 `pseq` applyWrapper appl_2 [appl_17])))
                                                                                                               !appl_18 <- kl_V4122 `pseq` klCons kl_V4122 (Types.Atom Types.Nil)
                                                                                                               !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_18
                                                                                                               !appl_20 <- appl_19 `pseq` klCons appl_19 (Types.Atom Types.Nil)
                                                                                                               !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_20
                                                                                                               !appl_22 <- kl_V4122 `pseq` klCons kl_V4122 (Types.Atom Types.Nil)
                                                                                                               !appl_23 <- appl_22 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_22
                                                                                                               !appl_24 <- appl_23 `pseq` klCons appl_23 (Types.Atom Types.Nil)
                                                                                                               !appl_25 <- appl_24 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_24
                                                                                                               !appl_26 <- appl_25 `pseq` klCons appl_25 (Types.Atom Types.Nil)
                                                                                                               !appl_27 <- kl_V4121h `pseq` (appl_26 `pseq` klCons kl_V4121h appl_26)
                                                                                                               !appl_28 <- appl_27 `pseq` klCons (ApplC (wrapNamed "=" eq)) appl_27
                                                                                                               !appl_29 <- appl_28 `pseq` klCons appl_28 (Types.Atom Types.Nil)
                                                                                                               !appl_30 <- appl_21 `pseq` (appl_29 `pseq` klCons appl_21 appl_29)
                                                                                                               !appl_31 <- appl_30 `pseq` klCons (Types.Atom (Types.UnboundSym "and")) appl_30
                                                                                                               appl_31 `pseq` applyWrapper appl_1 [appl_31]
                                                                  pat_cond_32 = do do let !aw_33 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                      applyWrapper aw_33 [ApplC (wrapNamed "shen.check_stream" kl_shen_check_stream)]
                                                               in case kl_V4121 of
                                                                      !(kl_V4121@(Cons (!kl_V4121h)
                                                                                       (!kl_V4121t))) -> pat_cond_0 kl_V4121 kl_V4121h kl_V4121t
                                                                      _ -> pat_cond_32

kl_shen_jump_stream :: Types.KLValue ->
                       Types.KLValue ->
                       Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_jump_stream (!kl_V4127) (!kl_V4128) (!kl_V4129) = do let pat_cond_0 kl_V4127 kl_V4127h kl_V4127t = do let !appl_1 = ApplC (Func "lambda" (Context (\(!kl_Test) -> do let !appl_2 = ApplC (Func "lambda" (Context (\(!kl_Action) -> do let !appl_3 = ApplC (Func "lambda" (Context (\(!kl_Else) -> do !appl_4 <- kl_Else `pseq` klCons kl_Else (Types.Atom Types.Nil)
                                                                                                                                                                                                                                                                                                             !appl_5 <- kl_Action `pseq` (appl_4 `pseq` klCons kl_Action appl_4)
                                                                                                                                                                                                                                                                                                             !appl_6 <- kl_Test `pseq` (appl_5 `pseq` klCons kl_Test appl_5)
                                                                                                                                                                                                                                                                                                             appl_6 `pseq` klCons (Types.Atom (Types.UnboundSym "if")) appl_6)))
                                                                                                                                                                                                                                              !appl_7 <- klCons (ApplC (PL "fail" kl_fail)) (Types.Atom Types.Nil)
                                                                                                                                                                                                                                              appl_7 `pseq` applyWrapper appl_3 [appl_7])))
                                                                                                                                                                             !appl_8 <- kl_V4128 `pseq` klCons kl_V4128 (Types.Atom Types.Nil)
                                                                                                                                                                             !appl_9 <- appl_8 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_8
                                                                                                                                                                             !appl_10 <- appl_9 `pseq` klCons appl_9 (Types.Atom Types.Nil)
                                                                                                                                                                             !appl_11 <- appl_10 `pseq` klCons (ApplC (wrapNamed "tl" tl)) appl_10
                                                                                                                                                                             !appl_12 <- kl_V4128 `pseq` klCons kl_V4128 (Types.Atom Types.Nil)
                                                                                                                                                                             !appl_13 <- appl_12 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_12
                                                                                                                                                                             !appl_14 <- appl_13 `pseq` klCons appl_13 (Types.Atom Types.Nil)
                                                                                                                                                                             !appl_15 <- appl_11 `pseq` (appl_14 `pseq` klCons appl_11 appl_14)
                                                                                                                                                                             !appl_16 <- appl_15 `pseq` klCons (ApplC (wrapNamed "shen.pair" kl_shen_pair)) appl_15
                                                                                                                                                                             !appl_17 <- kl_V4127t `pseq` (appl_16 `pseq` (kl_V4129 `pseq` kl_shen_syntax kl_V4127t appl_16 kl_V4129))
                                                                                                                                                                             appl_17 `pseq` applyWrapper appl_2 [appl_17])))
                                                                                                              !appl_18 <- kl_V4128 `pseq` klCons kl_V4128 (Types.Atom Types.Nil)
                                                                                                              !appl_19 <- appl_18 `pseq` klCons (ApplC (wrapNamed "hd" hd)) appl_18
                                                                                                              !appl_20 <- appl_19 `pseq` klCons appl_19 (Types.Atom Types.Nil)
                                                                                                              !appl_21 <- appl_20 `pseq` klCons (ApplC (wrapNamed "cons?" consP)) appl_20
                                                                                                              appl_21 `pseq` applyWrapper appl_1 [appl_21]
                                                                 pat_cond_22 = do do let !aw_23 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                                                     applyWrapper aw_23 [ApplC (wrapNamed "shen.jump_stream" kl_shen_jump_stream)]
                                                              in case kl_V4127 of
                                                                     !(kl_V4127@(Cons (!kl_V4127h)
                                                                                      (!kl_V4127t))) -> pat_cond_0 kl_V4127 kl_V4127h kl_V4127t
                                                                     _ -> pat_cond_22

kl_shen_semantics :: Types.KLValue ->
                     Types.KLContext Types.Env Types.KLValue
kl_shen_semantics (!kl_V4131) = do let pat_cond_0 = do return (Types.Atom Types.Nil)
                                       pat_cond_1 = do !kl_if_2 <- kl_V4131 `pseq` kl_shen_grammar_symbolP kl_V4131
                                                       case kl_if_2 of
                                                           Atom (B (True)) -> do !appl_3 <- kl_V4131 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V4131
                                                                                 !appl_4 <- appl_3 `pseq` klCons appl_3 (Types.Atom Types.Nil)
                                                                                 appl_4 `pseq` klCons (ApplC (wrapNamed "shen.hdtl" kl_shen_hdtl)) appl_4
                                                           Atom (B (False)) -> do !kl_if_5 <- kl_V4131 `pseq` kl_variableP kl_V4131
                                                                                  case kl_if_5 of
                                                                                      Atom (B (True)) -> do kl_V4131 `pseq` kl_concat (Types.Atom (Types.UnboundSym "Parse_")) kl_V4131
                                                                                      Atom (B (False)) -> do let pat_cond_6 kl_V4131 kl_V4131h kl_V4131t = do let !appl_7 = ApplC (Func "lambda" (Context (\(!kl_Z) -> do kl_Z `pseq` kl_shen_semantics kl_Z)))
                                                                                                                                                              appl_7 `pseq` (kl_V4131 `pseq` kl_map appl_7 kl_V4131)
                                                                                                                 pat_cond_8 = do do return kl_V4131
                                                                                                              in case kl_V4131 of
                                                                                                                     !(kl_V4131@(Cons (!kl_V4131h)
                                                                                                                                      (!kl_V4131t))) -> pat_cond_6 kl_V4131 kl_V4131h kl_V4131t
                                                                                                                     _ -> pat_cond_8
                                                                                      _ -> throwError "if: expected boolean"
                                                           _ -> throwError "if: expected boolean"
                                    in case kl_V4131 of
                                           kl_V4131@(Atom (Nil)) -> pat_cond_0
                                           _ -> pat_cond_1

kl_shen_snd_or_fail :: Types.KLValue ->
                       Types.KLContext Types.Env Types.KLValue
kl_shen_snd_or_fail (!kl_V4139) = do let pat_cond_0 kl_V4139 kl_V4139h kl_V4139t kl_V4139th = do return kl_V4139th
                                         pat_cond_1 = do do kl_fail
                                      in case kl_V4139 of
                                             !(kl_V4139@(Cons (!kl_V4139h)
                                                              (!(kl_V4139t@(Cons (!kl_V4139th)
                                                                                 (Atom (Nil))))))) -> pat_cond_0 kl_V4139 kl_V4139h kl_V4139t kl_V4139th
                                             _ -> pat_cond_1

kl_fail :: Types.KLContext Types.Env Types.KLValue
kl_fail = do return (Types.Atom (Types.UnboundSym "shen.fail!"))

kl_shen_pair :: Types.KLValue ->
                Types.KLValue -> Types.KLContext Types.Env Types.KLValue
kl_shen_pair (!kl_V4142) (!kl_V4143) = do !appl_0 <- kl_V4143 `pseq` klCons kl_V4143 (Types.Atom Types.Nil)
                                          kl_V4142 `pseq` (appl_0 `pseq` klCons kl_V4142 appl_0)

kl_shen_hdtl :: Types.KLValue ->
                Types.KLContext Types.Env Types.KLValue
kl_shen_hdtl (!kl_V4145) = do !appl_0 <- kl_V4145 `pseq` tl kl_V4145
                              appl_0 `pseq` hd appl_0

kl_shen_LBExclRB :: Types.KLValue ->
                    Types.KLContext Types.Env Types.KLValue
kl_shen_LBExclRB (!kl_V4153) = do let pat_cond_0 kl_V4153 kl_V4153h kl_V4153t kl_V4153th = do !appl_1 <- kl_V4153h `pseq` klCons kl_V4153h (Types.Atom Types.Nil)
                                                                                              appl_1 `pseq` klCons (Types.Atom Types.Nil) appl_1
                                      pat_cond_2 = do do kl_fail
                                   in case kl_V4153 of
                                          !(kl_V4153@(Cons (!kl_V4153h)
                                                           (!(kl_V4153t@(Cons (!kl_V4153th)
                                                                              (Atom (Nil))))))) -> pat_cond_0 kl_V4153 kl_V4153h kl_V4153t kl_V4153th
                                          _ -> pat_cond_2

kl_LBeRB :: Types.KLValue ->
            Types.KLContext Types.Env Types.KLValue
kl_LBeRB (!kl_V4159) = do let pat_cond_0 kl_V4159 kl_V4159h kl_V4159t kl_V4159th = do !appl_1 <- klCons (Types.Atom Types.Nil) (Types.Atom Types.Nil)
                                                                                      kl_V4159h `pseq` (appl_1 `pseq` klCons kl_V4159h appl_1)
                              pat_cond_2 = do do let !aw_3 = Types.Atom (Types.UnboundSym "shen.f_error")
                                                 applyWrapper aw_3 [ApplC (wrapNamed "<e>" kl_LBeRB)]
                           in case kl_V4159 of
                                  !(kl_V4159@(Cons (!kl_V4159h)
                                                   (!(kl_V4159t@(Cons (!kl_V4159th)
                                                                      (Atom (Nil))))))) -> pat_cond_0 kl_V4159 kl_V4159h kl_V4159t kl_V4159th
                                  _ -> pat_cond_2

expr4 :: Types.KLContext Types.Env Types.KLValue
expr4 = do (do return (Types.Atom (Types.Str "Copyright (c) 2015, Mark Tarver\n\nAll rights reserved.\n\nRedistribution and use in source and binary forms, with or without\nmodification, are permitted provided that the following conditions are met:\n1. Redistributions of source code must retain the above copyright\n   notice, this list of conditions and the following disclaimer.\n2. Redistributions in binary form must reproduce the above copyright\n   notice, this list of conditions and the following disclaimer in the\n   documentation and/or other materials provided with the distribution.\n3. The name of Mark Tarver may not be used to endorse or promote products\n   derived from this software without specific prior written permission.\n\nTHIS SOFTWARE IS PROVIDED BY Mark Tarver ''AS IS'' AND ANY\nEXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED\nWARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE\nDISCLAIMED. IN NO EVENT SHALL Mark Tarver BE LIABLE FOR ANY\nDIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES\n(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;\nLOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND\nON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT\n(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS\nSOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE."))) `catchError` (\(!kl_E) -> do return (Types.Atom (Types.Str "E")))
