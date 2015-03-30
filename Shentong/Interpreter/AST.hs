{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Shentong.Interpreter.AST ( reduceSExpr, bakeFreeVars ) where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.Generics.Uniplate.Operations
import Data.Traversable
import Shentong.Types
import Shentong.Utils

reduceSExpr :: ParamList -> SExpr -> KLContext Env RSExpr
reduceSExpr args body = markBoundVars args (bakeFreeVars args body)

markBoundVars :: ParamList -> SExpr -> KLContext Env RSExpr
markBoundVars args = bake (length args) (zip args [0..])
    where klTrue = Lit (B True)
          klFalse = Lit (B False)

          bake n args (Sym s)
              | Just i <- lookup s args = pure (RDeBruijn i)
              | otherwise = throwError "found bound symbol, should be a literal"
          bake n args (Lambda s e)
              | Just i <- lookup s args = RLambda i <$> bake n args e
              | otherwise = RLambda n <$> bake (n+1) ((s,n):args) e
          bake n args (Let v b e) = bake n args (Appl [Lambda v e, b])
          bake n args (Lit a) = pure (RLit a)
          bake n args (Freeze e) = RFreeze <$> bake n args e
          bake n args (TrapError e tr) =
              RTrapError <$> bake n args e <*> bake n args tr
          bake n args (If c t f) =
              RIf <$> bake n args c <*> bake n args t <*> bake n args f
          bake n args (And c1 c2) =
              bake n args (If c1 (If c2 klTrue klFalse) klFalse)
          bake n args (Or c1 c2) =
              bake n args (If c1 klTrue (If c2 klTrue klFalse))
          bake n args (Cond ((c,e):cs)) = bake n args (If c e (Cond cs))
          bake n args (Cond []) = pure REmptyList
          bake n args (Appl [Lit (UnboundSym "read-byte")]) =
              bake n args (Appl [Lit (UnboundSym "read-byte"),
                                 Appl [Lit (UnboundSym "stinput")]])
          bake n args (Appl [Lit (UnboundSym "write-byte"), b]) =
              bake n args (Appl [Lit (UnboundSym "write-byte"), b,
                                 Appl [Lit (UnboundSym "stoutput")]])
          bake n args (Appl (Lit (UnboundSym a):as)) =
              RApplDir <$> functionRef a <*> traverse (bake n args) as
          bake n args (Appl (a:as)) =
              RApplForm <$> bake n args a <*> traverse (bake n args) as
          bake n args (Appl []) = bake n args EmptyList
          bake n args EmptyList = pure REmptyList
                         
bakeFreeVars :: ParamList -> SExpr -> SExpr
bakeFreeVars = bake'
    where bake' args (Lambda sym expr) =
              Lambda sym (bake' (sym:args) expr)
          bake' args (Let sym bind expr) =
              bake' args (Appl [Lambda sym expr, bind])
          bake' args (Sym sym)
              | sym `elem` args = Sym sym
              | otherwise = Lit (UnboundSym sym)
          bake' args expr = descend (bake' args) expr
