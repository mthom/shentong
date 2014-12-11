{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Interpreter ( evalTopLevel ) where

import AST
import Control.Monad.Except
import Control.Monad.Fix
import Data.IORef
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Vector as V
import Types
import Utils
import Wrap

evalTopLevel :: TopLevel -> KLContext Env IO KLValue
evalTopLevel (SE se) = process (reduceSExpr [] se) (runKLC . eval V.empty)
evalTopLevel (Defun name args body) = evalDefun name args body

evalDefun :: Symbol -> ParamList -> SExpr -> KLContext Env IO KLValue
evalDefun name args body = process go return -- (return . ApplC)
    where go = do
            body' <- reduceSExpr args body
            mfix $ \f -> do
                 insertFunction name f
                 topLevelContext name (length args) body'
            return (Atom (UnboundSym name))

topLevelContext :: Monad m => Symbol -> Int -> RSExpr -> m ApplContext
topLevelContext name 0 e = return (PL (runKLC (eval V.empty e)))
topLevelContext name n e = return (Func (buildContext n V.empty))
    where buildContext 1 vals = Context (\x -> runKLC (eval (V.snoc vals x) e))
          buildContext n vals = PartialApp fn
              where fn x = buildContext (n-1) (V.snoc vals x)

eval :: Bindings -> RSExpr -> KLCont Env IO KLValue
eval vals (RDeBruijn db)   = lookupVal db vals
eval vals (RFreeze e)      = evalFreeze vals e
eval vals (RLambda i e)    = evalLambda vals i e
eval vals (RIf c t f)      = evalIf vals c t f
eval vals (RApplDir f as)  = evalApplDir vals f as
eval vals (RApplForm a as) = evalApplForm vals a as
eval vals (RLit a)         = return (checkForBooleans a)
eval vals REmptyList       = return (List [])

checkForBooleans :: Atom -> KLValue
checkForBooleans (UnboundSym "true")  = Atom (B True)
checkForBooleans (UnboundSym "false") = Atom (B False)  
checkForBooleans a = Atom a

evalFreeze :: Bindings -> RSExpr -> KLCont Env IO KLValue
evalFreeze vals e = return (ApplC (PL (runKLC (eval vals e))))

evalLambda :: Monad m => Bindings -> DeBruijn -> RSExpr -> m KLValue
evalLambda vals i = return . ApplC . Func . evalLambda' vals i
    where evalLambda' vals i e
              | RLambda i' e' <- e = PartialApp (contLambda i' e')
              | otherwise = Context termLambda
              where termLambda x = runKLC (eval (addVal i vals x) e)
                    contLambda i' e' x = evalLambda' (addVal i vals x) i' e'

evalApplDir' :: Bindings -> ApplContext -> [RSExpr] -> KLCont Env IO KLValue
evalApplDir' vals ac args = mapM' (eval vals) args >>= liftKLC . applyList ac

evalApplDir :: Bindings -> IORef ApplContext -> [RSExpr] -> KLCont Env IO KLValue
evalApplDir vals ref args = fromIORef ref >>= \ac -> evalApplDir' vals ac args

evalApplForm :: Bindings -> RSExpr -> [RSExpr] -> KLCont Env IO KLValue
evalApplForm vals (RLit (UnboundSym name)) args =
    functionRef name >>= \ac -> evalApplDir vals ac args    
evalApplForm vals form args =
    eval vals form >>= \case
         ApplC ac -> evalApplDir' vals ac args
         Atom (UnboundSym n) -> evalApplForm vals (RLit (UnboundSym n)) args
         v -> exceptionV "(form . args): form evaluates to" v

evalIf :: Bindings -> RSExpr -> RSExpr -> RSExpr -> KLCont Env IO KLValue
evalIf vals c t f =
    eval vals c >>= \case
         Atom (B True)  -> eval vals t
         Atom (B False) -> eval vals f
         _              -> exception "(if c t f): c must evaluate to boolean"

applyList :: ApplContext -> [KLValue] -> KLContext Env IO KLValue
applyList (Malformed e) _ = exception e
applyList (PL c)   [] = c
applyList f        [] = return (ApplC f)
applyList (Func f) (v:vs) = applyList (apply f v) vs
applyList _ _ = exception "too many arguments"
