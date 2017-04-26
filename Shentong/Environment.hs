{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Environment ( initEnv, evalKL ) where

import Control.Applicative
import Control.Monad.Except
import qualified Data.HashMap as HM
import Data.IORef
import Data.Traversable hiding (mapM)
import qualified Data.Vector as V
import Interpreter.Interpreter
import Core.Primitives
import System.IO
import Core.Types
import Core.Utils
import Wrap

valueToTopLevel :: KLValue -> KLContext Env TopLevel
valueToTopLevel (Cons (Atom (UnboundSym "defun"))
                      (Cons (Atom (UnboundSym name))
                            (Cons args (Cons e (Atom Nil))))) =
    Defun name <$> toParamList args <*> valueToSExpr e
    where toParamList (Cons (Atom (UnboundSym a)) as) = (a :) <$> toParamList as
          toParamList (Atom Nil) = pure []
          toParamList _  = throwError "defun form contains invalid lambda list"
valueToTopLevel se = SE <$> valueToSExpr se

valueToSExpr :: KLValue -> KLContext Env SExpr
valueToSExpr (ApplC (PL name _)) = return (Sym name)
valueToSExpr (ApplC (Func name _)) = return (Sym name)
valueToSExpr (Atom (UnboundSym sym)) = return (Sym sym)
valueToSExpr (Atom Nil) = return EmptyList
valueToSExpr (Atom a) = return (Lit a)
valueToSExpr (Cons v vs) = applToSExpr v (consToList vs)
    where consToList (Cons v vs) = v : consToList vs
          consToList (Atom Nil)  = []
          consToList v = [v]
valueToSExpr (Vec v)
  | V.null v  = pure emptyVec
  | otherwise = vecToSExprList (V.tail v)
    where emptyVec = Appl [Lit (UnboundSym "vector"), Lit (N (KI 0))]
          
          vecToSExprList vec 
            | V.null vec = pure emptyVec
            | otherwise  = do
                se <- valueToSExpr (V.head vec)
                ss <- vecToSExprList (V.tail vec)
                return (Appl [Lit (UnboundSym "@v"), se , ss])
valueToSExpr v = throwError "cannot evaluate list containing non-literal values"

applToSExpr :: KLValue -> [KLValue] -> KLContext Env SExpr
applToSExpr (Atom (UnboundSym "cond")) l = Cond <$> listOfConds l
    where listOfConds (Cons cond (Cons clause (Atom Nil)) : cs) =
              (:) <$> ((,) <$> valueToSExpr cond <*> valueToSExpr clause)
                  <*> listOfConds cs
          listOfConds [] = pure []
          listOfConds _  = throwError "improperly formed cond clause list"
applToSExpr (Atom (UnboundSym "if")) [c,t,f] =
    If <$> valueToSExpr c <*> valueToSExpr t <*> valueToSExpr f
applToSExpr (Atom (UnboundSym "let")) [Atom (UnboundSym s),b,e] =
    Let s <$> valueToSExpr b <*> valueToSExpr e
applToSExpr (Atom (UnboundSym "lambda")) [Atom (UnboundSym s), e] =
    Lambda s <$> valueToSExpr e
applToSExpr (Atom (UnboundSym "and")) [c1,c2] =
    And <$> valueToSExpr c1 <*> valueToSExpr c2
applToSExpr (Atom (UnboundSym "or")) [c1,c2] =
    Or <$> valueToSExpr c1 <*> valueToSExpr c2
applToSExpr (Atom (UnboundSym "freeze")) [e] =
    Freeze <$> valueToSExpr e
applToSExpr (Atom (UnboundSym "trap-error")) [e, h] =
    TrapError <$> valueToSExpr e <*> valueToSExpr h
applToSExpr l ls =
    Appl <$> liftA2 (:) (valueToSExpr l) (traverse valueToSExpr ls)

evalKL :: KLValue -> KLContext Env KLValue
evalKL = valueToTopLevel >=> evalTopLevel

primitives :: [(Symbol, Function)]
primitives = [("intern", wrap intern),
              ("pos", wrap pos),
              ("tlstr", wrap tlstr),
              ("cn", wrap cn),
              ("str", wrap str),
              ("string?", wrap stringP),
              ("n->string", wrap nToString),
              ("string->n", wrap stringToN),
              ("set", wrap klSet),
              ("value", wrap value),
              ("simple-error", wrap simpleError),
              ("error-to-string", wrap errorToString),
              ("cons", wrap klCons),
              ("hd", wrap hd),
              ("tl", wrap tl),
              ("cons?", wrap consP),
              ("=", wrap eq),
              ("type", wrap typeA),
              ("absvector", wrap absvector),
              ("address->", wrap addressTo),
              ("<-address", wrap addressFrom),
              ("absvector?", wrap absvectorP),
              ("write-byte", wrap writeByte),
              ("read-byte", wrap readByte),
              ("open", wrap openStream),
              ("close", wrap closeStream),
              ("get-time", wrap getTime),
              ("+", wrap add),
              ("-", wrap Core.Primitives.subtract),
              ("*", wrap multiply),
              ("/", wrap divide),
              (">", wrap greaterThan),
              ("<", wrap lessThan),
              (">=", wrap greaterThanOrEqualTo),
              ("<=", wrap lessThanOrEqualTo),   
              ("number?", wrap numberP),
              ("eval-kl", wrap evalKL)]

initEnv :: (Applicative m, MonadIO m) => m Env
initEnv = Env initSymbolTable <$> HM.fromList <$> mapM update primitives
    where update (n, f) = (n,) <$> liftIO (newIORef $! Func n f)

initSymbolTable :: HM.Map Symbol KLValue
initSymbolTable = HM.fromList [("*stoutput*", OutStream stdout),
                               ("*stinput*", InStream stdin)]
