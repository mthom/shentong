{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Utils where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Data.HashMap as HM
import Data.IORef
import Data.Maybe
import Data.Monoid
import qualified Data.Vector as V
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Prelude as P
import Types

exceptionV :: ErrorMsg -> KLValue -> KLContext s KLValue
exceptionV e v = throwError e'
    where e' = e <> " " <> (T.pack $ show v)

stubFunction :: Monad m => Symbol -> m ApplContext
stubFunction name = return (Malformed msg)
    where msg = "function " <> name <> " is not defined"

functionRef :: (MonadIO m, MonadState Env m) => Symbol -> m (IORef ApplContext)
functionRef name = do
  st <- get
  case HM.lookup name (functionTable st) of
    Just ref -> return ref
    Nothing  -> do
      stubFunction name >>= insertFunction name
      functionRef name

symbolRef :: (MonadState Env m, MonadError ErrorMsg m) => Symbol -> m KLValue
symbolRef name = do
  st <- get
  case HM.lookup name (symbolTable st) of
    Just v  -> return v
    Nothing -> throwError "name not found in symbol table."

insertFunction :: (MonadState Env m, MonadIO m) => Symbol -> ApplContext -> m ()
insertFunction name f = do
  st <- get
  case HM.lookup name (functionTable st) of
    Just ref -> liftIO $ writeIORef ref $! f
    Nothing  -> do
      ref <- liftIO $ newIORef $! f
      put $ st { functionTable = HM.insert name ref (functionTable st) }

insertSymbol :: MonadState Env m => Symbol -> KLValue -> m ()
insertSymbol name v = do
  st <- get
  put $ st { symbolTable = HM.insert name v (symbolTable st) }

addVal :: Int -> Bindings -> KLValue -> Bindings
addVal i vals v = replace vals
  where replace (p@(i',_) : is') 
          | i == i'   = (i,v) : is'
          | otherwise = p : replace is'
        replace [] = [(i,v)]

lookupVal :: DeBruijn -> Bindings -> KLContext s KLValue
lookupVal i vals = maybe err return (P.lookup i vals)
    where err = throwError "value not found in bindings list"

fromIORef :: MonadIO m => IORef a -> m a
fromIORef = liftIO . readIORef

apply :: Function -> KLValue -> ApplContext
apply (PartialApp f) v = Func (f v)
apply (Context f) v = PL (f v)

mapM' :: Monad m => (a-> m b) -> [a] -> m [b]
mapM' _ []     = return []
mapM' f (x:xs) = do
  y  <- f x
  ys <- y `seq` mapM' f xs
  return (y:ys)

checkForBooleans :: Atom -> KLValue
checkForBooleans (UnboundSym "true")  = Atom (B True)
checkForBooleans (UnboundSym "false") = Atom (B False)  
checkForBooleans a = Atom a
