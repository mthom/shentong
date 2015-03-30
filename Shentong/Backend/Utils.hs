{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Shentong.Backend.Utils where

import Control.Monad.Except
import Control.Parallel
import Data.List
import qualified Data.Text as T
import Data.Monoid
import qualified Data.Vector as V
import Shentong.Primitives
import Shentong.Types
import Shentong.Utils

klIf :: KLValue -> KLContext Env KLValue -> KLContext Env KLValue -> KLContext Env KLValue
klIf (Atom (B True)) tc _  = tc
klIf (Atom (B False)) _ fc = fc
klIf _ _ _ = throwError "klIf: expected a boolean value in first arg"

applyWrapper :: KLValue -> [KLValue] -> KLContext Env KLValue
applyWrapper (ApplC ac) vs = foldr pseq (apply ac vs) vs
applyWrapper (Atom (UnboundSym fname)) vs = do
                ac <- fromIORef =<< functionRef fname
                foldr pseq (apply ac vs) vs
applyWrapper v _ = 
  throwError $ "applyWrapper: expected fn in leading value, received" <> 
  (T.pack $ show v)
