{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Shentong.Backend.Utils where

import Control.Monad.Except
import Control.Parallel
import qualified Data.Text as T
import Data.Monoid
import Shentong.Primitives
import Shentong.Types
import Shentong.Utils

applyWrapper :: KLValue -> [KLValue] -> KLContext Env KLValue
applyWrapper (ApplC ac) vs = ac `pseq` vs `pseq` foldr pseq (apply ac vs) vs
applyWrapper (Atom (UnboundSym fname)) vs = do
                ac <- fromIORef =<< functionRef fname
                ac `pseq` vs `pseq` foldr pseq (apply ac vs) vs
applyWrapper v _ = throwError $ "applyWrapper: expected fn in leading value, received" <> (T.pack $ show v)
