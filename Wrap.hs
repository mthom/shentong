{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Wrap where

import Types

class Wrappable a where
  wrap :: a -> Function
  encode :: [Int] -> a -> Function

instance Wrappable (KLValue -> a) => Wrappable (KLValue -> KLValue -> a) where
  wrap f = PartialApp (wrap . f)
                
  encode [] f           = wrap f
  encode (!i : (!is)) f = construct (encode (map ((-) 1) is) . f)
    where construct | i == 0    = ExceptionHandler . PartialApp
                    | otherwise = PartialApp

instance (s ~ Env, m ~ IO) => Wrappable (KLValue -> KLContext s m KLValue) where
  wrap = Context

  encode is f = construct f
    where construct | is == [0] = ExceptionHandler . wrap
                    | is == []  = wrap
                    | otherwise = error "encode: too many indices."
