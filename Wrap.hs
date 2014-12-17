{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Wrap where

import Types

class Wrappable a where
  wrap :: a -> Function

instance Wrappable (KLValue -> a) => Wrappable (KLValue -> KLValue -> a) where
  wrap f = PartialApp (wrap . f)
                
instance s ~ Env => Wrappable (KLValue -> KLContext s KLValue) where
  wrap = Context
