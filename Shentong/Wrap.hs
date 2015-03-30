{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Shentong.Wrap where

import Shentong.Types

class Wrappable a where
  wrap :: a -> Function

instance Wrappable (KLValue -> a) => Wrappable (KLValue -> KLValue -> a) where
  wrap f = PartialApp (wrap . f)
                
instance s ~ Env => Wrappable (KLValue -> KLContext s KLValue) where
  wrap = Context

wrapNamed :: Wrappable a => Symbol -> a -> ApplContext
wrapNamed name fn = Func name (wrap fn)
