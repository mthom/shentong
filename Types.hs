{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Types where

import Control.Applicative
import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Data
import Data.Generics.Uniplate.Data
import Data.HashMap as HM
import Data.IORef
import qualified Data.Text as T
import Data.Vector as V hiding ((++))
import System.IO

type Symbol = T.Text
type ErrorMsg = T.Text
type ParamList = [Symbol]

data SExpr = Lit !Atom
           | Sym !Symbol
           | Freeze !SExpr
           | Let !Symbol !SExpr !SExpr
           | Lambda !Symbol !SExpr
           | If !SExpr !SExpr !SExpr
           | And !SExpr !SExpr
           | Or !SExpr !SExpr
           | Cond ![(SExpr,SExpr)]
           | Appl ![SExpr]
           | EmptyList
             deriving (Data, Typeable)

type DeBruijn = Int
type Bindings = Vector KLValue

data RSExpr = RLit !Atom
            | RDeBruijn !DeBruijn
            | RFreeze !RSExpr
            | RLambda !DeBruijn !RSExpr
            | RIf !RSExpr !RSExpr !RSExpr
            | RApplDir !(IORef ApplContext) ![RSExpr]
            | RApplForm !RSExpr ![RSExpr]
            | REmptyList

data KLNumber = KI !Integer
              | KD !Double
                deriving (Data, Show, Typeable)

instance Eq KLNumber where
    (KI n1) == (KI n2) = n1 == n2
    (KI n1) == (KD n2) = realToFrac n1 == n2
    (KD n1) == (KI n2) = n1 == realToFrac n2
    (KD n1) == (KD n2) = n1 == n2

instance Ord KLNumber where
    compare (KI n1) (KI n2) = compare n1 n2
    compare (KI n1) (KD n2) = compare (realToFrac n1) n2
    compare (KD n1) (KI n2) = compare n1 (realToFrac n2)
    compare (KD n1) (KD n2) = compare n1 n2

instance Num KLNumber where
    (KI n1) + (KI n2) = KI $ n1 + n2
    (KD n1) + (KD n2) = KD $ n1 + n2
    (KD n1) + (KI n2) = KD $ n1 + realToFrac n2
    (KI n1) + (KD n2) = KD $ realToFrac n1 + n2

    (KI n1) * (KI n2) = KI $ n1 * n2
    (KD n1) * (KD n2) = KD $ n1 * n2
    (KD n1) * (KI n2) = KD $ n1 * realToFrac n2
    (KI n1) * (KD n2) = KD $ realToFrac n1 * n2

    (KI n1) - (KI n2) = KI $ n1 - n2
    (KD n1) - (KD n2) = KD $ n1 - n2
    (KD n1) - (KI n2) = KD $ n1 - realToFrac n2
    (KI n1) - (KD n2) = KD $ realToFrac n1 - n2

    abs (KI n) = KI $ abs n
    abs (KD n) = KD $ abs n

    signum (KI n) = KI $ signum n
    signum (KD n) = KD $ signum n

    fromInteger = KI

instance Fractional KLNumber where
    (KI n1) / (KI n2) = KD $ realToFrac n1 / realToFrac n2
    (KD n1) / (KD n2) = KD $ n1 / n2
    (KD n1) / (KI n2) = KD $ n1 / realToFrac n2
    (KI n1) / (KD n2) = KD $ realToFrac n1 / n2

    fromRational r = KD $ fromRational r    
                                   
data Atom = UnboundSym !Symbol
          | B !Bool
          | N !KLNumber
          | Str !T.Text
            deriving (Data, Eq, Show, Typeable)
 
data TopLevel = Defun !Symbol !ParamList !SExpr
              | SE !SExpr

data KLValue = Atom !Atom
             | Cons !KLValue !KLValue
             | Excep !ErrorMsg
             | ApplC !ApplContext
             | InStream !Handle
             | List ![KLValue]
             | OutStream !Handle
             | Vec {-# UNPACK #-} !(Vector KLValue)
             deriving Show

data ApplContext = Func Function
                 | PL (KLContext Env IO KLValue)
                 | Malformed ErrorMsg

instance Show ApplContext where
    show _ = "<function>"

data Function = Context (KLValue -> KLContext Env IO KLValue)
              | ExceptionHandler Function
              | PartialApp (KLValue -> Function)

data Env = Env {  symbolTable :: Map Symbol KLValue
                , functionTable :: Map Symbol (IORef ApplContext) }

newtype KLCont s m a = KLCont {
      runKLCont :: ContT KLValue (KLContext s m) a
    } deriving (Functor, Monad, MonadState s, MonadIO, MonadCont)

instance (Functor m, Monad m) => Applicative (KLCont s m) where
    pure  = return
    (<*>) = ap

liftKLC :: (Monad m) => KLContext s m a -> KLCont s m a
liftKLC m = KLCont (ContT (m >>=))

newtype KLContext s m a = KLContext {
      runKLContext :: StateT s m a
  } deriving (Functor, Monad, MonadState s, MonadIO, MonadTrans, MonadFix)

instance (Functor m, Monad m) => Applicative (KLContext s m) where
    pure  = return
    (<*>) = ap

evalKLC :: Monad m => KLContext s m a -> s -> m a
evalKLC (KLContext st) = evalStateT st

runKLC :: Monad m => KLCont s m KLValue -> KLContext s m KLValue
runKLC m = runContT (runKLCont m) return
