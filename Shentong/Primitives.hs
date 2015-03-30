{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Shentong.Primitives where

import Control.Applicative
import Control.Exception
import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.Trans
import qualified Data.ByteString.Lazy as BL
import Data.Char hiding (isSymbol)
import Data.List
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Time.Clock.POSIX
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import System.CPUTime
import System.IO
import Shentong.Types
import Shentong.Utils

{-
intern: maps a string containing a symbol to a symbol
intern : string --> symbol
-}
intern :: KLValue -> KLContext s KLValue
intern = internFn
    where internFn (Atom (Str s)) = return (Atom (UnboundSym s))
          internFn _ = throwError "intern: requires a string argument."

{-
pos: given a natural number 0...n and a string S returns the nth unit string in S
pos : string --> number --> string
-}
pos :: KLValue -> KLValue -> KLContext s KLValue
pos = posFn
    where posFn (Atom (Str s)) (Atom (N (KI n))) = st s (fromIntegral n)
          posFn _ _ = throwError "pos s n: s must be a string, n an integer"
          st s n
            | 0 <= n && n < T.length s =
              return $ Atom . Str . T.singleton $ T.index s n
            | otherwise =
                throwError $ "pos s n: must have n < length s, n: " 
                <> (T.pack (show n)) <> ", s: " <> s

{-
tlstr: returns all but the first unit string of a string
tlstr : string --> string
-}
tlstr :: KLValue -> KLContext s KLValue 
tlstr = tlstrFn
    where tlstrFn (Atom (Str s)) = return (Atom . Str $ T.tail s)
          tlstrFn _ = throwError "tlstr: first parameter must be a string."

{-
cn:concatenate two strings
cn : string --> string --> string
-}
cn :: KLValue -> KLValue -> KLContext s KLValue
cn = cnFn
    where cnFn (Atom (Str s1)) (Atom (Str s2)) = return (Atom . Str $ s1 <> s2)
          cnFn v1 v2 = throwError "cn: both parameters must be a string."

{-
str: maps any atom to a string
str : Atom --> string
-}
str :: KLValue -> KLContext s KLValue
str = strFn
    where strFn s@(Atom (Str _)) = return s
          strFn (Atom (UnboundSym s)) = return (Atom (Str s))
          strFn (Atom (B b)) = return (Atom (Str bs))
              where bs | b         = "true"
                       | otherwise = "false"
          strFn (Atom (N n)) = return (Atom (Str s))
              where s = case n of
                      KI i -> T.pack $ show i
                      KD d -> T.pack $ show d
          strFn (ApplC (Func name _)) = return (Atom (Str name))
          strFn (ApplC (PL name _)) = return (Atom (Str name))
          strFn v = throwError "str : first parameter must be an atom."

{-
string?: test for strings
string? : Lit --> boolean
-}
stringP :: KLValue -> KLContext s KLValue
stringP = stringPFn
    where stringPFn (Atom (Str _)) = return (Atom (B True))
          stringPFn _ = return (Atom (B False))

{-
n->string: maps a code point in decimal to the corresponding unit string
n->string : number --> string
-}
nToString :: KLValue -> KLContext s KLValue
nToString = nToStringFn
    where nToStringFn (Atom (N (KI (fromIntegral -> n))))
            | 0 <= n && n <= 127 = return (Atom (Str . T.singleton $ chr n))
            | otherwise = throwError "n->string: needs an ASCII code point"
          nToStringFn _ = throwError "n->string: needs an ASCII code point"

{-
string->n: maps a unit string to the corresponding decimal
string->n : string --> number
-}
stringToN :: KLValue -> KLContext s KLValue
stringToN = stringToNFn
    where stringToNFn (Atom (Str str)) =
            return (Atom (N (KI . toInteger $ ord (T.head str))))
          stringToNFn v = throwError "string->n: first parameter must be an ASCII code point."
                          
{-
set: assigns a value to a symbol	
-}
klSet :: KLValue -> KLValue -> KLContext Env KLValue
klSet = setFn
  where setFn (Atom (UnboundSym sym)) klv = do
          insertSymbol sym klv
          return klv
        setFn _ _ = throwError "set: first parameter must be a symbol"

{-
value: retrieves the value of a symbol
-}
value :: KLValue -> KLContext Env KLValue
value = valueFn
  where valueFn (Atom (UnboundSym sym)) = symbolRef sym
        valueFn _ = throwError "value: first parameter must be a symbol."

{-
simple-error: calls an throwError
simple-error : string --> throwError
-}
simpleError :: KLValue -> KLContext s KLValue
simpleError = simpleErrorFn
  where simpleErrorFn (Atom (Str str)) =
          throwError str
        simpleErrorFn v1 =
          throwError "simple-error: first parameter must be a string."

{-
error-to-string: maps an throwError to a string
error-to-string : throwError --> string
-}
errorToString :: KLValue -> KLContext s KLValue
errorToString = errorToStringFn
  where errorToStringFn (Excep e) = return (Atom (Str e))
        errorToStringFn _ =
            throwError "error-to-string: first parameter must be an throwError."

{-
cons: add an element to the front of a list
cons : A --> (list A) --> (list A)
-}
klCons :: KLValue -> KLValue -> KLContext s KLValue
klCons = consFn
  where consFn klv (List klvs) = return (List (klv:klvs))
        consFn v1 v2 = return (Cons v1 v2)
          
{-
hd: take the head of a list
hd : (list A) --> A
-}        
hd :: KLValue -> KLContext s KLValue
hd = hdFn
  where hdFn (List (v:_)) = return v
        hdFn (List []) = return (List [])
        hdFn (Cons v _) = return v
        hdFn v = throwError "hd: first parameter must be a list."

{-
tl: return the tail of a list
tl : (list A) --> (list A)
-}
tl :: KLValue -> KLContext s KLValue
tl = tlFn
  where tlFn (List []) = return (List [])
        tlFn (List (_:vs)) = return (List vs)
        tlFn (Cons _ v) = return v
        tlFn v = throwError "tl: first parameter must be a list."

{-
cons?: test for non-empty list
cons? : A --> boolean
-}
consP :: KLValue -> KLContext s KLValue
consP = consPFn
  where consPFn (List []) = return (Atom (B False))
        consPFn (List _) = return (Atom (B True))
        consPFn (Cons _ _) = return (Atom (B True))
        consPFn _ = return (Atom (B False))

{-
=: equality
A --> A --> boolean
-}
eq :: KLValue -> KLValue -> KLContext s KLValue
eq v1 v2 = return $ Atom (B (eqFn v1 v2))
  where
    eqFn (ApplC (Func n _)) (Atom (UnboundSym n')) = n == n'
    eqFn (ApplC (Func n _)) (ApplC (Func n' _)) = n == n'
    eqFn (ApplC (PL n _)) (ApplC (PL n' _)) = n == n'
    eqFn (ApplC (PL n _)) (Atom (UnboundSym n'))   = n == n'
    eqFn (Atom (UnboundSym n')) (ApplC (Func n _)) = n == n'
    eqFn (Atom (UnboundSym n')) (ApplC (PL n _))   = n == n'
    eqFn (Atom (UnboundSym "true")) (Atom (B True)) = True
    eqFn (Atom (UnboundSym "false")) (Atom (B False)) = True
    eqFn (Atom (B True)) (Atom (UnboundSym "true")) = True
    eqFn (Atom (B False)) (Atom (UnboundSym "false")) = True
    eqFn (Atom a1) (Atom a2) = a1 == a2
    eqFn (List l1) (List l2) = length l1 == length l2 &&
      foldl' (\acc (x,y) -> acc && eqFn x y) True (zip l1 l2)
    eqFn (Cons v1 v2) (Cons v3 v4) = eqFn v1 v3 && eqFn v2 v4
    eqFn (Vec v1) (Vec v2) = V.length v1 == V.length v2 && 
      V.foldl' (\acc (x,y) -> acc && eqFn x y) True (V.zip v1 v2)
    eqFn _ _ = False

{-
type: labels the type of an expression
(type X A) : A
-}
typeA :: KLValue -> KLValue -> KLContext s KLValue
typeA v _ = return v

{-
absvector: a vector in the native platform, indexed from 0 to n inclusive
absvector : integer --> vector
-}
absvector :: KLValue -> KLContext s KLValue
absvector = absvectorFn
  where absvectorFn (Atom (N (KI (fromIntegral -> n))))
          | n >= 0 = return (Vec $ V.replicate n (List []))
          | otherwise = throwError "absvector n: must have n >= 0."
        absvectorFn _ =
          throwError "absvector: first parameter must be a positive integer."

{-
address->: destructively assign a value to a vector address
address-> : E -> integer -> vector -> vector
-}
addressTo :: KLValue -> KLValue -> KLValue -> KLContext s KLValue
addressTo = addressToFn
  where addressToFn (Vec vec) (Atom (N (KI (fromIntegral -> n)))) val
          | n >= 0 && n < V.length vec = return (Vec v')
          | otherwise =
              throwError "address-> n e v : n must be within range of v."
          where v' = runST $ do
                  mv <- V.unsafeThaw vec
                  MV.unsafeWrite mv n val
                  V.unsafeFreeze mv
        addressToFn _ _ _ =
          throwError "address->: requires a vector, positive integer, and element"
        {-# INLINE addressToFn #-}
{-# INLINE addressTo #-}

{-
<-address: retrieve a value from a vector address
<-address: integer -> vector -> value
-}
addressFrom :: KLValue -> KLValue -> KLContext s KLValue
addressFrom = addressFromFn
  where addressFromFn (Vec v) (Atom (N (KI (fromIntegral -> n))))
          | n >= 0 && n < V.length v = return ((V.!) v n)
          | otherwise = throwError "address<- n v: n must be within range of v."
        addressFromFn _ _ =
            throwError "<-address: requires a positive integer and vector"
            
{-
absvector? : Atom --> boolean
-}
absvectorP :: KLValue -> KLContext s KLValue
absvectorP = absvectorPFn
  where absvectorPFn (Vec v) = return (Atom (B True))
        absvectorPFn _ = return (Atom (B False))


{-
write-byte: write an unsigned 8 bit byte to a stream
write-byte : number --> (stream out) --> number
-}
writeByte :: KLValue -> KLValue -> KLContext s KLValue
writeByte = writeByteFn
  where writeByteFn num@(Atom (N (KI n))) (OutStream h) 
          | 0 <= n && n <= 255 = liftIO $ do
            BL.hPut h (BL.singleton (fromInteger n))
            return num
          | otherwise = throwError "write-byte n: must have 0 <= n <= 255."
        writeByteFn v1 v2 =
          throwError "write-byte: takes an integer and a (stream out)."

{-
read-byte: read an unsigned 8 bit byte from a stream
read-byte : (stream in) --> number
-}
readByte :: KLValue -> KLContext s KLValue
readByte = readByteFn
  where readByteFn (InStream stream) = do
          byte <- liftIO $ BL.hGet stream 1
          if BL.null byte then
              return (Atom (N (KI (-1))))
          else
              return (Atom (N (KI (toInteger (BL.head byte)))))
        readByteFn _ = throwError "read-byte: takes a (stream in)."
           
{-
open: open a stream
open : path --> direction (D) --> stream D
-}
openStream :: KLValue -> KLValue -> KLContext Env KLValue
openStream = openStreamFn
  where openStreamFn (Atom (Str path)) (Atom (UnboundSym "in")) =
            symbolRef "*home-directory*" >>= dir path ReadMode . getPath
        openStreamFn (Atom (Str path)) (Atom (UnboundSym "out")) =
            symbolRef "*home-directory*" >>= dir path WriteMode . getPath
        openStreamFn _ _ = throwError "open: requires filepath, in/out"                           
                           
        getPath (Atom (Str p)) = p
        getPath _ = "."

        toggleMode ReadMode = InStream
        toggleMode WriteMode = OutStream

        tryToOpenFile path mode = try $ openBinaryFile (T.unpack path) mode

        dir path mode homeDir = do         
          h <- liftIO $ tryToOpenFile (homeDir <> path) mode
          case h of
            Left (err :: IOException) -> throwError (T.pack $ show err)
            Right h  -> return (toggleMode mode h)

{-
close: close a stream
close : (stream D) --> (list B)
-}
closeStream :: KLValue -> KLContext s KLValue
closeStream = closeStreamFn
  where closeStreamFn (OutStream h) = do
          liftIO $ hClose h
          return (List [])
        closeStreamFn (InStream h) = do
          liftIO $ hClose h
          return (List [])
        closeStreamFn _ = throwError "close: takes a (stream D) as input."

{-
get-time: get the run/real time
get-time : symbol --> number
-}
getTime :: KLValue -> KLContext s KLValue
getTime = getTimeFn
  where seconds t = fromInteger (round t)
        picoseconds t = fromInteger t * 1e-12

        getTimeFn (Atom (UnboundSym "unix")) = do
          t <- liftIO getPOSIXTime
          return (Atom (N (KI (seconds t))))
        getTimeFn (Atom (UnboundSym "run")) = do
          t <- liftIO getCPUTime
          return (Atom (N (KD (picoseconds t))))
        getTimeFn _ =
          throwError "get-time: expects symbol 'real' or 'unix' as input."

binopTemplate :: ErrorMsg -> (forall a. (Num a, Fractional a) => a -> a -> a) ->
                 KLValue -> KLValue -> KLContext s KLValue
binopTemplate _ fn (Atom (N n1)) (Atom (N n2)) = return $ Atom (N (n1 `fn` n2))
binopTemplate e _ _ _ = throwError e

{-
+: addition
+ : number --> number --> number
-}
add :: KLValue -> KLValue -> KLContext s KLValue
add = addFn
  where addFn = binopTemplate "+: expects two numbers as input" (+)
            
{-
-: subtraction
- : number --> number --> number
-}
subtract :: KLValue -> KLValue -> KLContext s KLValue
subtract = subtractFn
  where subtractFn = binopTemplate "-: expects two numbers as input" (-)

{-
*: subtraction
* : number --> number --> number
-}
multiply :: KLValue -> KLValue -> KLContext s KLValue
multiply = multiplyFn
  where multiplyFn = binopTemplate "*: expects two numbers as input" (*)

{-
/: division
/ : number --> number --> number
-}
divide :: KLValue -> KLValue -> KLContext s KLValue
divide = divideFn
  where divideFn = binopTemplate "/: expects two numbers as input" (/)

compareTemplate :: ErrorMsg -> (forall a. (Ord a) => a -> a -> Bool) ->
                   KLValue -> KLValue -> KLContext s KLValue
compareTemplate _ fn (Atom (N n1)) (Atom (N n2)) = return (Atom (B (n1 `fn` n2)))
compareTemplate errorMsg _ v1 v2 = throwError errorMsg

{-
>: greater than
> : number --> number --> boolean
-}
greaterThan :: KLValue -> KLValue -> KLContext s KLValue
greaterThan = greaterThanFn
  where greaterThanFn = compareTemplate ">: expects two numbers." (>)

{-
<: less than
< : number --> number --> boolean
-}
lessThan :: KLValue -> KLValue -> KLContext s KLValue
lessThan = lessThanFn
  where lessThanFn = compareTemplate "<: expects two numbers" (<)
        
{-
>=: greater than or equal to
>= : number --> number --> boolean
-}
greaterThanOrEqualTo :: KLValue -> KLValue -> KLContext s KLValue
greaterThanOrEqualTo = greaterThanOrEqualToFn
  where greaterThanOrEqualToFn = compareTemplate ">=: expects two numbers" (>=)

{-        
<=: less than or equal to
<= : number --> number --> boolean
-}
lessThanOrEqualTo :: KLValue -> KLValue -> KLContext s KLValue
lessThanOrEqualTo = lessThanOrEqualToFn
  where lessThanOrEqualToFn = compareTemplate "<=: expects two numbers" (<=)
        
{-
number?	number test
A --> boolean
-}
numberP :: KLValue -> KLContext s KLValue
numberP = numberPFn
  where numberPFn (Atom (N _)) = return (Atom (B True))
        numberPFn _ = return (Atom (B False))
