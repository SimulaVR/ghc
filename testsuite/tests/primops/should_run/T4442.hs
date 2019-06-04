{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
module Main where

#include "MachDeps.h"

import GHC.Ptr(Ptr(..), nullPtr, plusPtr, minusPtr)
import GHC.Stable(
  StablePtr(..), castStablePtrToPtr, castPtrToStablePtr, newStablePtr)
import GHC.Exts
import Data.Char(ord)
import GHC.Int
import GHC.Word

assertEqual :: (Show a, Eq a) => String -> a -> a -> IO ()
assertEqual msg a b
  | a /= b = putStrLn (msg ++ " " ++ show a ++ " /= " ++ show b)
  | otherwise = return ()

readBytes :: MutableByteArray# s -> State# s -> Int# -> (# State# s, [Word8] #)
readBytes marr s0 len = go s0 len []
 where
  go s 0# bs = (# s, bs #)
  go s i  bs = case readWord8Array# marr (i -# 1#) s of
    (# s', b #) -> go s' (i -# 1#) (W8# b : bs)

indexBytes :: ByteArray# -> Int# -> [Word8]
indexBytes arr len  =
  [W8# (indexWord8Array# arr i) | I# i <- [0..I# len - 1]]

fillByteArray :: MutableByteArray# s -> Int# -> Word8 -> State# s -> State# s
fillByteArray arr len (W8# a) = go len
 where
  go 0# s = s
  go i s = go (i -# 1#) (writeWord8Array# arr (i -# 1#) a s)

test :: (Eq a, Show a)
  => String
  -> (ByteArray# -> Int# -> a)
  -> (MutableByteArray# RealWorld -> Int# -> State# RealWorld
      -> (# State# RealWorld, a #))
  -> (MutableByteArray# RealWorld -> Int# -> a -> State# RealWorld
      -> State# RealWorld)
  -> a
  -> [Word8]
  -> Int
  -> IO ()
test name index read write val valBytes len = do
  putStrLn name
  mapM_ testAtOffset [0..16]
 where
  arrLen :: Int#
  arrLen = 24#

  fillerByte :: Word8
  fillerByte = 0x34

  expectedArrayBytes :: Int -> [Word8]
  expectedArrayBytes offset =
       replicate offset fillerByte
    ++ valBytes
    ++ replicate (fromIntegral $ I# arrLen - len - offset) fillerByte

  testAtOffset :: Int -> IO ()
  testAtOffset offset@(I# offset#) = runRW# (\s0 -> let
    (# s1, marr #) = newByteArray# arrLen s0
    s2 = fillByteArray marr arrLen fillerByte s1
    s3 = write marr offset# val s2
    (# s4, actual0 #) = read marr offset# s3
    (# s5, actualBytes0 #) = readBytes marr s4 arrLen
    (# _, arr #) = unsafeFreezeByteArray# marr s5
    actual1 = index arr offset#
    actualBytes1 = indexBytes arr arrLen
   in do
       assertEqual "actual val 0" actual0 val
       assertEqual "actual val 1" actual1 val
       assertEqual "actualBytes0 indexed" actualBytes0 (expectedArrayBytes offset)
       assertEqual "actualButes1 indexed" actualBytes1 (expectedArrayBytes offset)
   )

intToBytes :: Word -> Int -> [Word8]
intToBytes (W# val0) (I# len0) = let
    result = go val0 len0
    go v 0# = []
    go v len =
      W8# (wordToWord8# v) : go (v `uncheckedShiftRL#` 8#) (len -# 1#)
  in
#if defined(WORDS_BIGENDIAN)
    reverse result
#else
    result
#endif

testIntArray :: (Eq a, Show a, Integral a, Num a)
  => String
  -> (ByteArray# -> Int# -> a)
  -> (MutableByteArray# RealWorld -> Int# -> State# RealWorld
      -> (# State# RealWorld, a #))
  -> (MutableByteArray# RealWorld -> Int# -> a -> State# RealWorld
      -> State# RealWorld)
  -> a
  -> Int
  -> IO ()
testIntArray name0 index read write val0 len = do
  doOne (name0 ++ " positive") val0
  doOne (name0 ++ " negative") (negate val0)
 where
  doOne name val = test name index read write
    val (intToBytes (fromIntegral val) len) len

testInt64Array ::
     String
  -> (ByteArray# -> Int# -> Int64#)
  -> (MutableByteArray# RealWorld -> Int# -> State# RealWorld
        -> (# State# RealWorld, Int64# #))
  -> (MutableByteArray# RealWorld -> Int# -> Int64# -> State# RealWorld
        -> State# RealWorld)
  -> Int64
  -> Int
  -> IO ()
testInt64Array name0 index read write val0 len = do
  doOne (name0 ++ " positive") val0
  doOne (name0 ++ " negative") (negate val0)
 where
  doOne :: String -> Int64 -> IO ()
  doOne name val = test
    name
    (\arr i -> I64# (index arr i))
    (\arr i s -> case read arr i s of (# s', a #) -> (# s', I64# a #))
    (\arr i (I64# a) s -> write arr i a s)
    val
    (intToBytes (fromIntegral val) len)
    len

testWordArray :: (Eq a, Show a, Integral a)
  => String
  -> (ByteArray# -> Int# -> a)
  -> (MutableByteArray# RealWorld -> Int# -> State# RealWorld
        -> (# State# RealWorld, a #))
  -> (MutableByteArray# RealWorld -> Int# -> a -> State# RealWorld
        -> State# RealWorld)
  -> a
  -> Int
  -> IO ()
testWordArray name index read write val len =
  test name index read write
    val (intToBytes (fromIntegral val) len) len

testWord64Array ::
     String
  -> (ByteArray# -> Int# -> Word64#)
  -> (MutableByteArray# RealWorld -> Int# -> State# RealWorld
        -> (# State# RealWorld, Word64# #))
  -> (MutableByteArray# RealWorld -> Int# -> Word64# -> State# RealWorld
        -> State# RealWorld)
  -> Word64
  -> Int
  -> IO ()
testWord64Array name index read write val len = test
  name
  (\arr i -> W64# (index arr i))
  (\arr i s -> case read arr i s of (# s', a #) -> (# s', W64# a #))
  (\arr i (W64# a) s -> write arr i a s)
  val
  (intToBytes (fromIntegral val) len)
  len

wordSizeInBytes :: Int
wordSizeInBytes = WORD_SIZE_IN_BITS `div` 8

int :: Int
int
  | WORD_SIZE_IN_BITS == 32 = 12345678
  | otherwise = 1234567890123

word :: Word
word = fromIntegral int

float :: Float
float = 123.456789

-- Test pattern generated by this python code:
-- >>> import struct
-- >>> import binascii
-- >>> binascii.hexlify(struct.pack('>f', 123.456789))
floatBytes :: Word
floatBytes = 0x42f6e9e0

double :: Double
double = 123.45678901234

-- Test pattern generated by this python code:
-- >>> import struct
-- >>> import binascii
-- >>> binascii.hexlify(struct.pack('>d', 123.45678901234))
doubleBytes :: Word
doubleBytes = 0x405edd3c07fb4b09

main :: IO ()
main = do
  testIntArray "Int8#"
    (\arr i -> I8# (indexInt8Array# arr i))
    (\arr i s -> case readInt8Array# arr i s of (# s', a #) -> (# s', I8# a #))
    (\arr i (I8# a) s -> writeInt8Array# arr i a s)
    123 1
  testIntArray "Int16#"
    (\arr i -> I16# (indexWord8ArrayAsInt16# arr i))
    (\arr i s -> case readWord8ArrayAsInt16# arr i s of (# s', a #) -> (# s', I16# a #))
    (\arr i (I16# a) s -> writeWord8ArrayAsInt16# arr i a s)
    12345 2
  testIntArray "Int32#"
    (\arr i -> I32# (indexWord8ArrayAsInt32# arr i))
    (\arr i s -> case readWord8ArrayAsInt32# arr i s of (# s', a #) -> (# s', I32# a #))
    (\arr i (I32# a) s -> writeWord8ArrayAsInt32# arr i a s)
    12345678 4
  testInt64Array "Int64#"
    (\arr i -> I64# (indexWord8ArrayAsInt64# arr i))
    (\arr i s -> case readWord8ArrayAsInt64# arr i s of (# s', a #) -> (# s', I64# a #))
    (\arr i (I64# a) s -> writeWord8ArrayAsInt64# arr i a s)
    1234567890123 8
  testIntArray "Int#"
    (\arr i -> I# (indexWord8ArrayAsInt# arr i))
    (\arr i s -> case readWord8ArrayAsInt# arr i s of (# s', a #) -> (# s', I# a #))
    (\arr i (I# a) s -> writeWord8ArrayAsInt# arr i a s)
    int wordSizeInBytes

  testWordArray "Word8#"
    (\arr i -> W8# (indexWord8Array# arr i))
    (\arr i s -> case readWord8Array# arr i s of (# s', a #) -> (# s', W8# a #))
    (\arr i (W8# a) s -> writeWord8Array# arr i a s)
    123 1
  testWordArray "Word16#"
    (\arr i -> W16# (indexWord8ArrayAsWord16# arr i))
    (\arr i s -> case readWord8ArrayAsWord16# arr i s of (# s', a #) -> (# s', W16# a #))
    (\arr i (W16# a) s -> writeWord8ArrayAsWord16# arr i a s)
    12345 2
  testWordArray "Word32#"
    (\arr i -> W32# (indexWord8ArrayAsWord32# arr i))
    (\arr i s -> case readWord8ArrayAsWord32# arr i s of (# s', a #) -> (# s', W32# a #))
    (\arr i (W32# a) s -> writeWord8ArrayAsWord32# arr i a s)
    12345678 4
  testWord64Array "Word64#"
    (\arr i -> W64# (indexWord8ArrayAsWord64# arr i))
    (\arr i s -> case readWord8ArrayAsWord64# arr i s of (# s', a #) -> (# s', W64# a #))
    (\arr i (W64# a) s -> writeWord8ArrayAsWord64# arr i a s)
    1234567890123 8
  testWordArray "Word#"
    (\arr i -> W# (indexWord8ArrayAsWord# arr i))
    (\arr i s -> case readWord8ArrayAsWord# arr i s of (# s', a #) -> (# s', W# a #))
    (\arr i (W# a) s -> writeWord8ArrayAsWord# arr i a s)
    word wordSizeInBytes

  test
    "Char#"
    (\arr i -> C# (indexWord8ArrayAsChar# arr i))
    (\arr i s ->
        case readWord8ArrayAsChar# arr i s of (# s', a #) -> (# s', C# a #))
    (\arr i (C# a) s -> writeWord8ArrayAsChar# arr i a s)
    'z'
    [fromIntegral $ ord 'z']
    1
  test
    "WideChar#"
    (\arr i -> C# (indexWord8ArrayAsWideChar# arr i))
    (\arr i s ->
        case readWord8ArrayAsWideChar# arr i s of (# s', a #) -> (# s', C# a #))
    (\arr i (C# a) s -> writeWord8ArrayAsWideChar# arr i a s)
    '𠜎'  -- See http://www.i18nguy.com/unicode/supplementary-test.html
    (intToBytes (fromIntegral $ ord '𠜎') 4)
    4
  test
    "Addr#"
    (\arr i -> Ptr (indexWord8ArrayAsAddr# arr i))
    (\arr i s ->
        case readWord8ArrayAsAddr# arr i s of (# s', a #) -> (# s', Ptr a #))
    (\arr i (Ptr a) s -> writeWord8ArrayAsAddr# arr i a s)
    (nullPtr `plusPtr` int)
    (intToBytes word wordSizeInBytes)
    wordSizeInBytes

  stablePtr <- newStablePtr ()
  test
    "StablePtr#"
    (\arr i ->
        castStablePtrToPtr (StablePtr (indexWord8ArrayAsStablePtr# arr i)))
    (\arr i s -> case readWord8ArrayAsStablePtr# arr i s of
                   (# s', a #) -> (# s', castStablePtrToPtr (StablePtr a) #))
    (\arr i p s -> case castPtrToStablePtr p of
                     (StablePtr a) -> writeWord8ArrayAsStablePtr# arr i a s)
    (castStablePtrToPtr stablePtr)
    (intToBytes (fromIntegral $ castStablePtrToPtr stablePtr `minusPtr` nullPtr)
                wordSizeInBytes)
    wordSizeInBytes

  test
    "Float#"
    (\arr i -> F# (indexWord8ArrayAsFloat# arr i))
    (\arr i s ->
        case readWord8ArrayAsFloat# arr i s of (# s', a #) -> (# s', F# a #))
    (\arr i (F# a) s -> writeWord8ArrayAsFloat# arr i a s)
    float
    (intToBytes floatBytes 4)
    4
  test
    "Double#"
    (\arr i -> D# (indexWord8ArrayAsDouble# arr i))
    (\arr i s ->
        case readWord8ArrayAsDouble# arr i s of (# s', a #) -> (# s', D# a #))
    (\arr i (D# a) s -> writeWord8ArrayAsDouble# arr i a s)
    double
    (intToBytes doubleBytes 8)
    8
