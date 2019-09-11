{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnboxedTuples #-}

import Control.Exception (assert, bracket)
import Control.Monad (when)
import Control.Monad.Extra (maybeM, ifM)
import Data.ByteString (length, append, hPut, hGetContents)
import Data.ByteString.Builder (toLazyByteString, intDec)
import Data.ByteString.Char8 (pack, unlines, putStrLn)
import Data.ByteString.Internal (ByteString(..), mallocByteString,
  accursedUnutterablePerformIO)
import qualified Data.ByteString.Lazy as BL (toStrict)
import Data.Foldable (fold)
import Data.Maybe (listToMaybe)
import Data.Word (Word8)
import Foreign (Ptr, peekByteOff, plusPtr, pokeByteOff)
import Foreign.ForeignPtr (withForeignPtr)
import Prelude hiding (unlines, FilePath, readFile, length, putStrLn, writeFile)
import System.IO (IOMode(..), Handle, hClose)
import System.Posix.ByteString (stdFileMode, openFd, createFile,
  OpenFileFlags(OpenFileFlags), OpenMode(..), fdToHandle)
import qualified System.Posix.ByteString as Posix (append)
import System.Posix.FilePath (splitFileName)
import System.Posix.Files.ByteString (fileExist)
import System.Posix.Env.ByteString (getArgs)

type FilePath = ByteString

-- | @S@ a state token used for `removeComments`
data S = MaybeComment          -- encountered a '/' in normal text
       | SingleLineComment     -- in single line comment
       | BlockCommentWithNL    -- in block comment without newline char yet
       | BlockCommentWithoutNL -- in block comment with newline char
       | MaybeEndWithoutNL     -- enocountered a '*' in a block comment
       | MaybeEndWithNL        -- enocountered a '*' in a block comment
       | QuoteBlock            -- in a quote block
       | EscingQuoteBlock      -- escapping quote block
       | HangingQuoteBlock     -- hanging block quote --> issue!
       | NormalSrc             -- regular source
       deriving Eq

-- | @removedComments@ removes any C-style comments from a bytestring,
-- returning the final state for exception handling.
removeCComments :: ByteString -> (ByteString, S)
removeCComments (PS fp off len) =
  accursedUnutterablePerformIO $
    withForeignPtr fp $ \a -> do
      fp <- mallocByteString len
      (l, res) <- withForeignPtr fp $
                    atomic NormalSrc 0 0 (a `plusPtr` off)
      assert (l <= len) $! return (PS fp 0 l, res)
  where

    -- `atomic` roughly-traverses the bytestring using a
    -- state `S`, coupled with two offset counters to atomically
    -- modify the bytestring. The offets are labeled as follows:
    --    * `hare` offset corresponds to read-byte location
    --    * `tort` offset corresponds to write-byte location
    --
    -- `hare` gets incramented at the end of the loop block.
    --
    -- `tort` gets adjused exclusively through the update function.
    --
    -- So, when entering a loop the
    -- `tort` location is `empty` since writing is only done when it
    -- gets moved (an byte is writen in the previous spot)
    atomic :: S -> Int -> Int -> Ptr Word8 -> Ptr Word8 -> IO (Int, S)
    atomic !st !tort !hare !r !w
      | hare >= len = return (tort, st)
      | otherwise   = do
         b <- peekByteOff r hare
         let (# t, s #) = update tort b st
         when (st == MaybeComment && b /= 47 && b /= 42)
              (pokeByteOff w tort (47::Word8))
         when (s /= MaybeComment && t > tort) (pokeByteOff w tort b)
         if s == HangingQuoteBlock
           then return (hare, s)
           else atomic s t (hare+1) r w
    {-# INLINE atomic #-}

    -- `update` modifies state and tortise pointer based on
    -- current state and focused byte.
    update :: Int -> Word8 -> S -> (# Int, S #)
    update t b NormalSrc = case b of
      47 -> (# t  , MaybeComment #)
      34 -> (# t+1, QuoteBlock   #)
      _  -> (# t+1, NormalSrc    #)
    update t b MaybeComment = case b of
      42 -> (# t  , BlockCommentWithoutNL #)
      47 -> (# t  , SingleLineComment     #)
      34 -> (# t+1, QuoteBlock            #)
      _  -> (# t+1, NormalSrc             #)
    update t b QuoteBlock = case b of
      34 -> (# t+1, NormalSrc         #)
      92 -> (# t+1, EscingQuoteBlock  #)
      _  -> if isEndOfLine b
       then (# t  , HangingQuoteBlock #)
       else (# t+1, QuoteBlock        #)
    update t b BlockCommentWithNL = case b of
      42 -> (# t  , MaybeEndWithNL     #)
      _  -> (# t  , BlockCommentWithNL #)
    update t b MaybeEndWithNL = case b of
      47 -> (# t  , NormalSrc          #)
      _  -> (# t  , BlockCommentWithNL #)
    update t b BlockCommentWithoutNL = case b of
      42 -> (# t  , MaybeEndWithoutNL     #)
      _  -> if isEndOfLine b
       then (# t+1, BlockCommentWithNL    #)
       else (# t  , BlockCommentWithoutNL #)
    update t b MaybeEndWithoutNL = case b of
      47 -> (# t  , NormalSrc             #)
      _  -> (# t  , BlockCommentWithoutNL #)
    update t b SingleLineComment = if isEndOfLine b
       then (# t+1, NormalSrc         #)
       else (# t  , SingleLineComment #)
    update t b EscingQuoteBlock = if b == 32 || b == 9
       then (# t+1, EscingQuoteBlock #)
       else (# t+1, QuoteBlock       #)
    update t _ HangingQuoteBlock = (# t, HangingQuoteBlock #)
    {-# INLINABLE update #-}

    isEndOfLine :: Word8 -> Bool
    isEndOfLine b = b == 13 || b == 10
    {-# INLINE isEndOfLine #-}
{-# INLINABLE removeCComments #-}

withFile :: FilePath -> IOMode -> (Handle -> IO r) -> IO r
withFile p m = bracket (open >>= fdToHandle) hClose
  where
    defaultFlags = OpenFileFlags False False True False False
    appendFlags = defaultFlags { Posix.append = True }
    open = case m of
      ReadMode      -> openFd p ReadOnly Nothing defaultFlags
      WriteMode     -> createFile p stdFileMode
      AppendMode    -> openFd p WriteOnly (Just stdFileMode) appendFlags
      ReadWriteMode -> openFd p ReadWrite (Just stdFileMode) defaultFlags
{-# INLINEABLE withFile #-}

readFile :: FilePath -> IO ByteString
readFile p = withFile p ReadMode hGetContents
{-# INLINABLE readFile #-}

writeFile :: FilePath -> ByteString -> IO ()
writeFile p c = withFile p WriteMode (`hPut` c)
{-# INLINEABLE writeFile #-}

-- | @int2bs@ converts an int to a bytestring.
-- Uses the really SLOW 'toStrict'.
int2bs :: Int -> ByteString
int2bs =  BL.toStrict . toLazyByteString . intDec
{-# INLINE int2bs #-}

removeCCommentsFromFile :: ByteString -> IO ()
removeCCommentsFromFile src = removeCComments_ =<< readFile src
  where
    removeCComments_ b =
      let (s,f) = removeCComments b
          l = int2bs . length $ s
      in case f of
        BlockCommentWithoutNL  -> putStrLn $
          "Error, unterminated string literal @" `append` l
        BlockCommentWithNL     -> putStrLn $
          "Error, unterminated string literal @" `append` l
        HangingQuoteBlock      -> putStrLn $
          "Error, unterminated block comment @" `append` l
        _                      -> success 0 src s
    {-# INLINE removeCComments_ #-}

    success m src res =
      let (p,f) = splitFileName src
          path = fold [p, "stripped", int2bs m, "_", f]
      in ifM (fileExist path) (success (m+1) src res) (writeFile path res)
    {-# INLINABLE success #-}
{-# INLINABLE removeCCommentsFromFile #-}

printMsg :: IO ()
printMsg = putStrLn $ unlines
  [ "use: remove-comments FILEPATH [IGNORED]"
  , "descrption: remove-comments removes C-style comments from FILEPATH"
  ]
{-# INLINE printMsg #-}

handleArgs :: ByteString -> IO ()
handleArgs ""   = printMsg
handleArgs "-h" = printMsg
handleArgs bs   = removeCCommentsFromFile bs
{-# INLINE handleArgs #-}

main :: IO ()
main = maybeM printMsg handleArgs (listToMaybe <$> getArgs)
