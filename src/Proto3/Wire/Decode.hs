{-
  Copyright 2016 Awake Networks

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-}

-- | Low level functions for reading data in the protobufs wire format.
--
-- This module exports a function 'decodeWire' which parses data in the raw wire
-- format into an untyped 'Map' representation.
--
-- This module also provides 'Parser' types and functions for reading messages
-- from the untyped 'Map' representation obtained from 'decodeWire'.

{-# LANGUAGE ApplicativeDo              #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternGuards              #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE ViewPatterns            #-}

module Proto3.Wire.Decode
    ( -- * Untyped Representation
      ParsedField(..)
    , decodeWire
      -- * Parser Types
    , Parser(Parser, runParser)
    , RawPrimitive
    , RawField
    , RawMessage
    , ParseError(..)
    , foldFields
    , parse
    , fromEither
      -- * Primitives
    , bool
    , int32
    , int64
    , uint32
    , uint64
    , sint32
    , sint64
    , enum
    , byteString
    , lazyByteString
    , text
    , packedVarints
    , packedFixed32
    , packedFixed64
    , packedFloats
    , packedDoubles
    , fixed32
    , fixed64
    , sfixed32
    , sfixed64
    , float
    , double
      -- * Decoding Messages
    , at
    , oneof
    , one
    , repeated
    , embedded
    , embedded'
      -- * ZigZag codec
    , zigZagDecode
      -- * Exported For Doctest Only
    , toMap
    ) where

import           Control.Applicative
import           Control.Arrow (first)
import           Control.Exception       ( Exception )
import           Control.Monad           ( msum, foldM )
import           Data.Bits
import qualified Data.ByteString         as B
import qualified Data.ByteString.Lazy    as BL
import           Data.Either             ( either )
import           Data.Foldable           ( foldl' )
import qualified Data.IntMap.Strict      as M -- TODO intmap
import           Data.Maybe              ( fromMaybe )
import           Data.Serialize.Get      ( Get, getWord8, getInt32le
                                         , getInt64le, getWord32le, getWord64le
                                         , runGet )
import           Data.Serialize.IEEE754  ( getFloat32le, getFloat64le )
import           Data.Text.Lazy          ( Text, pack )
import           Data.Text.Lazy.Encoding ( decodeUtf8' )
import qualified Data.Traversable        as T
import           Data.Int                ( Int32, Int64 )
import           Data.Word               ( Word8, Word32, Word64 )
import           Proto3.Wire.Class
import           Proto3.Wire.Types

import           Control.Category
import           Prelude                 hiding (id, (.))

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :module Proto3.Wire.Decode Proto3.Wire.Types

-- | Decode a zigzag-encoded numeric type.
-- See: http://stackoverflow.com/questions/2210923/zig-zag-decoding
zigZagDecode :: (Num a, Bits a) => a -> a
zigZagDecode i = shiftR i 1 `xor` (-(i .&. 1))

-- | One field in a protobuf message.
--
-- We don't know what's inside some of these fields until we know what type
-- we're deserializing to, so we leave them as 'ByteString' until a later step
-- in the process.
data ParsedField = VarintField Word64
                 | Fixed32Field B.ByteString
                 | Fixed64Field B.ByteString
                 | LengthDelimitedField B.ByteString
    deriving (Show, Eq)

-- | Convert key-value pairs to a map of keys to a sequence of values with that
-- key, in their reverse occurrence order.
--
-- >>> toMap ([(FieldNumber 1, 3),(FieldNumber 2, 4),(FieldNumber 1, 6)] :: [(FieldNumber,Int)])
-- fromList [(1,[6,3]),(2,[4])]
--
toMap :: [(FieldNumber, v)] -> M.IntMap [v]
toMap kvs0 = makeMap . map (first (fromIntegral . getFieldNumber)) $ kvs0
  where
    makeMap :: [(Int, v)] -> M.IntMap [v]
    makeMap = close . foldl' combineSeen Nothing

    close Nothing = M.empty
    close (Just (m, k, v)) = M.insertWith (++) k v m

    -- If keys are in order, then we don't have to make any lookups,
    -- we just maintain the active element.
    -- Out of order keys will lookup in the map
    combineSeen :: Maybe (M.IntMap [v], Int, [v]) -> (Int, v) -> Maybe (M.IntMap [v], Int, [v])
    combineSeen Nothing (k1, a1) = Just (M.empty, k1, [a1])
    combineSeen (Just (m, k2, as)) (k1, a1) =
      if k1 == k2
        then Just (m, k1, a1 : as)
        -- It might seem that we want to use DList but we don't because:
        -- - alter has worse performance than insertWith, and there's no upsert
        -- - We're building up a list of elements in a recursive way
        --    that will be opaque to GHC
        -- - DList would add another dependency
        else let !m' = M.insertWith (++) k2 as m
             in Just (m', k1, [a1])

-- | Parses data in the raw wire format into an untyped 'Map' representation.
decodeWire :: B.ByteString -> Either String [(FieldNumber, ParsedField)]
decodeWire bstr = drloop bstr []
 where
   drloop !bs xs | B.null bs = Right $ reverse xs
   drloop !bs xs | otherwise = do
      (w, rest) <- takeVarInt bs
      wt <- gwireType $ fromIntegral (w .&. 7)
      let fn = w `shiftR` 3
      (res, rest2) <- takeWT wt rest
      drloop rest2 ((FieldNumber fn,res):xs)

decodeWireErr :: B.ByteString -> Either ParseError [(FieldNumber, ParsedField)]
decodeWireErr = either (Left . BinaryError . pack) Right . decodeWire


eitherUncons :: B.ByteString -> Either String (Word8, B.ByteString)
eitherUncons = maybe (Left "failed to parse varint128") Right . B.uncons


takeVarInt :: B.ByteString -> Either String (Word64, B.ByteString)
takeVarInt !bs =
  case B.uncons bs of
     Nothing -> Right (0, B.empty)
     Just (w1, r1) -> do
       if w1 < 128 then return (fromIntegral w1, r1) else do
        let val1 = fromIntegral (w1 - 0x80)

        (w2,r2) <- eitherUncons r1
        if w2 < 128 then return (val1 + (fromIntegral w2 `shiftL` 7), r2) else do
         let val2 = (val1 + (fromIntegral (w2 - 0x80) `shiftL` 7))

         (w3,r3) <- eitherUncons r2
         if w3 < 128 then return (val2 + (fromIntegral w3 `shiftL` 14), r3) else do
          let val3 = (val2 + (fromIntegral (w3 - 0x80) `shiftL` 14))

          (w4,r4) <- eitherUncons r3
          if w4 < 128 then return (val3 + (fromIntegral w4 `shiftL` 21), r4) else do
           let val4 = (val3 + (fromIntegral (w4 - 0x80) `shiftL` 21))

           (w5,r5) <- eitherUncons r4
           if w5 < 128 then return (val4 + (fromIntegral w5 `shiftL` 28), r5) else do
            let val5 = (val4 + (fromIntegral (w5 - 0x80) `shiftL` 28))

            (w6,r6) <- eitherUncons r5
            if w6 < 128 then return (val5 + (fromIntegral w6 `shiftL` 35), r6) else do
             let val6 = (val5 + (fromIntegral (w6 - 0x80) `shiftL` 35))

             (w7,r7) <- eitherUncons r6
             if w7 < 128 then return (val6 + (fromIntegral w7 `shiftL` 42), r7) else do
              let val7 = (val6 + (fromIntegral (w7 - 0x80) `shiftL` 42))

              (w8,r8) <- eitherUncons r7
              if w8 < 128 then return (val7 + (fromIntegral w8 `shiftL` 49), r8) else do
               let val8 = (val7 + (fromIntegral (w8 - 0x80) `shiftL` 49))

               (w9,r9) <- eitherUncons r8
               if w9 < 128 then return (val8 + (fromIntegral w9 `shiftL` 56), r9) else do
                let val9 = (val8 + (fromIntegral (w9 - 0x80) `shiftL` 56))

                (w10,r10) <- eitherUncons r9
                if w10 < 128 then return (val9 + (fromIntegral w10 `shiftL` 63), r10) else do

                 Left ("failed to parse varint128: too big; " ++ show val6)


gwireType :: Word8 -> Either String WireType
gwireType 0 = return Varint
gwireType 5 = return Fixed32
gwireType 1 = return Fixed64
gwireType 2 = return LengthDelimited
gwireType wt = Left $ "wireType got unknown wire type: " ++ show wt

safeSplit :: Int -> B.ByteString -> Either String (B.ByteString, B.ByteString)
safeSplit !i !b | B.length b < i = Left "failed to parse varint128: not enough bytes"
                | otherwise = Right $ B.splitAt i b

takeWT :: WireType -> B.ByteString -> Either String (ParsedField, B.ByteString)
takeWT Varint !b  = fmap (first VarintField) $ takeVarInt b
takeWT Fixed32 !b = fmap (first Fixed32Field) $ safeSplit 4 b
takeWT Fixed64 !b = fmap (first Fixed64Field) $ safeSplit 8 b
takeWT LengthDelimited b = do
   (!len, rest) <- takeVarInt b
   fmap (first LengthDelimitedField) $ safeSplit (fromIntegral len) rest


-- * Parser Interface

-- | Type describing possible errors that can be encountered while parsing.
data ParseError =
                -- | A 'WireTypeError' occurs when the type of the data in the protobuf
                -- binary format does not match the type encountered by the parser. This can
                -- indicate that the type of a field has changed or is incorrect.
                WireTypeError Text
                |
                -- | A 'BinaryError' occurs when we can't successfully parse the contents of
                -- the field.
                BinaryError Text
                |
                -- | An 'EmbeddedError' occurs when we encounter an error while parsing an
                -- embedded message.
                EmbeddedError Text
                              (Maybe ParseError)
    deriving (Show, Eq, Ord)

-- | This library does not use this instance, but it is provided for convenience,
-- so that 'ParseError' may be used with functions like `throwIO`
instance Exception ParseError


type Result input r a = (a -> input -> r) -> (ParseError -> input -> r) -> input -> r

-- | A parsing function type synonym, to tidy up type signatures.
--
-- This synonym is used in three ways:
--
-- * Applied to 'RawPrimitive', to parse primitive fields.
-- * Applied to 'RawField', to parse fields which correspond to a single 'FieldNumber'.
-- * Applied to 'RawMessage', to parse entire messages.
--
-- Many of the combinators in this module are used to combine and convert between
-- these three parser types.
--
-- 'Parser's can be combined using the 'Applicative', 'Monad' and 'Alternative'
-- instances.
newtype Parser input a = MkParser {
    -- Effectively, input -> Either ParseError a
    -- the extra input is used to ensure that closures over the input aren't required
    -- and work can be pre-computed
    unParser :: forall r. (ParseError -> r) ->
                           (a -> r) ->
                           (input -> r)
  }
    deriving Functor

pattern Parser :: (input -> Either ParseError a) -> Parser input a
pattern Parser{ runParser } <- (runParser' -> runParser) where
  Parser f = fromEither f


runParser' :: Parser i a -> i -> Either ParseError a
runParser' (MkParser p) = p Left Right
{-# INLINE runParser' #-}

{-

parseF :: Parser i (DataPoint f)
parseF = do
  x <- ..
  y <- ..
  DataPoint (...)


Global f
Local r

fallible :: (forall a. Fallible a -> Either ParseError (Maybe a))

(ParseError -> r) -> (a -> r) -> r -> r
~ Maybe


 embedded :: forall m. (a -> m b) -> m b -> Parser RawMessage a -> Parser RawField (m b)

-}

instance Applicative (Parser input) where
    pure x = MkParser $ \_ good _ -> good x
    MkParser p1 <*> MkParser p2 =
      MkParser $ \bad good i -> p1 bad (\f -> p2 bad (\a -> good (f a)) i) i
    liftA2 f (MkParser p1) (MkParser p2) =
        MkParser $ \bad good i -> p1 bad (\x -> p2 bad (\y -> good (f x y)) i) i


instance Monad (Parser input) where
    -- return = pure
    MkParser p >>= f = MkParser $ \bad good i -> p bad (\a -> unParser (f a) bad good i) i

{-
instance Alternative (Parser input) where
    empty = Parser $ \_ _ missing -> missing
    Parser p1 <|> Parser p2 = Parser $ \good bad missing ->
      p1 good bad (p2 good bad missing)

combine2 :: (Either ParseError a -> Either ParseError b -> c) -> Parser input a -> Parser input b -> Parser input c
combine2 f (Parser p1) (Parser p2) = Parser $ \bad good input ->
  p1 (\e1 -> p2 (\e2 _ -> f (Left e1) (Left e2)) (\x2 _ -> f Nothing (Just b)))
     (\x1 -> p2 (\e2 _ -> f (Just a) Nothing) (\x2 _ -> f (Just a) (Just b)))
      -}

-- | Raw data corresponding to a single encoded key/value pair.
type RawPrimitive = ParsedField

-- | Raw data corresponding to a single 'FieldNumber'.
type RawField = [RawPrimitive]

-- | Raw data corresponding to an entire message.
--
-- A 'Map' from 'FieldNumber's to the those values associated with
-- that 'FieldNumber'.
type RawMessage = M.IntMap RawField


catchParse :: Parser i a -> (ParseError -> Parser i a) -> Parser i a
catchParse (MkParser p) whenErr = MkParser $ \bad good i -> p (\err -> unParser (whenErr err) bad good i) good i
{-# INLINE catchParse #-}

instance Category Parser where
  id = MkParser $ \_ good i -> good i
  MkParser p1 . MkParser p2 = MkParser $ \bad good ->
    p2 bad (p1 bad good)


-- | Fold over a list of parsed fields accumulating a result
foldFields :: M.IntMap (Parser RawPrimitive a, a -> acc -> acc)
           -> acc
           -> [(FieldNumber, ParsedField)]
           -> Either ParseError acc
foldFields parsers = foldM applyOne
  where applyOne acc (fn, field) =
            case M.lookup (fromIntegral . getFieldNumber $ fn) parsers of
                Nothing              -> pure acc
                Just (parser, apply) ->
                    unParser parser Left (\a -> Right (apply a acc)) field

-- | Parse a message (encoded in the raw wire format) using the specified
-- `Parser`.
parse :: Parser RawMessage a -> B.ByteString -> Either ParseError a
parse = parseWith Left Right
{-# INLINE parse #-}

parseWith :: (ParseError -> r) -> (a -> r) -> Parser RawMessage a -> B.ByteString -> r
parseWith bad good parser bs = either bad (unParser parser bad good . toMap) (decodeWireErr bs)
{-# INLINE parseWith #-}

{- RULES "either/parse" forall bad good p bs.
                         either bad good (parse p bs) = parseWith bad good p bs #-}


-- | To comply with the protobuf spec, if there are multiple fields with the same
-- field number, this will always return the last one.
parsedField :: RawField -> Maybe RawPrimitive
parsedField xs = case xs of
    [] -> Nothing
    (x:_) -> Just x
{-# INLINE parsedField #-}

fromEither :: (input -> Either ParseError a) -> Parser input a
fromEither f = MkParser $ \bad good inp -> either bad good (f inp)
{-# INLINE fromEither #-}


throwWireTypeError :: Show input
                   => String
                   -> input
                   -> ParseError
throwWireTypeError expected wrong =
    WireTypeError (pack msg)
  where
    msg = "Wrong wiretype. Expected " ++ expected ++ " but got " ++ show wrong
{-# NOINLINE throwWireTypeError #-}

throwCerealError :: String -> String -> ParseError
throwCerealError expected cerealErr =
    BinaryError (pack msg)
  where
    msg = "Failed to parse contents of " ++
        expected ++ " field. " ++ "Error from cereal was: " ++ cerealErr
{-# NOINLINE throwCerealError #-}

parseVarInt :: Integral a => Parser RawPrimitive a
parseVarInt = MkParser $ \bad good ->
    \case
        VarintField i -> good (fromIntegral i)
        wrong -> bad $ throwWireTypeError "varint" wrong

runGetPacked :: Get a -> Parser RawPrimitive a
runGetPacked g = MkParser $ \bad good ->
    \case
        LengthDelimitedField bs ->
            case runGet g bs of
                Left e -> bad $ throwCerealError "packed repeated field" e
                Right xs -> good xs
        wrong -> bad $ throwWireTypeError "packed repeated field" wrong

runGetFixed32 :: Get a -> Parser RawPrimitive a
runGetFixed32 g = MkParser $ \bad good ->
    \case
        Fixed32Field bs -> case runGet g bs of
            Left e -> bad $ throwCerealError "fixed32 field" e
            Right x -> good x
        wrong -> bad $ throwWireTypeError "fixed 32 field" wrong

runGetFixed64 :: Get a -> Parser RawPrimitive a
runGetFixed64 g = MkParser $ \bad good ->
    \case
        Fixed64Field bs -> case runGet g bs of
            Left e -> bad $ throwCerealError "fixed 64 field" e
            Right x -> good x
        wrong -> bad $ throwWireTypeError "fixed 64 field" wrong

bytes :: Parser RawPrimitive B.ByteString
bytes = MkParser $ \bad good ->
    \case
        LengthDelimitedField bs ->
            good $! B.copy bs
        wrong -> bad $ throwWireTypeError "bytes" wrong

-- | Parse a Boolean value.
bool :: Parser RawPrimitive Bool
bool = MkParser $ \bad good ->
    \case
        VarintField i -> good $! i /= 0
        wrong -> bad $ throwWireTypeError "bool" wrong

-- | Parse a primitive with the @int32@ wire type.
int32 :: Parser RawPrimitive Int32
int32 = parseVarInt

-- | Parse a primitive with the @int64@ wire type.
int64 :: Parser RawPrimitive Int64
int64 = parseVarInt

-- | Parse a primitive with the @uint32@ wire type.
uint32 :: Parser RawPrimitive Word32
uint32 = parseVarInt

-- | Parse a primitive with the @uint64@ wire type.
uint64 :: Parser RawPrimitive Word64
uint64 = parseVarInt

-- | Parse a primitive with the @sint32@ wire type.
sint32 :: Parser RawPrimitive Int32
sint32 = fmap (fromIntegral . (zigZagDecode :: Word32 -> Word32)) parseVarInt

-- | Parse a primitive with the @sint64@ wire type.
sint64 :: Parser RawPrimitive Int64
sint64 = fmap (fromIntegral . (zigZagDecode :: Word64 -> Word64)) parseVarInt

-- | Parse a primitive with the @bytes@ wire type as a 'B.ByteString'.
byteString :: Parser RawPrimitive B.ByteString
byteString = bytes

-- | Parse a primitive with the @bytes@ wire type as a lazy 'BL.ByteString'.
lazyByteString :: Parser RawPrimitive BL.ByteString
lazyByteString = fmap BL.fromStrict bytes

-- | Parse a primitive with the @bytes@ wire type as 'Text'.
text :: Parser RawPrimitive Text
text = MkParser $ \bad good ->
    \case
        LengthDelimitedField bs ->
            case decodeUtf8' $ BL.fromStrict bs of
                Left err -> bad (BinaryError (pack ("Failed to decode UTF-8: " ++
                                                         show err)))
                Right txt -> good txt
        wrong -> bad $ throwWireTypeError "string" wrong

-- | Parse a primitive with an enumerated type.
--
-- This parser will return 'Left' if the encoded integer value
-- is not a code for a known enumerator.
enum :: forall e. ProtoEnum e => Parser RawPrimitive (Either Int32 e)
enum = fmap toEither parseVarInt
  where
    toEither :: Int32 -> Either Int32 e
    toEither i
      | Just e <- toProtoEnumMay i = Right e
      | otherwise = Left i

-- | Parse a packed collection of variable-width integer values (any of @int32@,
-- @int64@, @sint32@, @sint64@, @uint32@, @uint64@ or enumerations).
packedVarints :: Integral a => Parser RawPrimitive [a]
packedVarints = fmap (fmap fromIntegral) (runGetPacked (many getBase128Varint))

getBase128Varint :: Get Word64
getBase128Varint = loop 0 0
  where
    loop !i !w64 = do
        w8 <- getWord8
        if base128Terminal w8
            then return $ combine i w64 w8
            else loop (i + 1) (combine i w64 w8)
    base128Terminal w8 = (not . (`testBit` 7)) $ w8
    combine i w64 w8 = (w64 .|.
                            (fromIntegral (w8 `clearBit` 7)
                             `shiftL`
                             (i * 7)))



-- | Parse a packed collection of @float@ values.
packedFloats :: Parser RawPrimitive [Float]
packedFloats = runGetPacked (many getFloat32le)

-- | Parse a packed collection of @double@ values.
packedDoubles :: Parser RawPrimitive [Double]
packedDoubles = runGetPacked (many getFloat64le)

-- | Parse a packed collection of @fixed32@ values.
packedFixed32 :: Integral a => Parser RawPrimitive [a]
packedFixed32 = fmap (fmap fromIntegral) (runGetPacked (many getWord32le))

-- | Parse a packed collection of @fixed64@ values.
packedFixed64 :: Integral a => Parser RawPrimitive [a]
packedFixed64 = fmap (fmap fromIntegral) (runGetPacked (many getWord64le))

-- | Parse a @float@.
float :: Parser RawPrimitive Float
float = runGetFixed32 getFloat32le

-- | Parse a @double@.
double :: Parser RawPrimitive Double
double = runGetFixed64 getFloat64le

-- | Parse an integer primitive with the @fixed32@ wire type.
fixed32 :: Parser RawPrimitive Word32
fixed32 = runGetFixed32 getWord32le

-- | Parse an integer primitive with the @fixed64@ wire type.
fixed64 :: Parser RawPrimitive Word64
fixed64 = runGetFixed64 getWord64le

-- | Parse a signed integer primitive with the @fixed32@ wire type.
sfixed32 :: Parser RawPrimitive Int32
sfixed32 = runGetFixed32 getInt32le

-- | Parse a signed integer primitive with the @fixed64@ wire type.
sfixed64 :: Parser RawPrimitive Int64
sfixed64 = runGetFixed64 getInt64le

-- | Turn a field parser into a message parser, by specifying the 'FieldNumber'.
--
-- This parser will fail if the specified 'FieldNumber' is not present.
--
-- For example:
--
-- > one float `at` fieldNumber 1 :: Parser RawMessage (Maybe Float)
at :: Parser RawField a -> FieldNumber -> Parser RawMessage a
at parser fn = MkParser $ \bad good -> unParser parser bad good . M.findWithDefault mempty (fromIntegral . getFieldNumber $ fn)

-- | Try to parse different field numbers with their respective parsers. This is
-- used to express alternative between possible fields of a oneof.
--
-- TODO: contrary to the protobuf spec, in the case of multiple fields number
-- matching the oneof content, the choice of field is biased to the order of the
-- list, instead of being biased to the last field of group of field number in
-- the oneof. This is related to the Map used for input that preserve order
-- across multiple invocation of the same field, but not across a group of
-- field.
oneof :: a
         -- ^ The value to produce when no field numbers belonging to the oneof
         -- are present in the input
      -> [(FieldNumber, Parser RawField a)]
         -- ^ Left-biased oneof field parsers, one per field number belonging to
         -- the oneof
      -> Parser RawMessage a
oneof def parsersByFieldNum = MkParser $ \bad good input ->
  case msum ((\(num,p) -> (p,) <$> M.lookup (fromIntegral . getFieldNumber $ num) input) <$> parsersByFieldNum) of
    Nothing     -> good def
    Just (p, v) -> unParser p bad good v

-- | This turns a primitive parser into a field parser by keeping the
-- last received value, or return a default value if the field number is missing.
--
-- Used to ensure that we return the last value with the given field number
-- in the message, in compliance with the protobuf standard.
--
-- The protocol buffers specification specifies default values for
-- primitive types.
--
-- For example:
--
-- > one float 0 :: Parser RawField Float
one :: Parser RawPrimitive a -> a -> Parser RawField a
one parser def = MkParser $ \bad good i ->
  maybe (good def) (unParser parser bad good) (parsedField i)

-- | Parse a repeated field, or an unpacked collection of primitives.
--
-- Each value with the identified 'FieldNumber' will be passed to the parser
-- in the first argument, to be converted into a value of the correct type.
--
-- For example, to parse a packed collection of @uint32@ values:
--
-- > repeated uint32 :: Parser RawField ([Word32])
--
-- or to parse a collection of embedded messages:
--
-- > repeated . embedded' :: Parser RawMessage a -> Parser RawField ([a])
repeated :: Parser RawPrimitive a -> Parser RawField [a]
repeated parser = do
  i <- id
  result <- mapM (thunkParser parser) i
  pure (reverse result)
{-# NOINLINE repeated #-}


throwEmbeddedParseError :: ParseError
                        -> ParseError
throwEmbeddedParseError err = EmbeddedError "Failed to parse embedded message. " (Just err)

-- | For a field containing an embedded message, parse as far as getting the
-- wire-level fields out of the message.
embeddedToParsedFields :: Parser RawPrimitive RawMessage
embeddedToParsedFields = MkParser $ \bad good ->
  \case
    (LengthDelimitedField bs) -> either (bad . throwEmbeddedParseError) (good . toMap) (decodeWireErr bs)
    wrong -> bad $ throwWireTypeError "embedded" wrong


thunkParser :: (Parser i x) -> i -> Parser any x
thunkParser (MkParser p) i = MkParser $ \bad good _ -> p bad good i


-- | Create a field parser for an embedded message, from a message parser.
--
-- The protobuf spec requires that embedded messages be mergeable, so that
-- protobuf encoding has the flexibility to transmit embedded messages in
-- pieces. This function reassembles the pieces, and must be used to parse all
-- embedded non-repeated messages.
--
-- If the embedded message is not found in the outer message, this function
-- returns 'Nothing'.
embedded :: Parser RawMessage a -> Parser RawField (Maybe a)
embedded p = do
    xs <- id
    if null xs then pure Nothing
    else do
      innerMaps <- T.mapM (thunkParser embeddedToParsedFields) xs
      let combinedMap = foldl' (M.unionWith (<>)) M.empty innerMaps
      MkParser $ \bad good _ -> unParser p bad (good . Just) combinedMap
{-# NOINLINED embedded #-}

-- | Create a primitive parser for an embedded message from a message parser.
--
-- This parser does no merging of fields if multiple message fragments are
-- sent separately.
embedded' :: Parser RawMessage a -> Parser RawPrimitive a
embedded' parser = MkParser $ \bad good ->
    \case
        LengthDelimitedField bs ->
            parseWith (bad . throwEmbeddedParseError) good
                      parser bs
        wrong -> bad $ throwWireTypeError "embedded" wrong
{-# NOINLINED embedded' #-}

