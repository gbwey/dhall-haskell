{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-| This module contains logic for converting Dhall expressions to and from
    CBOR expressions which can in turn be converted to and from a binary
    representation
-}

module Dhall.Binary
    ( -- * Standard versions
      StandardVersion(..)
    , renderStandardVersion

    -- * Encoding and decoding
    , encodeExpression
    , decodeExpression

    -- * Exceptions
    , DecodingFailure(..)
    ) where

import Codec.CBOR.Decoding  (Decoder, TokenType (..))
import Codec.CBOR.Encoding  (Encoding)
import Codec.Serialise      (Serialise (decode, encode))
import Control.Applicative  (empty, (<|>))
import Control.Exception    (Exception)
import Data.ByteString.Lazy (ByteString)
import Dhall.Syntax
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , DhallDouble (..)
    , Directory (..)
    , Expr (..)
    , File (..)
    , FilePrefix (..)
    , Import (..)
    , ImportHashed (..)
    , ImportMode (..)
    , ImportType (..)
    , MultiLet (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , Scheme (..)
    , URL (..)
    , Var (..)
    , NonZero(..)
    , mkNonZeroUnsafe
    , DateTime(..)
    , Regex(..)
    )

import Data.Foldable (toList)
import Data.Text     (Text)
import Data.Text.Encoding (encodeUtf8,decodeUtf8)
import Data.Void     (Void, absurd)
import GHC.Float     (double2Float, float2Double)
import Numeric.Half  (fromHalf, toHalf)

import qualified Codec.CBOR.ByteArray
import qualified Codec.CBOR.Decoding   as Decoding
import qualified Codec.CBOR.Encoding   as Encoding
import qualified Codec.CBOR.Read       as Read
import qualified Codec.Serialise       as Serialise
import qualified Data.ByteArray
import qualified Data.ByteString
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Short
import qualified Data.Sequence
import qualified Dhall.Crypto
import qualified Dhall.Map
import qualified Dhall.Set
import qualified Dhall.Syntax          as Syntax
import qualified Text.Printf           as Printf
import qualified Data.Ratio
import Data.Ratio ((%))
import qualified Control.Monad as Monad
--import Debug.Trace

{-| Supported version strings

    This exists primarily for backwards compatibility for expressions encoded
    before Dhall removed version tags from the binary encoding
-}
data StandardVersion
    = NoVersion
    -- ^ No version string
    | V_5_0_0
    -- ^ Version "5.0.0"
    | V_4_0_0
    -- ^ Version "4.0.0"
    | V_3_0_0
    -- ^ Version "3.0.0"
    | V_2_0_0
    -- ^ Version "2.0.0"
    | V_1_0_0
    -- ^ Version "1.0.0"
    deriving (Enum, Bounded)

-- | Render a `StandardVersion` as `Text`
renderStandardVersion :: StandardVersion -> Text
renderStandardVersion NoVersion = "none"
renderStandardVersion V_1_0_0   = "1.0.0"
renderStandardVersion V_2_0_0   = "2.0.0"
renderStandardVersion V_3_0_0   = "3.0.0"
renderStandardVersion V_4_0_0   = "4.0.0"
renderStandardVersion V_5_0_0   = "5.0.0"

{-| Convert a function applied to multiple arguments to the base function and
    the list of arguments
-}
unApply :: Expr s a -> (Expr s a, [Expr s a])
unApply e₀ = (baseFunction₀, diffArguments₀ [])
  where
    ~(baseFunction₀, diffArguments₀) = go e₀

    go (App f a) = (baseFunction, diffArguments . (a :))
      where
        ~(baseFunction, diffArguments) = go f

    go (Note _ e) = go e

    go baseFunction = (baseFunction, id)

decodeExpressionInternal :: (Int -> Decoder s a) -> Decoder s (Expr t a)
decodeExpressionInternal decodeEmbed = go
  where
    go = do
        let die message = fail ("Dhall.Binary.decodeExpressionInternal: " <> message)

        tokenType₀ <- Decoding.peekTokenType

        case tokenType₀ of
            TypeUInt -> do
                !n <- fromIntegral <$> Decoding.decodeWord

                return (Var (V "_" n))

            TypeUInt64 -> do
                !n <- fromIntegral <$> Decoding.decodeWord64

                return (Var (V "_" n))

            TypeFloat16 -> do
                !n <- float2Double <$> Decoding.decodeFloat

                return (DoubleLit (DhallDouble n))

            TypeFloat32 -> do
                !n <- float2Double <$> Decoding.decodeFloat

                return (DoubleLit (DhallDouble n))

            TypeFloat64 -> do
                !n <- Decoding.decodeDouble

                return (DoubleLit (DhallDouble n))

            TypeBool -> do
                !b <- Decoding.decodeBool

                return (BoolLit b)

            TypeString -> do
                !ba <- Decoding.decodeUtf8ByteArray

                let sb = Codec.CBOR.ByteArray.toShortByteString ba

                case Data.ByteString.Short.length sb of
                    2  | sb == "SZ" -> return SZ
                       | sb == "SS" -> return SS
                    4  | sb == "Bool"              -> return Bool
                       | sb == "List"              -> return List
                       | sb == "None"              -> return None
                       | sb == "Text"              -> return Text
                       | sb == "Type"              -> return (Const Type)
                       | sb == "Kind"              -> return (Const Kind)
                       | sb == "Sort"              -> return (Const Sort)
                    5  | sb == "Regex" -> return Regex
                       | sb == "Proof" -> return Proof
                       | sb == "PVoid" -> return PVoid
                    6  | sb == "Double"            -> return Double
                       | sb == "SS/add" -> return SSAdd
                    7  | sb == "Integer"           -> return Integer
                       | sb == "Natural"           -> return Natural
                       | sb == "NonZero" -> return NonZero
                    8  | sb == "Optional"          -> return Optional
                       | sb == "DateTime" -> return DateTime
                       | sb == "Rational" -> return Rational
                       | sb == "SS/equal" -> return SSEqual
                    9  | sb == "List/fold"         -> return ListFold
                       | sb == "List/head"         -> return ListHead
                       | sb == "List/last"         -> return ListLast
                       | sb == "Text/show"         -> return TextShow
                       | sb == "Text/pack" -> return TextPack
                       | sb == "ListFixed" -> return ListFixed
                    10 | sb == "List/build"        -> return ListBuild
                       | sb == "Regex/show" -> return RegexShow
                       | sb == "Regex/scan" -> return RegexScan
                       | sb == "Sym/toText" -> return SymToText
                    11 | sb == "Double/show"       -> return DoubleShow
                       | sb == "List/length"       -> return ListLength
                       | sb == "Natural/odd"       -> return NaturalOdd
                       | sb == "NonZero/div" -> return NonZeroDiv
                       | sb == "NonZero/mod" -> return NonZeroMod
                       | sb == "NonZero/log" -> return NonZeroLog
                       | sb == "NonZero/add" -> return NonZeroAdd
                       | sb == "Regex/match" -> return RegexMatch
                       | sb == "Regex/split" -> return RegexSplit
                       | sb == "Regex/parse" -> return RegexParse
                       | sb == "Natural/gcd" -> return NaturalGcd
                       | sb == "Integer/add" -> return IntegerAdd
                       | sb == "Integer/and" -> return IntegerAnd
                       | sb == "Integer/xor" -> return IntegerXor
                       | sb == "List/choose" -> return ListChoose
                       | sb == "Text/unpack" -> return TextUnpack
                       | sb == "Text/toList" -> return TextToList
                       | sb == "Text/length" -> return TextLength
                       | sb == "SS/subtract" -> return SSSubtract
                       | sb == "SS/lessThan" -> return SSLessThan
                       | sb == "PVoid/error" -> return PVoidError
                    12 | sb == "Integer/show"      -> return IntegerShow
                       | sb == "List/indexed"      -> return ListIndexed
                       | sb == "List/reverse"      -> return ListReverse
                       | sb == "Natural/even"      -> return NaturalEven
                       | sb == "Natural/fold"      -> return NaturalFold
                       | sb == "Natural/show"      -> return NaturalShow
                       | sb == "NonZero/show" -> return NonZeroShow
                       | sb == "Regex/replix" -> return RegexReplix
                       | sb == "Regex/toText" -> return RegexToText
                       | sb == "Double/parse" -> return DoubleParse
                       | sb == "Text/toLower" -> return TextToLower
                       | sb == "Text/toUpper" -> return TextToUpper
                       | sb == "Text/compare" -> return TextCompare
                       | sb == "Sym/fromText" -> return SymFromText
                       | sb == "SS/toNonZero" -> return SSToNonZero
                       | sb == "SS/toNatural" -> return SSToNatural
                       | sb == "Proof/toBool" -> return ProofToBool
                    13 | sb == "Integer/clamp"     -> return IntegerClamp
                       | sb == "Natural/build"     -> return NaturalBuild
                       | sb == "NonZero/clamp" -> return NonZeroClamp
                       | sb == "NonZero/parse" -> return NonZeroParse
                       | sb == "DateTime/show" -> return DateTimeShow
                       | sb == "Regex/replace" -> return RegexReplace
                       | sb == "Rational/show" -> return RationalShow
                       | sb == "Natural/parse" -> return NaturalParse
                       | sb == "Integer/parse" -> return IntegerParse
                    14 | sb == "Integer/negate"    -> return IntegerNegate
                       | sb == "Natural/isZero"    -> return NaturalIsZero
                       | sb == "DateTime/parse" -> return DateTimeParse
                       | sb == "Rational/parse" -> return RationalParse
                       | sb == "Natural/toBits" -> return NaturalToBits
                       | sb == "ListFixed/head" -> return ListFixedHead
                       | sb == "ListFixed/tail" -> return ListFixedTail
                       | sb == "SS/fromNonZero" -> return SSFromNonZero
                       | sb == "Proof/fromBool" -> return ProofFromBool
                    15 | sb == "DateTime/toWeek" -> return DateTimeToWeek
                       | sb == "DateTime/toDate" -> return DateTimeToDate
                       | sb == "PVoid/undefined" -> return PVoidUndefined
                    16 | sb == "Integer/toDouble"  -> return IntegerToDouble
                       | sb == "Natural/subtract"  -> return NaturalSubtract
                       | sb == "NonZero/multiply" -> return NonZeroMultiply
                       | sb == "DateTime/addDays" -> return DateTimeAddDays
                       | sb == "Integer/multiply" -> return IntegerMultiply
                       | sb == "ListFixed/toList" -> return ListFixedToList
                    17 | sb == "Natural/toInteger" -> return NaturalToInteger
                       | sb == "NonZero/toNatural" -> return NonZeroToNatural
                       | sb == "NonZero/toInteger" -> return NonZeroToInteger
                       | sb == "DateTime/addYears" -> return DateTimeAddYears
                       | sb == "DateTime/fromWeek" -> return DateTimeFromWeek
                       | sb == "DateTime/fromDate" -> return DateTimeFromDate
                       | sb == "Rational/toDouble" -> return RationalToDouble
                       | sb == "List/permutations" -> return ListPermutations
                    18 | sb == "DateTime/toSeconds" -> return DateTimeToSeconds
                       | sb == "DateTime/addMonths" -> return DateTimeAddMonths
                       | sb == "ListFixed/fromList" -> return ListFixedFromList
                    19 | sb == "Rational/fromDouble" -> return RationalFromDouble
                       | sb == "PVoid/kindUndefined" -> return PVoidKindUndefined
                    20 | sb == "DateTime/fromSeconds" -> return DateTimeFromSeconds
                    21 | sb == "DateTime/getJulianDay" -> return DateTimeGetJulianDay
                       | sb == "DateTime/setJulianDay" -> return DateTimeSetJulianDay
                       | sb == "Rational/fromRational" -> return RationalFromRational
                    23 | sb == "DateTime/lastDayOfMonth" -> return DateTimeLastDayOfMonth
                    _                              -> die ("Unrecognized built-in: " <> show sb)



            TypeListLen -> do
                len <- Decoding.decodeListLen

                case len of
                    0 -> die "Missing tag"
                    _ -> return ()

                tokenType₁ <- Decoding.peekTokenType

                case tokenType₁ of
                    TypeString -> do
                        x <- Decoding.decodeString

                        if x == "_"
                            then die "Non-standard encoding of an α-normalized variable"
                            else return ()

                        tokenType₂ <- Decoding.peekTokenType

                        case tokenType₂ of
                            TypeUInt -> do
                                !n <- fromIntegral <$> Decoding.decodeWord

                                return (Var (V x n))

                            TypeUInt64 -> do
                                !n <- fromIntegral <$> Decoding.decodeWord64

                                return (Var (V x n))

                            _ ->
                                die ("Unexpected token type for variable index: " <> show tokenType₂)

                    TypeUInt -> do
                        tag <- Decoding.decodeWord

                        case tag of
                            0 -> do
                                !f <- go

                                let loop n !acc
                                        | n <= 0    = return acc
                                        | otherwise = do
                                              !x <- go
                                              loop (n - 1) (App acc x)

                                let nArgs = len - 2

                                if nArgs <= 0
                                    then die "Non-standard encoding of a function with no arguments"
                                    else loop nArgs f

                            1 ->
                                case len of
                                    3 -> do
                                        _A <- go

                                        b <- go

                                        return (Lam "_" _A b)

                                    4 -> do
                                        x <- Decoding.decodeString

                                        if x == "_"
                                            then die "Non-standard encoding of a λ expression"
                                            else return ()

                                        _A <- go

                                        b <- go

                                        return (Lam x _A b)

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a λ expression: " <> show len)

                            2 ->
                                case len of
                                    3 -> do
                                        _A <- go

                                        _B <- go

                                        return (Pi "_" _A _B)

                                    4 -> do
                                        x <- Decoding.decodeString

                                        if x == "_"
                                            then die "Non-standard encoding of a ∀ expression"
                                            else return ()

                                        _A <- go

                                        _B <- go

                                        return (Pi x _A _B)

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a ∀ expression: " <> show len)

                            3 -> do
                                opcode <- Decoding.decodeWord

                                op <- case opcode of
                                    0  -> return BoolOr
                                    1  -> return BoolAnd
                                    2  -> return BoolEQ
                                    3  -> return BoolNE
                                    4  -> return NaturalPlus
                                    5  -> return NaturalTimes
                                    6  -> return TextAppend
                                    7  -> return ListAppend
                                    8  -> return (Combine Nothing)
                                    9  -> return (Prefer PreferFromSource)
                                    10 -> return CombineTypes
                                    11 -> return ImportAlt
                                    12 -> return Equivalent
                                    13 -> return RecordCompletion
                                    14 -> return RationalPercent
                                    _  -> die ("Unrecognized operator code: " <> show opcode)

                                l <- go

                                r <- go

                                return (op l r)

                            4 ->
                                case len of
                                    2 -> do
                                        _T <- go

                                        return (ListLit (Just (App List _T)) empty)

                                    _ -> do
                                        Decoding.decodeNull

                                        xs <- Data.Sequence.replicateA (len - 2) go
                                        return (ListLit Nothing xs)

                            29 -> do
                                        Decoding.decodeNull
                                        x:xs <- Monad.replicateM (len - 2) go
                                        return (ListFixedLit x (Data.Sequence.fromList xs))

                            30 -> do
                                        Decoding.decodeNull
                                        return SZLit
                            31 -> do
                                        Decoding.decodeNull
                                        t <- go
                                        return $ SSLit t

                            32 -> do
                                        Decoding.decodeNull
                                        return ProofLit

                            33 -> do
                                z <- Decoding.decodeBytes
                                return (SymLit (decodeUtf8 z))

                            34 -> do
                                z <- Decoding.decodeBytes
                                return (Sym (decodeUtf8 z))

                            5 -> do
                                Decoding.decodeNull

                                t <- go

                                return (Some t)

                            6 -> do
                                t <- go

                                u <- go

                                case len of
                                    3 ->
                                        return (Merge t u Nothing)

                                    4 -> do
                                        _T <- go

                                        return (Merge t u (Just _T))

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a `merge` expression: " <> show len)

                            7 -> do
                                mapLength <- Decoding.decodeMapLen

                                xTs <- replicateDecoder mapLength $ do
                                    x <- Decoding.decodeString

                                    _T <- go

                                    return (x, Syntax.makeRecordField _T)

                                return (Record (Dhall.Map.fromList xTs))

                            8 -> do
                                mapLength <- Decoding.decodeMapLen

                                xts <- replicateDecoder mapLength $ do
                                    x <- Decoding.decodeString

                                    t <- go

                                    return (x, Syntax.makeRecordField t)

                                return (RecordLit (Dhall.Map.fromList xts))

                            9 -> do
                                t <- go

                                x <- Decoding.decodeString

                                return (Field t x)

                            10 -> do
                                t <- go

                                xs <- case len of
                                    3 -> do
                                        tokenType₂ <- Decoding.peekTokenType

                                        case tokenType₂ of
                                            TypeListLen -> do
                                                _ <- Decoding.decodeListLen

                                                _T <- go

                                                return (Right _T)

                                            TypeString -> do
                                                x <- Decoding.decodeString
                                                return (Left (Dhall.Set.fromList [x]))

                                            _ ->
                                                die ("Unexpected token type for projection: " <> show tokenType₂)

                                    _ -> do
                                        xs <- replicateDecoder (len - 2) Decoding.decodeString

                                        return (Left (Dhall.Set.fromList xs))

                                return (Project t xs)

                            11 -> do
                                mapLength <- Decoding.decodeMapLen

                                xTs <- replicateDecoder mapLength $ do
                                    x <- Decoding.decodeString

                                    tokenType₂ <- Decoding.peekTokenType

                                    mT <- case tokenType₂ of
                                        TypeNull -> do
                                            Decoding.decodeNull

                                            return Nothing

                                        _ -> do
                                            _T <- go

                                            return (Just _T)

                                    return (x, mT)

                                return (Union (Dhall.Map.fromList xTs))

                            14 -> do
                                t <- go

                                l <- go

                                r <- go

                                return (BoolIf t l r)

                            15 -> do
                                tokenType₂ <- Decoding.peekTokenType

                                case tokenType₂ of
                                    TypeUInt -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord

                                        return (NaturalLit n)

                                    TypeUInt64 -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord64

                                        return (NaturalLit n)

                                    TypeInteger -> do
                                        !n <- fromIntegral <$> Decoding.decodeInteger
                                        return (NaturalLit n)

                                    _ ->
                                        die ("Unexpected token type for Natural literal: " <> show tokenType₂)

                            16 -> do
                                tokenType₂ <- Decoding.peekTokenType

                                case tokenType₂ of
                                    TypeUInt -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord

                                        return (IntegerLit n)

                                    TypeUInt64 -> do
                                        !n <- fromIntegral <$> Decoding.decodeWord64

                                        return (IntegerLit n)

                                    TypeNInt -> do
                                        !n <- fromIntegral <$> Decoding.decodeNegWord

                                        return (IntegerLit $! (-1 - n))

                                    TypeNInt64 -> do
                                        !n <- fromIntegral <$> Decoding.decodeNegWord64

                                        return (IntegerLit $! (-1 - n))
                                    TypeInteger -> do
                                        n <- Decoding.decodeInteger
                                        return (IntegerLit n)

                                    _ ->
                                        die ("Unexpected token type for Integer literal: " <> show tokenType₂)

                            17 -> do
                                tokenType₂ <- Decoding.peekTokenType

                                case tokenType₂ of
                                    TypeUInt -> do
                                        n <- Decoding.decodeWord
                                        return (NonZeroLit (mkNonZeroUnsafe (fromIntegral n)))

                                    TypeUInt64 -> do
                                        n <- Decoding.decodeWord64

                                        return (NonZeroLit (mkNonZeroUnsafe (fromIntegral n)))

                                    TypeInteger -> do
                                        n <- Decoding.decodeInteger
                                        return (NonZeroLit (mkNonZeroUnsafe (fromIntegral n)))

                                    _ -> do
                                        die ("Unexpected token type for NonZero literal: " <> show tokenType₂)

                            18 -> do
                                xys <- replicateDecoder ((len - 2) `quot` 2) $ do
                                    x <- Decoding.decodeString

                                    y <- go

                                    return (x, y)

                                z <- Decoding.decodeString

                                return (TextLit (Chunks xys z))

                            21 -> do

                                z <- Decoding.decodeBytes

                                return (RegexLit (RegexC (decodeUtf8 z)))

                            22 -> do
                                    x <- do
                                          tokenType₂ <- Decoding.peekTokenType

                                          case tokenType₂ of
                                              TypeUInt -> do
                                                  n <- Decoding.decodeWord
                                                  return (fromIntegral n)

                                              TypeUInt64 -> do
                                                  n <- Decoding.decodeWord64
                                                  return (fromIntegral n)

                                              TypeNInt -> do
                                                  n <- Decoding.decodeNegWord
                                                  return (-1 - fromIntegral n)

                                              TypeNInt64 -> do
                                                  n <- Decoding.decodeNegWord64
                                                  return (-1 - fromIntegral n)

                                              TypeInteger -> do
                                                  n <- Decoding.decodeInteger
                                                  return (fromIntegral n)

                                              _ -> do
                                                  die ("Unexpected token type for Rational numerator literal: " <> show tokenType₂)

                                    y <- do
                                          tokenType₂ <- Decoding.peekTokenType

                                          case tokenType₂ of
                                              TypeUInt -> do
                                                  n <- Decoding.decodeWord
                                                  return (fromIntegral n)

                                              TypeUInt64 -> do
                                                  n <- Decoding.decodeWord64
                                                  return (fromIntegral n)

                                              TypeInteger -> do
                                                  n <- Decoding.decodeInteger
                                                  return (fromIntegral n)

                                              _ -> do
                                                  die ("Unexpected token type for Rational denominator literal: " <> show tokenType₂)
                                    return (RationalLit (x % y))

                            19 -> do
                                t <- go

                                return (Assert t)

                            20 -> do
                                tokenType₂ <- Decoding.peekTokenType

                                case tokenType₂ of
                                    TypeUInt -> do
                                        n <- Decoding.decodeWord
                                        return (DateTimeLit (DateTimeC (fromIntegral n)))

                                    TypeUInt64 -> do
                                        n <- Decoding.decodeWord64
                                        return (DateTimeLit (DateTimeC (fromIntegral n)))

                                    TypeNInt -> do
                                        n <- Decoding.decodeNegWord
                                        return (DateTimeLit (DateTimeC (-1 - fromIntegral n)))

                                    TypeNInt64 -> do
                                        n <- Decoding.decodeNegWord64
                                        return (DateTimeLit (DateTimeC (-1 - fromIntegral n)))

                                    TypeInteger -> do
                                        n <- Decoding.decodeInteger
                                        return (DateTimeLit (DateTimeC (fromIntegral n)))

                                    _ -> do
                                        die ("Unexpected token type for DateTime literal: " <> show tokenType₂)

                            24 -> do
                                fmap Embed (decodeEmbed len)

                            25 -> do
                                bindings <- replicateDecoder ((len - 2) `quot` 3) $ do
                                    x <- Decoding.decodeString

                                    tokenType₂ <- Decoding.peekTokenType

                                    mA <- case tokenType₂ of
                                        TypeNull -> do
                                            Decoding.decodeNull

                                            return Nothing

                                        _ -> do
                                            _A <- go

                                            return (Just (Nothing, _A))

                                    a <- go

                                    return (Binding Nothing x Nothing mA Nothing a)

                                b <- go

                                return (foldr Let b bindings)

                            26 -> do
                                t <- go

                                _T <- go

                                return (Annot t _T)

                            27 -> do
                                t <- go

                                mT <- case len of
                                    2 ->
                                        return Nothing

                                    3 -> do
                                        _T <- go

                                        return (Just _T)

                                    _ ->
                                        die ("Incorrect number of tokens used to encode a type annotation: " <> show len)

                                return (ToMap t mT)

                            28 -> do
                                _T <- go

                                return (ListLit (Just _T) empty)

                            _ ->
                                die ("Unexpected tag: " <> show tag)

                    _ ->
                        die ("Unexpected tag type: " <> show tokenType₁)

            _ ->
                die ("Unexpected initial token: " <> show tokenType₀)

encodeExpressionInternal :: (a -> Encoding) -> Expr Void a -> Encoding
encodeExpressionInternal encodeEmbed = go
  where
    go e = case e of
        Var (V "_" n) ->
            Encoding.encodeInt n

        Var (V x n) ->
                Encoding.encodeListLen 2
            <>  Encoding.encodeString x
            <>  Encoding.encodeInt n

        NonZeroShow ->
            Encoding.encodeString "NonZero/show"

        NonZeroClamp ->
            Encoding.encodeString "NonZero/clamp"

        NonZeroDiv ->
            Encoding.encodeString "NonZero/div"

        NonZeroMod ->
            Encoding.encodeString "NonZero/mod"

        NonZeroLog ->
            Encoding.encodeString "NonZero/log"

        NonZeroAdd ->
            Encoding.encodeString "NonZero/add"

        NonZeroMultiply ->
            Encoding.encodeString "NonZero/multiply"

        NonZeroToNatural ->
            Encoding.encodeString "NonZero/toNatural"

        NonZeroToInteger ->
            Encoding.encodeString "NonZero/toInteger"

        NonZeroParse ->
            Encoding.encodeString "NonZero/parse"

        DateTimeShow ->
            Encoding.encodeString "DateTime/show"
        DateTimeParse ->
            Encoding.encodeString "DateTime/parse"

        DateTimeFromSeconds ->
            Encoding.encodeString "DateTime/fromSeconds"

        DateTimeToSeconds ->
            Encoding.encodeString "DateTime/toSeconds"

        DateTimeAddYears ->
            Encoding.encodeString "DateTime/addYears"
        DateTimeAddMonths ->
            Encoding.encodeString "DateTime/addMonths"
        DateTimeAddDays ->
            Encoding.encodeString "DateTime/addDays"
        DateTimeFromWeek ->
            Encoding.encodeString "DateTime/fromWeek"
        DateTimeToWeek ->
            Encoding.encodeString "DateTime/toWeek"
        DateTimeToDate ->
            Encoding.encodeString "DateTime/toDate"
        DateTimeFromDate ->
            Encoding.encodeString "DateTime/fromDate"
        DateTimeLastDayOfMonth ->
            Encoding.encodeString "DateTime/lastDayOfMonth"

        DateTimeGetJulianDay ->
            Encoding.encodeString "DateTime/getJulianDay"
        DateTimeSetJulianDay ->
            Encoding.encodeString "DateTime/setJulianDay"

        RegexShow ->
            Encoding.encodeString "Regex/show"
        RegexMatch ->
            Encoding.encodeString "Regex/match"
        RegexScan ->
            Encoding.encodeString "Regex/scan"
        RegexSplit ->
            Encoding.encodeString "Regex/split"
        RegexReplace ->
            Encoding.encodeString "Regex/replace"
        RegexReplix ->
            Encoding.encodeString "Regex/replix"
        RegexParse ->
            Encoding.encodeString "Regex/parse"
        RegexToText ->
            Encoding.encodeString "Regex/toText"

        RationalShow ->
            Encoding.encodeString "Rational/show"
        RationalFromDouble ->
            Encoding.encodeString "Rational/fromDouble"
        RationalToDouble ->
            Encoding.encodeString "Rational/toDouble"
        RationalFromRational ->
            Encoding.encodeString "Rational/fromRational"
        RationalParse ->
            Encoding.encodeString "Rational/parse"

        NaturalBuild ->
            Encoding.encodeUtf8ByteArray "Natural/build"

        NaturalFold ->
            Encoding.encodeUtf8ByteArray "Natural/fold"

        NaturalIsZero ->
            Encoding.encodeUtf8ByteArray "Natural/isZero"

        NaturalEven ->
            Encoding.encodeUtf8ByteArray "Natural/even"

        NaturalOdd ->
            Encoding.encodeUtf8ByteArray "Natural/odd"

        NaturalToInteger ->
            Encoding.encodeUtf8ByteArray "Natural/toInteger"

        NaturalShow ->
            Encoding.encodeUtf8ByteArray "Natural/show"

        NaturalParse ->
            Encoding.encodeString "Natural/parse"

        NaturalToBits ->
            Encoding.encodeString "Natural/toBits"

        NaturalSubtract ->
            Encoding.encodeUtf8ByteArray "Natural/subtract"

        NaturalGcd ->
            Encoding.encodeString "Natural/gcd"

        IntegerToDouble ->
            Encoding.encodeUtf8ByteArray "Integer/toDouble"

        IntegerAdd ->
            Encoding.encodeString "Integer/add"

        IntegerMultiply ->
            Encoding.encodeString "Integer/multiply"

        IntegerAnd ->
            Encoding.encodeString "Integer/and"

        IntegerXor ->
            Encoding.encodeString "Integer/xor"

        IntegerClamp ->
            Encoding.encodeUtf8ByteArray "Integer/clamp"

        IntegerNegate ->
            Encoding.encodeUtf8ByteArray "Integer/negate"

        IntegerShow ->
            Encoding.encodeUtf8ByteArray "Integer/show"

        IntegerParse ->
            Encoding.encodeString "Integer/parse"

        DoubleShow ->
            Encoding.encodeUtf8ByteArray "Double/show"

        DoubleParse ->
            Encoding.encodeString "Double/parse"

        ListBuild ->
            Encoding.encodeUtf8ByteArray "List/build"

        ListFold ->
            Encoding.encodeUtf8ByteArray "List/fold"

        ListLength ->
            Encoding.encodeUtf8ByteArray "List/length"

        ListHead ->
            Encoding.encodeUtf8ByteArray "List/head"

        ListLast ->
            Encoding.encodeUtf8ByteArray "List/last"

        ListIndexed ->
            Encoding.encodeUtf8ByteArray "List/indexed"

        ListReverse ->
            Encoding.encodeUtf8ByteArray "List/reverse"

        ListPermutations ->
            Encoding.encodeString "List/permutations"

        ListChoose ->
            Encoding.encodeString "List/choose"

        Bool ->
            Encoding.encodeUtf8ByteArray "Bool"

        Optional ->
            Encoding.encodeUtf8ByteArray "Optional"

        SZ ->
            Encoding.encodeString "SZ"

        SS ->
            Encoding.encodeString "SS"

        Proof ->
            Encoding.encodeString "Proof"

        PVoid ->
            Encoding.encodeString "PVoid"

        None ->
            Encoding.encodeUtf8ByteArray "None"

        NonZero ->
            Encoding.encodeString "NonZero"

        DateTime ->
            Encoding.encodeString "DateTime"

        Regex ->
            Encoding.encodeString "Regex"

        Rational ->
            Encoding.encodeString "Rational"

        Natural ->
            Encoding.encodeUtf8ByteArray "Natural"

        Integer ->
            Encoding.encodeUtf8ByteArray "Integer"

        Double ->
            Encoding.encodeUtf8ByteArray "Double"

        Text ->
            Encoding.encodeUtf8ByteArray "Text"

        TextShow ->
            Encoding.encodeUtf8ByteArray "Text/show"

        TextToLower ->
            Encoding.encodeString "Text/toLower"

        TextToUpper ->
            Encoding.encodeString "Text/toUpper"

        TextUnpack ->
            Encoding.encodeString "Text/unpack"

        TextPack ->
            Encoding.encodeString "Text/pack"

        TextToList ->
            Encoding.encodeString "Text/toList"

        TextLength ->
            Encoding.encodeString "Text/length"

        TextCompare ->
            Encoding.encodeString "Text/compare"

        List ->
            Encoding.encodeUtf8ByteArray "List"

        ListFixed ->
            Encoding.encodeString "ListFixed"

        ListFixedFromList ->
            Encoding.encodeString "ListFixed/fromList"

        ListFixedToList ->
            Encoding.encodeString "ListFixed/toList"

        ListFixedHead ->
            Encoding.encodeString "ListFixed/head"

        ListFixedTail ->
            Encoding.encodeString "ListFixed/tail"

        SymFromText ->
            Encoding.encodeString "Sym/fromText"

        SymToText ->
            Encoding.encodeString "Sym/toText"

        SSFromNonZero ->
            Encoding.encodeString "SS/fromNonZero"

        SSToNonZero ->
            Encoding.encodeString "SS/toNonZero"

        SSToNatural ->
            Encoding.encodeString "SS/toNatural"

        SSAdd ->
            Encoding.encodeString "SS/add"

        SSSubtract ->
            Encoding.encodeString "SS/subtract"

        SSEqual ->
            Encoding.encodeString "SS/equal"

        SSLessThan ->
            Encoding.encodeString "SS/lessThan"

        ProofToBool ->
            Encoding.encodeString "Proof/toBool"

        ProofFromBool ->
            Encoding.encodeString "Proof/fromBool"

        PVoidUndefined ->
            Encoding.encodeString "PVoid/undefined"

        PVoidError ->
            Encoding.encodeString "PVoid/error"

        PVoidKindUndefined ->
            Encoding.encodeString "PVoid/kindUndefined"

        Const Type ->
            Encoding.encodeUtf8ByteArray "Type"

        Const Kind ->
            Encoding.encodeUtf8ByteArray "Kind"

        Const Sort ->
            Encoding.encodeUtf8ByteArray "Sort"

        a@App{} ->
            encodeListN
                (2 + length arguments)
                ( Encoding.encodeInt 0
                : go function
                : map go arguments
                )
          where
            (function, arguments) = unApply a

        Lam "_" _A b ->
            encodeList3
                (Encoding.encodeInt 1)
                (go _A)
                (go b)

        Lam x _A b ->
            encodeList4
                (Encoding.encodeInt 1)
                (Encoding.encodeString x)
                (go _A)
                (go b)

        Pi "_" _A _B ->
            encodeList3
                (Encoding.encodeInt 2)
                (go _A)
                (go _B)

        Pi x _A _B ->
            encodeList4
                (Encoding.encodeInt 2)
                (Encoding.encodeString x)
                (go _A)
                (go _B)

        BoolOr l r ->
            encodeOperator 0 l r

        BoolAnd l r ->
            encodeOperator 1 l r

        BoolEQ l r ->
            encodeOperator 2 l r

        BoolNE l r ->
            encodeOperator 3 l r

        NaturalPlus l r ->
            encodeOperator 4 l r

        RationalPercent l r ->
            encodeOperator 14 l r

        NaturalTimes l r ->
            encodeOperator 5 l r

        TextAppend l r ->
            encodeOperator 6 l r

        ListAppend l r ->
            encodeOperator 7 l r

        Combine _ l r ->
            encodeOperator 8 l r

        Prefer _ l r ->
            encodeOperator 9 l r

        CombineTypes l r ->
            encodeOperator 10 l r

        ImportAlt l r ->
            encodeOperator 11 l r

        Equivalent l r ->
            encodeOperator 12 l r

        RecordCompletion l r ->
            encodeOperator 13 l r

        ListLit _T₀ xs
            | null xs ->
                encodeList2 (Encoding.encodeInt label) _T₁
            | otherwise ->
                encodeListN
                    (2 + length xs)
                    ( Encoding.encodeInt 4
                    : Encoding.encodeNull
                    : map go (Data.Foldable.toList xs)
                    )
          where
            (label, _T₁) = case _T₀ of
                Nothing           -> (4 , Encoding.encodeNull)
                Just (App List t) -> (4 , go t               )
                Just  t           -> (28, go t               )

-- todo: need the string
        SymLit t ->
            encodeList2
                (Encoding.encodeInt 33)
                (Encoding.encodeBytes (encodeUtf8 t))

        Sym t ->
            encodeList2
                (Encoding.encodeInt 34)
                (Encoding.encodeBytes (encodeUtf8 t))

        SZLit ->
             encodeList2
                 (Encoding.encodeInt 30)
                 Encoding.encodeNull

        SSLit t ->
             encodeList3
                 (Encoding.encodeInt 31)
                 Encoding.encodeNull
                 (go t)

        ProofLit ->
             encodeList2
                 (Encoding.encodeInt 32)
                 Encoding.encodeNull

        ListFixedLit x xs ->
                encodeListN
                    (2 + 1 + length xs)
                    ( Encoding.encodeInt 29
                    : Encoding.encodeNull
                    : map go (x:Data.Foldable.toList xs)
                    )

        Some t ->
            encodeList3
                (Encoding.encodeInt 5)
                Encoding.encodeNull
                (go t)

        Merge t u Nothing ->
            encodeList3
                (Encoding.encodeInt 6)
                (go t)
                (go u)

        Merge t u (Just _T) ->
            encodeList4
                (Encoding.encodeInt 6)
                (go t)
                (go u)
                (go _T)

        Record xTs ->
            encodeList2
                (Encoding.encodeInt 7)
                (encodeMapWith (go . recordFieldValue) xTs)

        RecordLit xts ->
            encodeList2
                (Encoding.encodeInt 8)
                (encodeMapWith (go. recordFieldValue) xts)

        Field t x ->
            encodeList3
                (Encoding.encodeInt 9)
                (go t)
                (Encoding.encodeString x)

        Project t (Left xs) ->
            encodeListN
                (2 + Dhall.Set.size xs)
                ( Encoding.encodeInt 10
                : go t
                : map Encoding.encodeString (Dhall.Set.toList xs)
                )

        Project t (Right _T) ->
            encodeList3
                (Encoding.encodeInt 10)
                (go t)
                (encodeList1 (go _T))

        Union xTs ->
            encodeList2
                (Encoding.encodeInt 11)
                (encodeMapWith encodeValue xTs)
          where
            encodeValue  Nothing  = Encoding.encodeNull
            encodeValue (Just _T) = go _T

        BoolLit b ->
            Encoding.encodeBool b

        BoolIf t l r ->
            encodeList4
                (Encoding.encodeInt 14)
                (go t)
                (go l)
                (go r)

        NaturalLit n ->
            encodeList2
                (Encoding.encodeInt 15)
                (Encoding.encodeInteger (fromIntegral n))

        NonZeroLit (NonZeroC n) ->
            encodeList2
                (Encoding.encodeInt 17)
                (Encoding.encodeInteger (fromIntegral n))

        DateTimeLit (DateTimeC n) ->
            encodeList2
                (Encoding.encodeInt 20)
                (Encoding.encodeInteger n)

        IntegerLit n ->
            encodeList2
                (Encoding.encodeInt 16)
                (Encoding.encodeInteger (fromIntegral n))

        DoubleLit (DhallDouble n64)
            | useHalf   -> Encoding.encodeFloat16 n32
            | useFloat  -> Encoding.encodeFloat n32
            | otherwise -> Encoding.encodeDouble n64
          where
            n32 = double2Float n64

            n16 = toHalf n32

            useFloat = n64 == float2Double n32

            useHalf = n64 == (float2Double $ fromHalf n16)

        RegexLit (RegexC t) ->
            encodeList2
                (Encoding.encodeInt 21)
                (Encoding.encodeBytes (encodeUtf8 t))

        RationalLit r ->
            encodeList3
                (Encoding.encodeInt 22)
                (Encoding.encodeInteger (Data.Ratio.numerator r))
                (Encoding.encodeInteger (Data.Ratio.denominator r))

        -- Fast path for the common case of an uninterpolated string
        TextLit (Chunks [] z) ->
            encodeList2
                (Encoding.encodeInt 18)
                (Encoding.encodeString z)

        TextLit (Chunks xys z) ->
            encodeListN
                (2 + 2 * length xys)
                ( Encoding.encodeInt 18
                : concatMap encodePair xys ++ [ Encoding.encodeString z ]
                )
          where
            encodePair (x, y) = [ Encoding.encodeString x, go y ]

        Assert t ->
            encodeList2
                (Encoding.encodeInt 19)
                (go t)

        Embed x ->
            encodeEmbed x

        Let a₀ b₀ ->
            encodeListN
                (2 + 3 * length as)
                ( Encoding.encodeInt 25
                : concatMap encodeBinding (toList as) ++ [ go b₁ ]
                )
          where
            MultiLet as b₁ = Syntax.multiLet a₀ b₀

            encodeBinding (Binding _ x _ mA₀ _ a) =
                [ Encoding.encodeString x
                , mA₁
                , go a
                ]
              where
                mA₁ = case mA₀ of
                    Nothing      -> Encoding.encodeNull
                    Just (_, _A) -> go _A

        Annot t _T ->
            encodeList3
                (Encoding.encodeInt 26)
                (go t)
                (go _T)

        ToMap t Nothing ->
            encodeList2
                (Encoding.encodeInt 27)
                (go t)

        ToMap t (Just _T) ->
            encodeList3
                (Encoding.encodeInt 27)
                (go t)
                (go _T)

        a@With{} ->
            go (Syntax.desugarWith a)

        Note _ b ->
            go b

    encodeOperator n l r =
        encodeList4
            (Encoding.encodeInt 3)
            (Encoding.encodeInt n)
            (go l)
            (go r)

    encodeMapWith encodeValue m =
            Encoding.encodeMapLen (fromIntegral (Dhall.Map.size m))
        <>  foldMap encodeKeyValue (Dhall.Map.toList (Dhall.Map.sort m))
      where
        encodeKeyValue (k, v) = Encoding.encodeString k <> encodeValue v

encodeList1 :: Encoding -> Encoding
encodeList1 a = Encoding.encodeListLen 1 <> a
{-# INLINE encodeList1 #-}

encodeList2 :: Encoding -> Encoding -> Encoding
encodeList2 a b = Encoding.encodeListLen 2 <> a <> b
{-# INLINE encodeList2 #-}

encodeList3 :: Encoding -> Encoding -> Encoding -> Encoding
encodeList3 a b c = Encoding.encodeListLen 3 <> a <> b <> c
{-# INLINE encodeList3 #-}

encodeList4 :: Encoding -> Encoding -> Encoding -> Encoding -> Encoding
encodeList4 a b c d = Encoding.encodeListLen 4 <> a <> b <> c <> d
{-# INLINE encodeList4 #-}

encodeListN :: Int -> [ Encoding ] -> Encoding
encodeListN len xs = Encoding.encodeListLen (fromIntegral len) <> mconcat xs
{-# INLINE encodeListN #-}

encodeList :: [ Encoding ] -> Encoding
encodeList xs = encodeListN (length xs) xs
{-# INLINE encodeList #-}

decodeImport :: Int -> Decoder s Import
decodeImport len = do
    let die message = fail ("Dhall.Binary.decodeImport: " <> message)

    tokenType₀ <- Decoding.peekTokenType

    hash <- case tokenType₀ of
        TypeNull -> do
            Decoding.decodeNull

            return Nothing

        TypeBytes -> do
            bytes <- Decoding.decodeBytes

            let (prefix, suffix) = Data.ByteString.splitAt 2 bytes

            case prefix of
                "\x12\x20" -> return ()
                _          -> die ("Unrecognized multihash prefix: " <> show prefix)
            case Dhall.Crypto.sha256DigestFromByteString suffix of
                Nothing     -> die ("Invalid sha256 digest: " <> show bytes)
                Just digest -> return (Just digest)

        _ ->
            die ("Unexpected hash token: " <> show tokenType₀)

    m <- Decoding.decodeWord

    importMode <- case m of
        0 -> return Code
        1 -> return RawText
        2 -> return Location
        _ -> die ("Unexpected code for import mode: " <> show m)

    let remote scheme = do
            tokenType₁ <- Decoding.peekTokenType

            headers <- case tokenType₁ of
                TypeNull -> do
                    Decoding.decodeNull
                    return Nothing

                _ -> do
                    headers <- decodeExpressionInternal decodeImport

                    return (Just headers)

            authority <- Decoding.decodeString

            paths <- replicateDecoder (len - 8) Decoding.decodeString

            file <- Decoding.decodeString

            tokenType₂ <- Decoding.peekTokenType

            query <- case tokenType₂ of
                TypeNull -> do
                    Decoding.decodeNull
                    return Nothing
                _ ->
                    fmap Just Decoding.decodeString

            let components = reverse paths
            let directory  = Directory {..}
            let path       = File {..}

            return (Remote (URL {..}))

    let local prefix = do
            paths <- replicateDecoder (len - 5) Decoding.decodeString

            file <- Decoding.decodeString

            let components = reverse paths
            let directory  = Directory {..}

            return (Local prefix (File {..}))

    let missing = return Missing

    let env = do
            x <- Decoding.decodeString

            return (Env x)

    n <- Decoding.decodeWord

    importType <- case n of
        0 -> remote HTTP
        1 -> remote HTTPS
        2 -> local Absolute
        3 -> local Here
        4 -> local Parent
        5 -> local Home
        6 -> env
        7 -> missing
        _ -> fail ("Unrecognized import type code: " <> show n)

    let importHashed = ImportHashed {..}

    return (Import {..})

encodeImport :: Import -> Encoding
encodeImport import_ =
    case importType of
        Remote (URL { scheme = scheme₀, .. }) ->
            encodeList
                (   prefix
                ++  [ Encoding.encodeInt scheme₁
                    , using
                    , Encoding.encodeString authority
                    ]
                ++  map Encoding.encodeString (reverse components)
                ++  [ Encoding.encodeString file ]
                ++  [ case query of
                         Nothing -> Encoding.encodeNull
                         Just q  -> Encoding.encodeString q
                    ]
                )
          where
            using = case headers of
                Nothing ->
                    Encoding.encodeNull
                Just h ->
                    encodeExpressionInternal encodeImport (Syntax.denote h)

            scheme₁ = case scheme₀ of
                HTTP  -> 0
                HTTPS -> 1

            File{..} = path

            Directory {..} = directory

        Local prefix₀ path ->
            encodeList
                (   prefix
                ++  [ Encoding.encodeInt prefix₁ ]
                ++  map Encoding.encodeString components₁
                ++  [ Encoding.encodeString file ]
                )
          where
            File{..} = path

            Directory{..} = directory

            prefix₁ = case prefix₀ of
                Absolute -> 2
                Here     -> 3
                Parent   -> 4
                Home     -> 5

            components₁ = reverse components

        Env x ->
            encodeList
                (prefix ++ [ Encoding.encodeInt 6, Encoding.encodeString x ])

        Missing ->
            encodeList (prefix ++ [ Encoding.encodeInt 7 ])
  where
    prefix = [ Encoding.encodeInt 24, h, m ]
      where
        h = case hash of
            Nothing ->
                Encoding.encodeNull

            Just digest ->
                Encoding.encodeBytes ("\x12\x20" <> Data.ByteArray.convert digest)

        m = Encoding.encodeInt (case importMode of Code -> 0; RawText -> 1; Location -> 2;)

    Import{..} = import_

    ImportHashed{..} = importHashed

decodeVoid :: Int -> Decoder s Void
decodeVoid _ = fail "Dhall.Binary.decodeVoid: Cannot decode an uninhabited type"

encodeVoid :: Void -> Encoding
encodeVoid = absurd

instance Serialise (Expr Void Void) where
    encode = encodeExpressionInternal encodeVoid

    decode = decodeExpressionInternal decodeVoid

instance Serialise (Expr Void Import) where
    encode = encodeExpressionInternal encodeImport

    decode = decodeExpressionInternal decodeImport

-- | Encode a Dhall expression as a CBOR-encoded `ByteString`
encodeExpression :: Serialise (Expr Void a) => Expr Void a -> ByteString
encodeExpression = Serialise.serialise

-- | Decode a Dhall expression from a CBOR `Term`
decodeExpression
    :: Serialise (Expr s a) => ByteString -> Either DecodingFailure (Expr s a)
decodeExpression bytes =
    case decodeWithoutVersion <|> decodeWithVersion of
        Just expression -> Right expression
        Nothing         -> Left (CBORIsNotDhall bytes)
  where
    adapt (Right ("", x)) = Just x
    adapt  _              = Nothing

    decode' = decodeWith55799Tag decode

    -- This is the behavior specified by the standard
    decodeWithoutVersion = adapt (Read.deserialiseFromBytes decode' bytes)

    -- tag to ease the migration
    decodeWithVersion = adapt (Read.deserialiseFromBytes decodeWithTag bytes)
      where
        decodeWithTag = do
            2 <- Decoding.decodeListLen

            version <- Decoding.decodeString


            -- "_" has never been a valid version string, and this ensures that
            -- we don't interpret `[ "_", 0 ]` as the expression `_` (encoded as
            -- `0`) tagged with a version string of `"_"`
            if (version == "_")
                then fail "Dhall.Binary.decodeExpression: \"_\" is not a valid version string"
                else return ()

            decode'

decodeWith55799Tag :: Decoder s a -> Decoder s a
decodeWith55799Tag decoder = do
    tokenType <- Decoding.peekTokenType

    case tokenType of
        TypeTag -> do
            w <- Decoding.decodeTag

            if w /= 55799
                then fail ("Dhall.Binary.decodeWith55799Tag: Unexpected tag: " <> show w)
                else return ()

            decoder
        _ ->
            decoder

{-| This indicates that a given CBOR-encoded `ByteString` did not correspond to
    a valid Dhall expression
-}
newtype DecodingFailure = CBORIsNotDhall ByteString
    deriving (Eq)

instance Exception DecodingFailure

_ERROR :: String
_ERROR = "\ESC[1;31mError\ESC[0m"

instance Show DecodingFailure where
    show (CBORIsNotDhall bytes) =
            _ERROR <> ": Cannot decode CBOR to Dhall\n"
        <>  "\n"
        <>  "The following bytes do not encode a valid Dhall expression\n"
        <>  "\n"
        <>  "↳ 0x" <> concatMap toHex (Data.ByteString.Lazy.unpack bytes) <> "\n"
      where
        toHex = Printf.printf "%02x "

-- | This specialized version of 'Control.Monad.replicateM' reduces
-- decoding timings by roughly 10%.
replicateDecoder :: Int -> Decoder s a -> Decoder s [a]
replicateDecoder n0 decoder = go n0
  where
    go n
      | n <= 0    = pure []
      | otherwise = do
            x <- decoder
            xs <- go (n - 1)
            pure (x:xs)
