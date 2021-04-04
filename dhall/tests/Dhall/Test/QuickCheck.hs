{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- Build without optimizations to prevent out-of-memory situations in Hydra CI
{-# OPTIONS_GHC -O0 #-}

module Dhall.Test.QuickCheck where

import Data.Either            (isRight)
import Data.Either.Validation (Validation (..))
import Data.Text              (Text)
import Data.Void              (Void)
import Dhall
    ( FromDhall (..)
    , ToDhall (..)
    , Vector
    , auto
    , embed
    , extract
    , inject
    )
import Dhall.Core
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , DateTime(..)
    , DhallDouble (..)
    , Directory (..)
    , Expr (..)
    , File (..)
    , FilePrefix (..)
    , Import (..)
    , ImportHashed (..)
    , ImportMode (..)
    , ImportType (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , NonZero(..)
    , mkNonZeroUnsafe
    , Regex(..)
    , Scheme (..)
    , URL (..)
    , Var (..)
    )
import Dhall.Map              (Map)

import Data.Functor.Identity     (Identity (..))
import Data.Proxy                (Proxy (..))
import Data.Typeable             (Typeable, typeRep)
import Dhall.Parser              (Header (..), createHeader)
import Dhall.Pretty              (CharacterSet (..))
import Dhall.Set                 (Set)
import Dhall.Src                 (Src (..))
import Dhall.Test.Format         (format)
import Dhall.TypeCheck           (TypeError, Typer)
import Generic.Random            ((:+) (..), W, Weights, (%), ConstrGen(..))
import Test.QuickCheck
    ( Arbitrary (..)
    , Gen
    , NonNegative (..)
    , Positive (..)
    , Property
    , genericShrink
    , suchThat
    , (===)
    , (==>)
    )
import Test.QuickCheck.Instances ()
import Test.Tasty                (TestTree)
import Test.Tasty.QuickCheck     (QuickCheckTests (..))
import Text.Megaparsec           (Pos, SourcePos (..))

import qualified Control.Spoon
import qualified Data.Char
import qualified Data.Foldable         as Foldable
import qualified Data.HashMap.Strict   as HashMap
import qualified Data.HashSet
import qualified Data.List
import qualified Data.Map
import qualified Data.Sequence
import qualified Data.Set
import qualified Data.SpecialValues
import qualified Data.Text             as Text
import qualified Dhall.Binary
import qualified Dhall.Context
import qualified Dhall.Core
import qualified Dhall.Diff
import qualified Dhall.Map
import qualified Dhall.Parser          as Parser
import qualified Dhall.Set
import qualified Dhall.TypeCheck
import qualified Generic.Random
import qualified Lens.Family           as Lens
import qualified Numeric.Natural       as Nat
import qualified Test.QuickCheck
import qualified Test.Tasty
import qualified Test.Tasty.QuickCheck
import qualified Text.Megaparsec       as Megaparsec
--import Debug.Trace

instance (Arbitrary a, Ord a) => Arbitrary (Set a) where
  arbitrary = Dhall.Set.fromList <$> arbitrary
  shrink = map Dhall.Set.fromList . shrink . Dhall.Set.toList

lift0 :: a -> Gen a
lift0 = pure

lift1 :: Arbitrary a => (a -> b) -> Gen b
lift1 f = f <$> arbitrary

lift2 :: (Arbitrary a, Arbitrary b) => (a -> b -> c) -> Gen c
lift2 f = f <$> arbitrary <*> arbitrary

lift3 :: (Arbitrary a, Arbitrary b, Arbitrary c) => (a -> b -> c -> d) -> Gen d
lift3 f = f <$> arbitrary <*> arbitrary <*> arbitrary

lift4
    :: (Arbitrary a, Arbitrary b, Arbitrary c, Arbitrary d)
    => (a -> b -> c -> d -> e) -> Gen e
lift4 f = f <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

lift5
    :: ( Arbitrary a
       , Arbitrary b
       , Arbitrary c
       , Arbitrary d
       , Arbitrary e
       )
    => (a -> b -> c -> d -> e -> f) -> Gen f
lift5 f =
      f <$> arbitrary
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary

lift6
    :: ( Arbitrary a
       , Arbitrary b
       , Arbitrary c
       , Arbitrary d
       , Arbitrary e
       , Arbitrary f
       )
    => (a -> b -> c -> d -> e -> f -> g) -> Gen g
lift6 f =
      f <$> arbitrary
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary
        <*> arbitrary

integer :: (Arbitrary a, Num a) => Gen a
integer =
    Test.QuickCheck.frequency
        [ (7, arbitrary)
        , (1, fmap (\x -> x + (2 ^ (64 :: Int))) arbitrary)
        , (1, fmap (\x -> x - (2 ^ (64 :: Int))) arbitrary)
        ]

whitespace :: Gen Text
whitespace = do
      let commentChar =
              Test.QuickCheck.frequency
                  [ (20, Test.QuickCheck.elements [' ' .. '\DEL'])
                  , ( 1, arbitrary)
                  ]

          noInteriorBlockComments text =
              not (Text.isInfixOf "{-" text || Text.isInfixOf "-}" text)

          commentText =
              suchThat
                  (Text.pack <$> Test.QuickCheck.listOf commentChar)
                  noInteriorBlockComments

          multiline = do
              txt <- commentText
              pure $ "{-" <> txt <> "-}"

          singleline = do
              txt <- commentText `suchThat` (not . Text.isInfixOf "\n")
              endOfLine <- Test.QuickCheck.elements ["\n", "\r\n"]
              pure $ "--" <> txt <> endOfLine

          newlines = Text.concat <$> Test.QuickCheck.listOf (pure "\n")

      comments <- do
          n <- Test.QuickCheck.choose (0, 2)
          Test.QuickCheck.vectorOf n $ Test.QuickCheck.oneof
              [ multiline
              , singleline
              , newlines
              ]

      pure $ Text.unlines comments

shrinkWhitespace :: Text -> [Text]
shrinkWhitespace "" = []
shrinkWhitespace _  = [""]

instance Arbitrary CharacterSet where
    arbitrary = Test.QuickCheck.elements [ ASCII, Unicode ]

instance Arbitrary Header where
    arbitrary = createHeader <$> whitespace

    shrink (Header text) = Header <$> shrinkWhitespace text

instance (Arbitrary v) => Arbitrary (Map Text v) where
    arbitrary = do
        n   <- Test.QuickCheck.choose (0, 2)
        kvs <- Test.QuickCheck.vectorOf n ((,) <$> label <*> arbitrary)
        -- Sorting the fields here because serialization needs them in order
        return (Dhall.Map.fromList (Data.List.sortOn fst kvs))

    shrink =
            map Dhall.Map.fromList
        .   shrink
        .   Dhall.Map.toList

instance (Arbitrary s, Arbitrary a) => Arbitrary (Binding s a) where
    arbitrary = do
        bindingSrc0 <- arbitrary

        variable <- Test.QuickCheck.oneof [ pure "_", label ]

        bindingSrc1 <- arbitrary

        annotation <- arbitrary

        bindingSrc2 <- arbitrary

        value <- arbitrary

        return Binding{..}

    shrink = genericShrink

instance (Arbitrary s, Arbitrary a) => Arbitrary (Chunks s a) where
    arbitrary = do
        n <- Test.QuickCheck.choose (0, 2)
        Chunks <$> Test.QuickCheck.vectorOf n arbitrary <*> arbitrary

    shrink = genericShrink

instance Arbitrary Const where
    arbitrary = Test.QuickCheck.oneof [ pure Type, pure Kind, pure Sort ]

    shrink = genericShrink

instance Arbitrary DhallDouble where
    arbitrary = fmap DhallDouble (Test.QuickCheck.oneof [ arbitrary, special ])
      where
        special = Test.QuickCheck.elements Data.SpecialValues.specialValues

    shrink = genericShrink

instance Arbitrary Directory where
    arbitrary = lift1 Directory

    shrink = genericShrink

instance (Arbitrary s, Arbitrary a) => Arbitrary (PreferAnnotation s a) where
    arbitrary =
        Test.QuickCheck.oneof
            [ pure PreferFromSource
            , PreferFromWith <$> arbitrary
            , pure PreferFromCompletion
            ]

instance (Arbitrary s, Arbitrary a) => Arbitrary (RecordField s a) where
    arbitrary =
        lift1 Dhall.Core.makeRecordField

    shrink = genericShrink

instance (Arbitrary s, Arbitrary a) => Arbitrary (Expr s a) where
    arbitrary =
        Test.QuickCheck.suchThat
            (Generic.Random.withBaseCase
                (Generic.Random.genericArbitraryRecG customGens weights)
                (Var <$> arbitrary)
                )
            standardizedExpression
      where
        customGens
            :: ConstrGen "Lam" 0 Text
            :+ ConstrGen "Pi" 0 Text
            :+ ConstrGen "Field" 1 Text
            :+ ConstrGen "Project" 1 (Either (Set Text) (Expr s a))
            :+ Gen Integer  -- Generates all Integer fields in Expr
            :+ Gen Text     -- Generates all Text fields in Expr
            :+ ()
        customGens =
               ConstrGen label
            :+ ConstrGen label
            :+ ConstrGen label
            :+ ConstrGen projection
            :+ integer
               -- 'Lam's and 'Pi's are encoded differently when the binding is
               -- the special string "_", so we generate some of these strings
               -- to improve test coverage for these code paths.
            :+ Test.QuickCheck.oneof [pure "_", arbitrary]
            :+ ()

        projection =
            Test.QuickCheck.oneof
                [ fmap (Left . Dhall.Set.fromList) (Test.QuickCheck.listOf label)
                , arbitrary
                ]

        -- These weights determine the frequency of constructors in the generated
        -- Expr.
        -- They will fail to compile if the constructors don't appear in the order
        -- in which they are defined in 'Expr'!
        weights :: Weights (Expr s a)
        weights =
              (7 :: W "Const")
            % (7 :: W "Var")
            % (7 :: W "Lam")
            % (7 :: W "Pi")
            % (7 :: W "App")
            % (7 :: W "Let")
            % (1 :: W "Annot")
            % (1 :: W "Bool")
            % (7 :: W "BoolLit")
            % (1 :: W "BoolAnd")
            % (1 :: W "BoolOr")
            % (1 :: W "BoolEQ")
            % (1 :: W "BoolNE")
            % (1 :: W "BoolIf")
            % (1 :: W "NonZero")
            % (7 :: W "NonZeroLit")
            % (1 :: W "NonZeroShow")
            % (1 :: W "NonZeroClamp")
            % (1 :: W "NonZeroDiv")
            % (1 :: W "NonZeroMod")
            % (1 :: W "NonZeroLog")
            % (1 :: W "NonZeroAdd")
            % (1 :: W "NonZeroMultiply")
            % (1 :: W "NonZeroToNatural")
            % (1 :: W "NonZeroToInteger")
            % (1 :: W "NonZeroParse")

            % (1 :: W "DateTime")
            % (7 :: W "DateTimeLit")
            % (1 :: W "DateTimeShow")
            % (1 :: W "DateTimeParse")
            % (1 :: W "DateTimeFromSeconds")
            % (1 :: W "DateTimeToSeconds")
            % (1 :: W "DateTimeAddYears")
            % (1 :: W "DateTimeAddMonths")
            % (1 :: W "DateTimeAddDays")
            % (1 :: W "DateTimeFromWeek")
            % (1 :: W "DateTimeToWeek")
            % (1 :: W "DateTimeToDate")
            % (1 :: W "DateTimeFromDate")
            % (1 :: W "DateTimeLastDayOfMonth")
            % (1 :: W "DateTimeGetJulianDay")
            % (1 :: W "DateTimeSetJulianDay")
            % (1 :: W "Regex")
            % (7 :: W "RegexLit")
            % (1 :: W "RegexShow")
            % (1 :: W "RegexMatch")
            % (1 :: W "RegexScan")
            % (1 :: W "RegexSplit")
            % (1 :: W "RegexReplace")
            % (1 :: W "RegexReplix")
            % (1 :: W "RegexParse")
            % (1 :: W "RegexToText")

            % (1 :: W "Rational")
            % (7 :: W "RationalLit")
            % (1 :: W "RationalShow")
            % (1 :: W "RationalFromDouble")
            % (1 :: W "RationalToDouble")
            % (1 :: W "RationalFromRational")
            % (1 :: W "RationalPercent")
            % (1 :: W "RationalParse")

            % (1 :: W "Natural")
            % (7 :: W "NaturalLit")
            % (1 :: W "NaturalFold")
            % (1 :: W "NaturalBuild")
            % (1 :: W "NaturalIsZero")
            % (1 :: W "NaturalEven")
            % (1 :: W "NaturalOdd")
            % (1 :: W "NaturalToInteger")
            % (1 :: W "NaturalShow")
            % (1 :: W "NaturalParse")
            % (1 :: W "NaturalToBits")
            % (1 :: W "NaturalSubtract")
            % (1 :: W "NaturalGcd")
            % (1 :: W "NaturalPlus")
            % (1 :: W "NaturalTimes")
            % (1 :: W "Integer")
            % (7 :: W "IntegerLit")
            % (1 :: W "IntegerAdd")
            % (1 :: W "IntegerMultiply")
            % (1 :: W "IntegerAnd")
            % (1 :: W "IntegerXor")
            % (1 :: W "IntegerClamp")
            % (1 :: W "IntegerNegate")
            % (1 :: W "IntegerShow")
            % (1 :: W "IntegerParse")
            % (1 :: W "IntegerToDouble")
            % (1 :: W "Double")
            % (7 :: W "DoubleLit")
            % (1 :: W "DoubleShow")
            % (1 :: W "DoubleParse")
            % (1 :: W "Text")
            % (1 :: W "TextLit")
            % (1 :: W "TextAppend")
            % (1 :: W "TextShow")
            % (1 :: W "TextToLower")
            % (1 :: W "TextToUpper")
            % (1 :: W "TextUnpack")
            % (1 :: W "TextPack")
            % (1 :: W "TextToList")
            % (1 :: W "TextLength")
            % (1 :: W "TextCompare")
            % (1 :: W "List")
            % (1 :: W "ListLit")
            % (1 :: W "ListAppend")
            % (1 :: W "ListBuild")
            % (1 :: W "ListFold")
            % (1 :: W "ListLength")
            % (1 :: W "ListHead")
            % (1 :: W "ListLast")
            % (1 :: W "ListIndexed")
            % (1 :: W "ListReverse")
            % (1 :: W "ListPermutations")
            % (1 :: W "ListChoose")
            % (1 :: W "ListFixed")
            % (1 :: W "ListFixedLit")
            % (1 :: W "ListFixedFromList")
            % (1 :: W "ListFixedToList")
            % (1 :: W "ListFixedHead")
            % (1 :: W "ListFixedTail")

            % (1 :: W "Sym")
            % (7 :: W "SymLit")
            % (1 :: W "SymFromText")
            % (1 :: W "SymToText")

            % (7 :: W "SZ")
            % (7 :: W "SS")
            % (7 :: W "SZLit")
            % (7 :: W "SSLit")
            % (1 :: W "SSFromNonZero")
            % (1 :: W "SSToNonZero")
            % (1 :: W "SSToNatural")
            % (1 :: W "SSAdd")
            % (1 :: W "SSSubtract")
            % (1 :: W "SSEqual")
            % (1 :: W "SSLessThan")

            % (1 :: W "Proof")
            % (7 :: W "ProofLit")
            % (1 :: W "ProofToBool")
            % (1 :: W "ProofFromBool")

            % (1 :: W "PVoid")
            % (1 :: W "PVoidUndefined")
            % (1 :: W "PVoidError")
            % (1 :: W "PVoidKindUndefined")

            % (1 :: W "Optional")
            % (7 :: W "Some")
            % (1 :: W "None")
            % (1 :: W "Record")
            % (7 :: W "RecordLit")
            % (1 :: W "Union")
            % (7 :: W "Combine")
            % (1 :: W "CombineTypes")
            % (7 :: W "Prefer")
            % (7 :: W "RecordCompletion")
            % (1 :: W "Merge")
            % (1 :: W "ToMap")
            % (7 :: W "Field")
            % (7 :: W "Project")
            % (1 :: W "Assert")
            % (1 :: W "Equivalent")
            % (1 :: W "With")
            % (0 :: W "Note")
            % (7 :: W "ImportAlt")
            % (7 :: W "Embed")
            % ()

    shrink expression = filter standardizedExpression (genericShrink expression)

standardizedExpression :: Expr s a -> Bool
standardizedExpression (ListLit  Nothing  xs) =
    not (Data.Sequence.null xs)
standardizedExpression (ListLit (Just _ ) xs) =
    Data.Sequence.null xs
standardizedExpression (Note _ _) =
    False
standardizedExpression (Combine (Just _) _ _) =
    False
standardizedExpression With{} =
    False
standardizedExpression (Prefer PreferFromCompletion _ _) =
    False
standardizedExpression (Prefer (PreferFromWith _) _ _) =
    False
-- The following three expressions are valid ASTs, but they can never be parsed,
-- because the annotation will associate with `Merge`/`ListLit`/`ToMap` with
-- higher precedence
standardizedExpression (Annot (Merge _ _ Nothing) _) =
    False
standardizedExpression (Annot (ListLit Nothing _) _) =
    False
standardizedExpression (Annot (ToMap _ Nothing) _) =
    False
standardizedExpression _ =
    True

chooseCharacter :: (Char, Char) -> Gen Char
chooseCharacter =
#if MIN_VERSION_QuickCheck(2,14,0)
    Test.QuickCheck.chooseEnum
#else
    Test.QuickCheck.choose
#endif

instance Arbitrary File where
    arbitrary = lift2 File

    shrink = genericShrink

instance Arbitrary FilePrefix where
    arbitrary = Test.QuickCheck.oneof [ pure Absolute, pure Here, pure Home ]

    shrink = genericShrink

instance Arbitrary Src where
    arbitrary = do
        lift2 Src <*> whitespace

    shrink _ = []

instance Arbitrary SourcePos where
    arbitrary = lift3 SourcePos

    shrink = genericShrink

instance Arbitrary Pos where
    arbitrary = lift1 (Megaparsec.mkPos . getPositive)

instance Arbitrary ImportType where
    arbitrary =
        Test.QuickCheck.oneof
            [ do  prefix <- arbitrary

                  let nonEmptyText =
                          fmap Text.pack (Test.QuickCheck.listOf1 arbitrary)

                  components <- Test.QuickCheck.listOf nonEmptyText

                  file <- nonEmptyText

                  let directory = Directory{ components }

                  let path = File{ file, directory }

                  return (Local prefix path)
            , lift1 Remote
            , lift1 Env
            , lift0 Missing
            ]

    shrink = genericShrink

instance Arbitrary ImportHashed where
    arbitrary =
        lift1 (ImportHashed Nothing)

    shrink (ImportHashed { importType = oldImportType, .. }) = do
        newImportType <- shrink oldImportType
        let importHashed = ImportHashed { importType = newImportType, .. }
        return importHashed

-- The standard does not yet specify how to encode `as Text`, so don't test it
-- yet
instance Arbitrary ImportMode where
    arbitrary = Test.QuickCheck.elements [ Code, RawText, Location ]

    shrink = genericShrink

instance Arbitrary Import where
    arbitrary = lift2 Import

    shrink = genericShrink

inBounds :: Integral a => (Integer -> a) -> Gen Integer -> Gen a
inBounds fi g = fmap fi (g `Test.QuickCheck.suchThat` (\x -> toInteger (fi x) == x))

instance Arbitrary NonZero where
    arbitrary = fmap (mkNonZeroUnsafe . Test.QuickCheck.getNonZero) (Test.QuickCheck.arbitrary :: (Test.QuickCheck.Gen (Test.QuickCheck.NonZero Nat.Natural)))

    shrink (NonZeroC a) = fmap (mkNonZeroUnsafe . Test.QuickCheck.getNonZero) (Test.QuickCheck.shrink (Test.QuickCheck.NonZero a :: Test.QuickCheck.NonZero Nat.Natural))

instance Arbitrary DateTime where
    arbitrary = fmap DateTimeC Test.QuickCheck.arbitrarySizedIntegral

    shrink (DateTimeC a) = fmap DateTimeC (Test.QuickCheck.shrinkIntegral a)

instance Arbitrary Regex where
{-
    arbitrary = fmap (RegexC . Text.pack)
          (Test.QuickCheck.listOf
             (Test.QuickCheck.frequency
                [ (10, Test.QuickCheck.elements (['a'..'z'] <> ['A'..'Z']))
                , (1, Test.QuickCheck.elements ".,@:;'_-^$")
                , (1, Test.QuickCheck.elements ".,@:;'_-^$")
                ]
             )
-}
    arbitrary = fmap (RegexC . Text.pack) (Test.QuickCheck.listOf Test.QuickCheck.arbitraryASCIIChar)

    shrink (RegexC a) = fmap (RegexC . Text.pack) (Test.QuickCheck.genericShrink (Text.unpack a))

instance Arbitrary Scheme where
    arbitrary = Test.QuickCheck.oneof [ pure HTTP, pure HTTPS ]

    shrink = genericShrink

instance Arbitrary URL where
    arbitrary = do
        scheme <- arbitrary

        -- TODO: the authority generator could be more precise, but it currently
        -- seems good enough.
        let validAuthorityChar =
                arbitrary `suchThat` \ch ->
                    not (Data.Char.isSpace ch) && not (Data.Char.isPunctuation ch)

        authority <- Text.pack <$> Test.QuickCheck.listOf validAuthorityChar

        let validPChar =
                Test.QuickCheck.frequency
                    [ (26, chooseCharacter ('A', 'Z'))
                    , (26, chooseCharacter ('a', 'z'))
                    , (10, chooseCharacter ('0', '9'))
                    , (17, Test.QuickCheck.elements "-._~!$&'*+;=:@")
                    ]

        let component = fmap Text.pack (Test.QuickCheck.listOf validPChar)

        components <- Test.QuickCheck.listOf component

        file <- component

        let directory = Directory{ components }

        let path = File{ file, directory }

        let validQueryCharacters =
                Test.QuickCheck.frequency
                    [ (79, validPChar)
                    , ( 2, Test.QuickCheck.elements "/?")
                    ]

        query <- Test.QuickCheck.oneof
            [ pure Nothing
            , fmap (Just . Text.pack) (Test.QuickCheck.listOf validQueryCharacters)
            ]

        headers <- arbitrary

        return URL{..}

    shrink _ = []

instance Arbitrary Var where
    arbitrary =
        Test.QuickCheck.oneof
            [ fmap (V "_") (getNonNegative <$> arbitrary)
            , fmap (\t -> V t 0) label
            , V <$> label <*> (getNonNegative <$> arbitrary)
            ]
    shrink = genericShrink

label :: Gen Text
label = fmap Text.pack (Test.QuickCheck.listOf labelCharacter)
  where
    labelCharacter =
        Test.QuickCheck.frequency
            [ (64, chooseCharacter ('\x20', '\x5F'))
            , (30, chooseCharacter ('\x61', '\x7e'))
            ]

binaryRoundtrip :: Expr () Import -> Property
binaryRoundtrip expression =
        Dhall.Binary.decodeExpression (Dhall.Binary.encodeExpression denotedExpression)
    === Right denotedExpression
  where
    denotedExpression :: Expr Void Import
    denotedExpression = denote' expression

    denote' :: Expr a Import -> Expr b Import
    denote' = Dhall.Core.denote . fmap denoteHttpHeaders

    denoteHttpHeaders import_@(Import importHashed _)
        | Remote url <- importType importHashed
        = let headers' = denote' <$> headers url
              importType' = Remote url { headers = headers' }
              importHashed' = importHashed { importType = importType' }
          in  import_ {importHashed = importHashed'}
        | otherwise = import_

everythingWellTypedNormalizes :: Expr () () -> Property
everythingWellTypedNormalizes expression =
        isRight (Dhall.TypeCheck.typeWithA filterOutEmbeds Dhall.Context.empty expression)
    ==> Test.QuickCheck.total (Dhall.Core.normalize expression :: Expr () ())
  where
    filterOutEmbeds :: Typer a
    filterOutEmbeds _ = Const Sort -- This could be any ill-typed expression.

isNormalizedIsConsistentWithNormalize :: Expr () Import -> Property
isNormalizedIsConsistentWithNormalize expression =
    case maybeProp of
        Nothing -> Test.QuickCheck.discard
        Just v -> v
  where
      maybeProp = do
          nf <- Control.Spoon.spoon (Dhall.Core.normalize expression)
          isNormalized <- Control.Spoon.spoon (Dhall.Core.isNormalized expression)
          return $ isNormalized === (nf == expression)

normalizeWithMIsConsistentWithNormalize :: Expr () Import -> Property
normalizeWithMIsConsistentWithNormalize expression =
    case Control.Spoon.spoon (nfM, nf) of
        Just (a, b) -> a === b
        Nothing -> Test.QuickCheck.discard
  where nfM = runIdentity (Dhall.Core.normalizeWithM (\_ -> Identity Nothing) expression)
        nf = Dhall.Core.normalize expression :: Expr () Import

isSameAsSelf :: Expr () Import -> Property
isSameAsSelf expression =
--  hasNoImportAndTypechecks ==> trace ("QuickCheck: isSameAsSelf " ++ Dhall.Core.dumpExpr denoted) $ Dhall.Diff.same (Dhall.Diff.diff denoted denoted)
  hasNoImportAndTypechecks ==> Dhall.Diff.same (Dhall.Diff.diff denoted denoted)
  where denoted = Dhall.Core.denote expression
        hasNoImportAndTypechecks =
          case traverse (\_ -> Left ()) expression of
            Right importlessExpression -> isRight (Dhall.TypeCheck.typeOf importlessExpression)
            Left _ -> False

inferredTypesAreNormalized :: Expr () Import -> Property
inferredTypesAreNormalized expression =
    Test.Tasty.QuickCheck.counterexample report (all Dhall.Core.isNormalized result)
  where
    report =  "Got: " ++ show result
           ++ "\nExpected: " ++ show (fmap Dhall.Core.normalize result
                                      :: Either (TypeError () Import) (Expr () Import))

    result = Dhall.TypeCheck.typeWithA filterOutEmbeds Dhall.Context.empty expression

    filterOutEmbeds :: Typer a
    filterOutEmbeds _ = Const Sort -- This could be any ill-typed expression.

normalizingAnExpressionDoesntChangeItsInferredType :: Expr () Import -> Property
normalizingAnExpressionDoesntChangeItsInferredType expression =
    case (eT0, eT1) of
        (Right t0, Right t1) -> t0 === t1
        _ -> Test.QuickCheck.discard
  where
    eT0 = typeCheck expression
    eT1 = typeCheck (Dhall.Core.normalize expression)

    typeCheck = Dhall.TypeCheck.typeWithA filterOutEmbeds Dhall.Context.empty

    filterOutEmbeds :: Typer a
    filterOutEmbeds _ = Const Sort -- This could be any ill-typed expression.

noDoubleNotes :: Expr () Import -> Property
noDoubleNotes expression =
    length
        [ ()
        | e <- Foldable.toList parsedExpression
        , Note _ (Note _ _) <- Lens.toListOf Dhall.Core.subExpressions e
        ] === 0
  where
    text = Dhall.Core.pretty expression

    parsedExpression = Parser.exprFromText "" text

embedThenExtractIsIdentity
    :: forall a. (ToDhall a, FromDhall a, Eq a, Typeable a, Arbitrary a, Show a)
    => Proxy a
    -> (String, Property, TestTree -> TestTree)
embedThenExtractIsIdentity p =
    ( "Embedding then extracting is identity for " ++ show (typeRep p)
    , Test.QuickCheck.property (prop :: a -> Bool)
    , adjustQuickCheckTests 1000
    )
  where
    prop a = case extract auto (embed inject a) of
        Success a' -> a == a'
        Failure _  -> False

idempotenceTest :: CharacterSet -> Header -> Expr Src Import -> Property
idempotenceTest characterSet header expr =
        not (any hasHttpHeaders expr)
    ==> let once = format characterSet (header, expr)
        in case Parser.exprAndHeaderFromText mempty once of
            Right (format characterSet -> twice) -> once === twice
            Left _ -> Test.QuickCheck.discard
  where
    -- Workaround for https://github.com/dhall-lang/dhall-haskell/issues/1925.
    hasHttpHeaders = \case
        Import (ImportHashed _ (Remote (URL { headers = Just _ }))) _ -> True
        _                                                             -> False

tests :: TestTree
tests =
    testProperties'
        "QuickCheck"
        [ ( "Binary serialization should round-trip"
          , Test.QuickCheck.property binaryRoundtrip
          , adjustQuickCheckTests 100000
          )
        , ( "everything well-typed should normalize"
          , Test.QuickCheck.property everythingWellTypedNormalizes
          , adjustQuickCheckTests 100000
          )
        , ( "isNormalized should be consistent with normalize"
          , Test.QuickCheck.property isNormalizedIsConsistentWithNormalize
          , adjustQuickCheckTests 100000
          )
        , ( "normalizeWithM should be consistent with normalize"
          , Test.QuickCheck.property normalizeWithMIsConsistentWithNormalize
          , adjustQuickCheckTests 100000
          )
        , ( "An expression should have no difference with itself"
          , Test.QuickCheck.property isSameAsSelf
          , adjustQuickCheckTests 100000
          )
        , ( "Inferred types should be normalized"
          , Test.QuickCheck.property inferredTypesAreNormalized
          , adjustQuickCheckTests 100000
          )
        , ( "Normalizing an expression doesn't change its inferred type"
          , Test.QuickCheck.property normalizingAnExpressionDoesntChangeItsInferredType
          , adjustQuickCheckTests 100000
          )
        , ( "Parsing an expression doesn't generated doubly-nested Note constructors"
          , Test.QuickCheck.property noDoubleNotes
          , adjustQuickCheckTests 100
          )
        , embedThenExtractIsIdentity (Proxy :: Proxy (Text))
        , embedThenExtractIsIdentity (Proxy :: Proxy [Nat.Natural])
        , embedThenExtractIsIdentity (Proxy :: Proxy (Bool, Double))
        , embedThenExtractIsIdentity (Proxy :: Proxy (Data.Sequence.Seq ()))
        , embedThenExtractIsIdentity (Proxy :: Proxy (Maybe Integer))
        , embedThenExtractIsIdentity (Proxy :: Proxy (Data.Set.Set Nat.Natural))
        , embedThenExtractIsIdentity (Proxy :: Proxy (Data.HashSet.HashSet Text))
        , embedThenExtractIsIdentity (Proxy :: Proxy (Vector Double))
        , embedThenExtractIsIdentity (Proxy :: Proxy (Data.Map.Map Double Bool))
        , embedThenExtractIsIdentity (Proxy :: Proxy (HashMap.HashMap Double Bool))
{-
        , ( "Formatting should be idempotent"
          , Test.QuickCheck.property idempotenceTest
          , adjustQuickCheckTests 10000
          )
-}
        ]

adjustQuickCheckMaxRatio :: Int -> TestTree -> TestTree
adjustQuickCheckMaxRatio maxSize =
    Test.Tasty.adjustOption (max $ Test.Tasty.QuickCheck.QuickCheckMaxRatio maxSize)

adjustQuickCheckTests :: Int -> TestTree -> TestTree
adjustQuickCheckTests nTests =
    -- Using adjustOption instead of withMaxSuccess allows us to override the number of tests
    -- with the --quickcheck-tests CLI option.
    Test.Tasty.adjustOption (max $ QuickCheckTests nTests)

testProperties' :: String -> [(String, Property, TestTree -> TestTree)] -> TestTree
testProperties' name = Test.Tasty.testGroup name . map f
  where
    f (n, p, adjust) = adjust (Test.Tasty.QuickCheck.testProperty n p)
