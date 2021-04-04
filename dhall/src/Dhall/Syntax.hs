{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveLift         #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedLists    #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UnicodeSyntax      #-}

{-| This module contains the core syntax types and optics for them.

'reservedIdentifiers', 'denote' and friends are included because they are
involved in a dependency circle with "Dhall.Pretty.Internal".
-}

module Dhall.Syntax (
    -- * 'Expr'
      Const(..)
    , Var(..)
    , Binding(..)
    , makeBinding
    , Chunks(..)
    , DhallDouble(..)
    , PreferAnnotation(..)
    , Expr(..)
    , RecordField(..)
    , makeRecordField

    -- ** 'Let'-blocks
    , MultiLet(..)
    , multiLet
    , wrapInLets

    -- ** Optics
    , subExpressions
    , unsafeSubExpressions
    , chunkExprs
    , bindingExprs
    , recordFieldExprs

    -- ** Handling 'Note's
    , denote
    , renote
    , shallowDenote

    -- * 'Import'
    , Directory(..)
    , File(..)
    , FilePrefix(..)
    , Import(..)
    , ImportHashed(..)
    , ImportMode(..)
    , ImportType(..)
    , URL(..)
    , Scheme(..)
    , pathCharacter

    -- * Reserved identifiers
    , reservedIdentifiers
    , reservedKeywords

    -- * `Text` manipulation
    , toDoubleQuoted
    , longestSharedWhitespacePrefix
    , linesLiteral
    , unlinesLiteral

    -- * Desugaring
    , desugarWith

    -- * Utilities
    , internalError
    -- * nonzero type
    , NonZero(..)
    , mkNonZero
    , mkNonZeroUnsafe
    , pattern NonZeroP

    -- * datetime type
    , DateTime(..)
    , dateTimeToUtc
    , utcToDateTime

    -- * regex type
    , Regex(..)
    , compileRegex
    , compileRegexUnsafe

    -- * rational
    , showDhallRational

    , makeSSExpr
    ) where

import Control.DeepSeq            (NFData)
import Data.Bifunctor             (Bifunctor (..))
import Data.Bits                  (xor)
import Data.Data                  (Data)
import Data.Foldable
import Data.HashSet               (HashSet)
import Data.List.NonEmpty         (NonEmpty (..))
import Data.Sequence              (Seq)
import Data.String                (IsString (..))
import Data.Text                  (Text)
import Data.Text.Prettyprint.Doc  (Doc, Pretty)
import Data.Traversable           ()
import qualified Data.Time
import qualified Data.Time.Clock.POSIX
import Data.Void                  (Void)
import Dhall.Map                  (Map)
import {-# SOURCE #-} Dhall.Pretty.Internal
import Dhall.Set                  (Set)
import Dhall.Src                  (Src (..))
import GHC.Generics               (Generic)
import Instances.TH.Lift          ()
import Language.Haskell.TH.Syntax (Lift)
import Numeric.Natural            (Natural)
import Unsafe.Coerce              (unsafeCoerce)

import qualified Control.Monad
import qualified Data.HashSet
import qualified Data.List.NonEmpty        as NonEmpty
import qualified Data.Ratio
import qualified Data.Text
import qualified Data.Text.Encoding
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Dhall.Crypto
import qualified Dhall.Optics              as Optics
import qualified Lens.Family               as Lens
import qualified Network.URI               as URI
import Data.Maybe (fromMaybe)
import qualified Data.Aeson

import qualified Text.Regex.PCRE.Heavy as RH
-- $setup
-- >>> import Dhall.Binary () -- For the orphan instance for `Serialise (Expr Void Import)`

{-| Constants for a pure type system

    The axioms are:

> ⊦ Type : Kind
> ⊦ Kind : Sort

    ... and the valid rule pairs are:

> ⊦ Type ↝ Type : Type  -- Functions from terms to terms (ordinary functions)
> ⊦ Kind ↝ Type : Type  -- Functions from types to terms (type-polymorphic functions)
> ⊦ Sort ↝ Type : Type  -- Functions from kinds to terms
> ⊦ Kind ↝ Kind : Kind  -- Functions from types to types (type-level functions)
> ⊦ Sort ↝ Kind : Sort  -- Functions from kinds to types (kind-polymorphic functions)
> ⊦ Sort ↝ Sort : Sort  -- Functions from kinds to kinds (kind-level functions)

    Note that Dhall does not support functions from terms to types and therefore
    Dhall is not a dependently typed language
-}
data Const = Type | Kind | Sort
    deriving (Show, Eq, Ord, Data, Bounded, Enum, Generic, Lift, NFData)

instance Pretty Const where
    pretty = Pretty.unAnnotate . prettyConst

{-| Label for a bound variable

    The `Text` field is the variable's name (i.e. \"@x@\").

    The `Int` field disambiguates variables with the same name if there are
    multiple bound variables of the same name in scope.  Zero refers to the
    nearest bound variable and the index increases by one for each bound
    variable of the same name going outward.  The following diagram may help:

>                               ┌──refers to──┐
>                               │             │
>                               v             │
> λ(x : Type) → λ(y : Type) → λ(x : Type) → x@0
>
> ┌─────────────────refers to─────────────────┐
> │                                           │
> v                                           │
> λ(x : Type) → λ(y : Type) → λ(x : Type) → x@1

    This `Int` behaves like a De Bruijn index in the special case where all
    variables have the same name.

    You can optionally omit the index if it is @0@:

>                               ┌─refers to─┐
>                               │           │
>                               v           │
> λ(x : Type) → λ(y : Type) → λ(x : Type) → x

    Zero indices are omitted when pretty-printing `Var`s and non-zero indices
    appear as a numeric suffix.
-}
data Var = V Text !Int
    deriving (Data, Generic, Eq, Ord, Show, Lift, NFData)

instance IsString Var where
    fromString str = V (fromString str) 0

instance Pretty Var where
    pretty = Pretty.unAnnotate . prettyVar

newtype NonZero = NonZeroC { unNonZero :: Natural }
  deriving stock (Show,Eq,Data,Generic,Lift)
  deriving (NFData,Ord) via Natural

{-# COMPLETE NonZeroP #-}
pattern NonZeroP :: Natural -> NonZero
pattern NonZeroP a <- NonZeroC a

mkNonZero :: Natural -> Maybe NonZero
mkNonZero n | n == 0 = Nothing
       | otherwise = Just (NonZeroC n)

mkNonZeroUnsafe :: Natural -> NonZero
mkNonZeroUnsafe = fromMaybe (error "invalid nonzero") . mkNonZero

instance Pretty NonZero where
    pretty (NonZeroC n) = Pretty.pretty '!' <> Pretty.pretty n

newtype DateTime = DateTimeC { unDateTime :: Integer }
  deriving stock (Show,Eq,Data,Generic,Lift)
  deriving (NFData,Ord,Num) via Integer

dateTimeToUtc :: DateTime -> Data.Time.UTCTime
dateTimeToUtc (DateTimeC n) = Data.Time.Clock.POSIX.posixSecondsToUTCTime (fromIntegral n)

utcToDateTime :: Data.Time.UTCTime -> DateTime
utcToDateTime u = DateTimeC (round (Data.Time.Clock.POSIX.utcTimeToPOSIXSeconds u))

instance Pretty DateTime where
    pretty n =
      let x = dateTimeToUtc n
          y = Data.Time.formatTime Data.Time.defaultTimeLocale "%FT%T" x
      in Pretty.pretty '^' <> Pretty.pretty y

newtype Regex = RegexC { unRegex :: Text }
  deriving stock (Show,Eq,Data,Generic,Lift)
  deriving (NFData,Ord,Data.Aeson.ToJSON,Data.Aeson.FromJSON) via Text

instance Pretty Regex where
    pretty (RegexC y) =
      Pretty.pretty '~' <> Pretty.pretty '"' <> Pretty.pretty y <> Pretty.pretty '"'

compileRegex :: Text -> Either String RH.Regex
compileRegex m
  | Data.Text.null m = Left "empty regex is not allowed"
  | otherwise = RH.compileM (Data.Text.Encoding.encodeUtf8 m) []

compileRegexUnsafe :: Text -> RH.Regex
compileRegexUnsafe m =
  case compileRegex m of
    Left e -> error $ "should not happen: compiled before but not now or programmer error?: msg[" ++ e ++ "]"
    Right r -> r

showDhallRational :: Rational -> Text
showDhallRational r =
  let n = Data.Ratio.numerator r
      d = Data.Ratio.denominator r
  in Data.Text.pack ((if n>=0 then "+" else "") <> show n <> " % !" <> show d)


{- | Record the binding part of a @let@ expression.

For example,

> let {- A -} x {- B -} : {- C -} Bool = {- D -} True in x

will be instantiated as follows:

* @bindingSrc0@ corresponds to the @A@ comment.
* @variable@ is @"x"@
* @bindingSrc1@ corresponds to the @B@ comment.
* @annotation@ is 'Just' a pair, corresponding to the @C@ comment and @Bool@.
* @bindingSrc2@ corresponds to the @D@ comment.
* @value@ corresponds to @True@.
-}
data Binding s a = Binding
    { bindingSrc0 :: Maybe s
    , variable    :: Text
    , bindingSrc1 :: Maybe s
    , annotation  :: Maybe (Maybe s, Expr s a)
    , bindingSrc2 :: Maybe s
    , value       :: Expr s a
    } deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

instance Bifunctor Binding where
    first k (Binding src0 a src1 b src2 c) =
        Binding (fmap k src0) a (fmap k src1) (fmap adapt0 b) (fmap k src2) (first k c)
      where
        adapt0 (src3, d) = (fmap k src3, first k d)

    second = fmap

{-| Construct a 'Binding' with no source information and no type annotation.
-}
makeBinding :: Text -> Expr s a -> Binding s a
makeBinding name = Binding Nothing name Nothing Nothing Nothing

-- | This wrapper around 'Prelude.Double' exists for its 'Eq' instance which is
-- defined via the binary encoding of Dhall @Double@s.
newtype DhallDouble = DhallDouble { getDhallDouble :: Double }
    deriving (Show, Data, Lift, NFData, Generic)

-- | This instance satisfies all the customary 'Eq' laws except substitutivity.
--
-- In particular:
--
-- >>> nan = DhallDouble (0/0)
-- >>> nan == nan
-- True
--
-- This instance is also consistent with with the binary encoding of Dhall @Double@s:
--
-- >>> toBytes n = Dhall.Binary.encodeExpression (DoubleLit n :: Expr Void Import)
--
-- prop> \a b -> (a == b) == (toBytes a == toBytes b)
instance Eq DhallDouble where
    DhallDouble a == DhallDouble b
        | isNaN a && isNaN b                      = True
        | isNegativeZero a `xor` isNegativeZero b = False
        | otherwise                               = a == b

-- | This instance relies on the 'Eq' instance for 'DhallDouble' but cannot
-- satisfy the customary 'Ord' laws when @NaN@ is involved.
instance Ord DhallDouble where
    compare a@(DhallDouble a') b@(DhallDouble b') =
        if a == b
            then EQ
            else compare a' b'

-- | The body of an interpolated @Text@ literal
data Chunks s a = Chunks [(Text, Expr s a)] Text
    deriving (Functor, Foldable, Generic, Traversable, Show, Eq, Ord, Data, Lift, NFData)

instance Semigroup (Chunks s a) where
    Chunks xysL zL <> Chunks         []    zR =
        Chunks xysL (zL <> zR)
    Chunks xysL zL <> Chunks ((x, y):xysR) zR =
        Chunks (xysL ++ (zL <> x, y):xysR) zR

instance Monoid (Chunks s a) where
    mempty = Chunks [] mempty

instance IsString (Chunks s a) where
    fromString str = Chunks [] (fromString str)

-- | Used to record the origin of a @//@ operator (i.e. from source code or a
-- product of desugaring)
data PreferAnnotation s a
    = PreferFromSource
    | PreferFromWith (Expr s a)
      -- ^ Stores the original @with@ expression
    | PreferFromCompletion
    deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

instance Bifunctor PreferAnnotation where
    first _  PreferFromSource      = PreferFromSource
    first f (PreferFromWith e    ) = PreferFromWith (first f e)
    first _  PreferFromCompletion  = PreferFromCompletion

    second = fmap

{-| Record the field of a record-type and record-literal expression.
    The reason why we use the same ADT for both of them is because they store
    the same information.

For example,

> { {- A -} x : T }

... or

> { {- A -} x = T }

will be instantiated as follows:

* @recordFieldSrc@ corresponds to the @A@ comment.
* @field@ is @"T"@

Although the @A@ comment isn't annotating the @"T"@ Record Field,
this is the best place to keep these comments
-}
data RecordField s a = RecordField
    { recordFieldSrc  :: Maybe s
    , recordFieldValue :: Expr s a
    } deriving (Data, Eq, Foldable, Functor, Generic, Lift, NFData, Ord, Show, Traversable)

-- | Construct a 'RecordField' with no src information
makeRecordField :: Expr s a -> RecordField s a
makeRecordField = RecordField Nothing


instance Bifunctor RecordField where
    first k (RecordField s0 value) =
        RecordField (k <$> s0) (first k value)
    second = fmap

{-| Syntax tree for expressions

    The @s@ type parameter is used to track the presence or absence of `Src`
    spans:

    * If @s = `Src`@ then the code may contains `Src` spans (either in a `Noted`
      constructor or inline within another constructor, like `Let`)
    * If @s = `Void`@ then the code has no `Src` spans

    The @a@ type parameter is used to track the presence or absence of imports

    * If @a = `Import`@ then the code may contain unresolved `Import`s
    * If @a = `Void`@ then the code has no `Import`s
-}
data Expr s a
    -- | > Const c                                  ~  c
    = Const Const
    -- | > Var (V x 0)                              ~  x
    --   > Var (V x n)                              ~  x@n
    | Var Var
    -- | > Lam x     A b                            ~  λ(x : A) -> b
    | Lam Text (Expr s a) (Expr s a)
    -- | > Pi "_" A B                               ~        A  -> B
    --   > Pi x   A B                               ~  ∀(x : A) -> B
    | Pi  Text (Expr s a) (Expr s a)
    -- | > App f a                                  ~  f a
    | App (Expr s a) (Expr s a)
    -- | > Let (Binding _ x _  Nothing  _ r) e      ~  let x     = r in e
    --   > Let (Binding _ x _ (Just t ) _ r) e      ~  let x : t = r in e
    --
    -- The difference between
    --
    -- > let x = a    let y = b in e
    --
    -- and
    --
    -- > let x = a in let y = b in e
    --
    -- is only an additional 'Note' around @'Let' "y" …@ in the second
    -- example.
    --
    -- See 'MultiLet' for a representation of let-blocks that mirrors the
    -- source code more closely.
    | Let (Binding s a) (Expr s a)
    -- | > Annot x t                                ~  x : t
    | Annot (Expr s a) (Expr s a)
    -- | > Bool                                     ~  Bool
    | Bool
    -- | > BoolLit b                                ~  b
    | BoolLit Bool
    -- | > BoolAnd x y                              ~  x && y
    | BoolAnd (Expr s a) (Expr s a)
    -- | > BoolOr  x y                              ~  x || y
    | BoolOr  (Expr s a) (Expr s a)
    -- | > BoolEQ  x y                              ~  x == y
    | BoolEQ  (Expr s a) (Expr s a)
    -- | > BoolNE  x y                              ~  x != y
    | BoolNE  (Expr s a) (Expr s a)
    -- | > BoolIf x y z                             ~  if x then y else z
    | BoolIf (Expr s a) (Expr s a) (Expr s a)
    -- | > NonZero                                  ~  NonZero
    | NonZero
    -- | > NonZeroLit n                             ~  n
    | NonZeroLit NonZero
    -- | > NonZeroShow                              ~  NonZero/show
    | NonZeroShow
    -- | > NonZeroClamp                             ~  NonZero/clamp
    | NonZeroClamp
    -- | > NonZeroDiv                               ~  NonZero/div
    | NonZeroDiv
    -- | > NonZeroMod                               ~  NonZero/mod
    | NonZeroMod
    -- | > NonZeroLog                               ~  NonZero/log
    | NonZeroLog
    -- | > NonZeroAdd                               ~  NonZero/add
    | NonZeroAdd
    -- | > NonZeroMultiply                          ~  NonZero/multiply
    | NonZeroMultiply
    -- | > NonZeroToNatural                         ~  NonZero/toNatural
    | NonZeroToNatural
    -- | > NonZeroToInteger                         ~  NonZero/toInteger
    | NonZeroToInteger
    -- | > NonZeroParse                             ~  NonZero/parse
    | NonZeroParse

    -- | > DateTime                                 ~  DateTime
    | DateTime
    -- | > DateTimeLit n                            ~  n
    | DateTimeLit DateTime
    -- | > DateTimeShow                             ~  DateTime/show
    | DateTimeShow
    -- | > DateTimeParse                            ~  DateTime/parse
    | DateTimeParse
    -- | > DateTimeFromSeconds                      ~  DateTime/fromSeconds
    | DateTimeFromSeconds
    -- | > DateTimeToSeconds                        ~  DateTime/toSeconds
    | DateTimeToSeconds

    -- | > DateTimeAddYears                         ~  DateTime/addYears
    | DateTimeAddYears
    -- | > DateTimeAddMonths                        ~  DateTime/addMonths
    | DateTimeAddMonths
    -- | > DateTimeAddDays                          ~  DateTime/addDays
    | DateTimeAddDays
    -- | > DateTimeFromWeek                         ~  DateTime/fromWeek
    | DateTimeFromWeek
    -- | > DateTimeToWeek                           ~  DateTime/toWeek
    | DateTimeToWeek
    -- | > DateTimeToDate                           ~  DateTime/toDate
    | DateTimeToDate
    -- | > DateTimeFromDate                         ~  DateTime/FromDate
    | DateTimeFromDate
    -- | > DateTimeLastDayOfMonth                   ~  DateTime/lastDayOfMonth
    | DateTimeLastDayOfMonth

    -- | > DateTimeGetJulianDay                     ~  DateTime/getJulianDay
    | DateTimeGetJulianDay
    -- | > DateTimeSetJulianDay                     ~  DateTime/setJulianDay
    | DateTimeSetJulianDay

    -- | > Regex                                    ~  Regex
    | Regex
    -- | > RegexLit n                               ~  n
    | RegexLit Regex
    -- | > RegexShow                                ~  Regex/show
    | RegexShow
    -- | > RegexMatch                               ~  Regex/match
    | RegexMatch
    -- | > RegexScan                                ~  Regex/scan
    | RegexScan
    -- | > RegexSplit                               ~  Regex/split
    | RegexSplit
    -- | > RegexReplace                             ~  Regex/replace
    | RegexReplace
    -- | > RegexReplix                              ~  Regex/replix
    | RegexReplix
    -- | > RegexParse                               ~  Regex/parse
    | RegexParse
    -- | > RegexToText                              ~  Regex/toText
    | RegexToText


    -- | > Rational                                 ~  Rational
    | Rational
    -- | > RationalLit n                            ~  n
    | RationalLit Rational
    -- | > RationalShow                             ~  Rational/show
    | RationalShow
    -- | > RationalFromDouble                       ~  Rational/fromDouble
    | RationalFromDouble
    -- | > RationalToDouble                         ~  Rational/toDouble
    | RationalToDouble
    -- | > RationalFromRational                     ~  Rational/fromRational
    | RationalFromRational
    -- | > RationalPercent x y                      ~  x % y
    | RationalPercent (Expr s a) (Expr s a)
    -- | > RationalParse                            ~  Rational/parse
    | RationalParse


    -- | > Natural                                  ~  Natural
    | Natural
    -- | > NaturalLit n                             ~  n
    | NaturalLit Natural
    -- | > NaturalFold                              ~  Natural/fold
    | NaturalFold
    -- | > NaturalBuild                             ~  Natural/build
    | NaturalBuild
    -- | > NaturalIsZero                            ~  Natural/isZero
    | NaturalIsZero
    -- | > NaturalEven                              ~  Natural/even
    | NaturalEven
    -- | > NaturalOdd                               ~  Natural/odd
    | NaturalOdd
    -- | > NaturalToInteger                         ~  Natural/toInteger
    | NaturalToInteger
    -- | > NaturalShow                              ~  Natural/show
    | NaturalShow
    -- | > NaturalParse                             ~  Natural/parse
    | NaturalParse
    -- | > NaturalToBits                            ~  Natural/toBits
    | NaturalToBits
    -- | > NaturalSubtract                          ~  Natural/subtract
    | NaturalSubtract
    -- | > NaturalGcd                               ~  Natural/gcd
    | NaturalGcd
    -- | > NaturalPlus x y                          ~  x + y
    | NaturalPlus (Expr s a) (Expr s a)
    -- | > NaturalTimes x y                         ~  x * y
    | NaturalTimes (Expr s a) (Expr s a)
    -- | > Integer                                  ~  Integer
    | Integer
    -- | > IntegerLit n                             ~  ±n
    | IntegerLit Integer
    -- | IntegerAdd                                 ~  Integer/add
    | IntegerAdd
    -- | IntegerMultiply                            ~  Integer/multiply
    | IntegerMultiply
    -- | IntegerAdd                                 ~  Integer/and
    | IntegerAnd
    -- | IntegerXor                                 ~  Integer/xor
    | IntegerXor
    -- | IntegerClamp                               ~  Integer/clamp
    | IntegerClamp
    -- | > IntegerNegate                              ~  Integer/negate
    | IntegerNegate
    -- | > IntegerShow                              ~  Integer/show
    | IntegerShow
    -- | > IntegerParse                             ~  Integer/parse
    | IntegerParse
    -- | > IntegerToDouble                          ~  Integer/toDouble
    | IntegerToDouble
    -- | > Double                                   ~  Double
    | Double
    -- | > DoubleLit n                              ~  n
    | DoubleLit DhallDouble
    -- | > DoubleShow                               ~  Double/show
    | DoubleShow
    -- | > DoubleParse                              ~  Double/parse
    | DoubleParse
    -- | > Text                                     ~  Text
    | Text
    -- | > TextLit (Chunks [(t1, e1), (t2, e2)] t3) ~  "t1${e1}t2${e2}t3"
    | TextLit (Chunks s a)
    -- | > TextAppend x y                           ~  x ++ y
    | TextAppend (Expr s a) (Expr s a)
    -- | > TextShow                                 ~  Text/show
    | TextShow
    -- | > TextToLower                              ~  Text/toLower
    | TextToLower
    -- | > TextToUpper                              ~  Text/toUpper
    | TextToUpper
    -- | > TextUnpack                               ~  Text/unpack
    | TextUnpack
    -- | > TextPack                                 ~  Text/pack
    | TextPack
    -- | > TexttoList                               ~  Text/toList
    | TextToList
    -- | > Textlength                               ~  Text/length
    | TextLength
    -- | > TextCompare                              ~  Text/compare
    | TextCompare
    -- | > List                                     ~  List
    | List
    -- | > ListLit (Just t ) []                     ~  [] : t
    --   > ListLit  Nothing  [x, y, z]              ~  [x, y, z]
    --
    --   Invariant: A non-empty list literal is always represented as
    --   @ListLit Nothing xs@.
    --
    --   When an annotated, non-empty list literal is parsed, it is represented
    --   as
    --
    --   > Annot (ListLit Nothing [x, y, z]) t      ~ [x, y, z] : t

    -- Eventually we should have separate constructors for empty and non-empty
    -- list literals. For now it's easier to check the invariant in @infer@.
    -- See https://github.com/dhall-lang/dhall-haskell/issues/1359#issuecomment-537087234.
    | ListLit (Maybe (Expr s a)) (Seq (Expr s a))
    -- | > ListAppend x y                           ~  x # y
    | ListAppend (Expr s a) (Expr s a)
    -- | > ListBuild                                ~  List/build
    | ListBuild
    -- | > ListFold                                 ~  List/fold
    | ListFold
    -- | > ListLength                               ~  List/length
    | ListLength
    -- | > ListHead                                 ~  List/head
    | ListHead
    -- | > ListLast                                 ~  List/last
    | ListLast
    -- | > ListIndexed                              ~  List/indexed
    | ListIndexed
    -- | > ListReverse                              ~  List/reverse
    | ListReverse
    -- | > ListPermutations                         ~  List/permutations
    | ListPermutations
    -- | > ListChoose                               ~  List/choose
    | ListChoose

    -- | > ListFixed                                ~  ListFixed
    | ListFixed
    -- | > ListFixedLit                             ~  ListFixedLit
    | ListFixedLit (Expr s a) (Seq (Expr s a))

    -- | > ListFixedFromList                        ~  ListFixed/fromList
    | ListFixedFromList
    -- | > ListFixedToList                          ~  ListFixed/toList
    | ListFixedToList
    -- | > ListFixedHead                            ~  ListFixed/head
    | ListFixedHead
    -- | > ListFixedTail                            ~  ListFixed/tail
    | ListFixedTail

    -- | > Sym                                       ~  Sym
    | Sym Text
    -- | > SymLit                                    ~  SymLit
    | SymLit Text

    -- | > SymFromText                            ~  Sym/fromText
    | SymFromText
    -- | > SymToText                              ~  Sym/toText
    | SymToText

    -- | > SZ                                       ~  SZ
    | SZ
    -- | > SS                                       ~  SS
    | SS
    -- | > SZLit                                    ~  SZLit
    | SZLit
    -- | > SSLit                                    ~  SSLit
    | SSLit (Expr s a)
    -- | > SSFromNonZero                            ~  SS/fromNonZero
    | SSFromNonZero
    -- | > SSToNonZero                              ~  SS/toNonZero
    | SSToNonZero
    -- | > SSToNatural                              ~  SS/toNatural
    | SSToNatural
    -- | > SSAdd                                    ~  SS/add
    | SSAdd
    -- | > SSSubtract                               ~  SS/subtract
    | SSSubtract
    -- | > SSEqual                                  ~  SS/equal
    | SSEqual
    -- | > SSLessThan                               ~  SS/lessThan
    | SSLessThan

    -- | > Proof                                    ~  Proof
    | Proof
    -- | > ProofLit                                 ~  ProofLit
    | ProofLit
    -- | > ProofToBool                              ~  Proof/toBool
    | ProofToBool
    -- | > ProofFromBool                            ~  Proof/fromBool
    | ProofFromBool

    -- | > PVoid                                    ~  PVoid
    | PVoid
    -- | > PVoidUndefined                           ~  PVoid/undefined
    | PVoidUndefined
    -- | > PVoidError                               ~  PVoid/error
    | PVoidError
    -- | > PVoidKindUndefined                       ~  PVoid/kindUndefined
    | PVoidKindUndefined

    -- | > Optional                                 ~  Optional
    | Optional
    -- | > Some e                                   ~  Some e
    | Some (Expr s a)
    -- | > None                                     ~  None
    | None
    -- | > Record [ (k1, RecordField _ t1)          ~  { k1 : t1, k2 : t1 }
    --   >        , (k2, RecordField _ t2)
    --   >        ]
    | Record    (Map Text (RecordField s a))
    -- | > RecordLit [ (k1, RecordField _ v1)       ~  { k1 = v1, k2 = v2 }
    --   >           , (k2, RecordField _ v2)
    --   >           ]
    | RecordLit (Map Text (RecordField s a))
    -- | > Union        [(k1, Just t1), (k2, Nothing)] ~  < k1 : t1 | k2 >
    | Union     (Map Text (Maybe (Expr s a)))
    -- | > Combine Nothing x y                      ~  x ∧ y
    --
    -- The first field is a `Just` when the `Combine` operator is introduced
    -- as a result of desugaring duplicate record fields:
    --
    --   > RecordLit [ ( k                          ~ { k = x, k = y }
    --   >           , RecordField
    --   >              _
    --   >              (Combine (Just k) x y)
    --   >            )]
    | Combine (Maybe Text) (Expr s a) (Expr s a)
    -- | > CombineTypes x y                         ~  x ⩓ y
    | CombineTypes (Expr s a) (Expr s a)
    -- | > Prefer False x y                         ~  x ⫽ y
    --
    -- The first field is a `True` when the `Prefer` operator is introduced as a
    -- result of desugaring a @with@ expression
    | Prefer (PreferAnnotation s a) (Expr s a) (Expr s a)
    -- | > RecordCompletion x y                     ~  x::y
    | RecordCompletion (Expr s a) (Expr s a)
    -- | > Merge x y (Just t )                      ~  merge x y : t
    --   > Merge x y  Nothing                       ~  merge x y
    | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
    -- | > ToMap x (Just t)                         ~  toMap x : t
    --   > ToMap x  Nothing                         ~  toMap x
    | ToMap (Expr s a) (Maybe (Expr s a))
    -- | > Field e x                                ~  e.x
    | Field (Expr s a) Text
    -- | > Project e (Left xs)                      ~  e.{ xs }
    --   > Project e (Right t)                      ~  e.(t)
    | Project (Expr s a) (Either (Set Text) (Expr s a))
    -- | > Assert e                                 ~  assert : e
    | Assert (Expr s a)
    -- | > Equivalent x y                           ~  x ≡ y
    | Equivalent (Expr s a) (Expr s a)
    -- | > With x y e                               ~  x with y = e
    | With (Expr s a) (NonEmpty Text) (Expr s a)
    -- | > Note s x                                 ~  e
    | Note s (Expr s a)
    -- | > ImportAlt                                ~  e1 ? e2
    | ImportAlt (Expr s a) (Expr s a)
    -- | > Embed import                             ~  import
    | Embed a
    deriving (Foldable, Generic, Traversable, Show, Data, Lift, NFData)
-- NB: If you add a constructor to Expr, please also update the Arbitrary
-- instance in Dhall.Test.QuickCheck.

-- | This instance encodes what the Dhall standard calls an \"exact match\"
-- between two expressions.
--
-- Note that
--
-- >>> nan = DhallDouble (0/0)
-- >>> DoubleLit nan == DoubleLit nan
-- True
deriving instance (Eq s, Eq a) => Eq (Expr s a)

-- | Note that this 'Ord' instance inherits `DhallDouble`'s defects.
deriving instance (Ord s, Ord a) => Ord (Expr s a)

-- This instance is hand-written due to the fact that deriving
-- it does not give us an INLINABLE pragma. We annotate this fmap
-- implementation with this pragma below to allow GHC to, possibly,
-- inline the implementation for performance improvements.
instance Functor (Expr s) where
  fmap f (Embed a) = Embed (f a)
  fmap f (Let b e2) = Let (fmap f b) (fmap f e2)

  fmap _ NonZero = NonZero
  fmap _ (NonZeroLit n) = NonZeroLit n
  fmap _ NonZeroShow = NonZeroShow
  fmap _ NonZeroClamp = NonZeroClamp
  fmap _ NonZeroDiv = NonZeroDiv
  fmap _ NonZeroMod = NonZeroMod
  fmap _ NonZeroLog = NonZeroLog
  fmap _ NonZeroAdd = NonZeroAdd
  fmap _ NonZeroMultiply = NonZeroMultiply
  fmap _ NonZeroToNatural = NonZeroToNatural
  fmap _ NonZeroToInteger = NonZeroToInteger
  fmap _ NonZeroParse = NonZeroParse

  fmap _ DateTime = DateTime
  fmap _ (DateTimeLit n) = DateTimeLit n
  fmap _ DateTimeShow = DateTimeShow
  fmap _ DateTimeParse = DateTimeParse
  fmap _ DateTimeFromSeconds = DateTimeFromSeconds
  fmap _ DateTimeToSeconds = DateTimeToSeconds

  fmap _ DateTimeAddYears = DateTimeAddYears
  fmap _ DateTimeAddMonths = DateTimeAddMonths
  fmap _ DateTimeAddDays = DateTimeAddDays
  fmap _ DateTimeFromWeek = DateTimeFromWeek
  fmap _ DateTimeToWeek = DateTimeToWeek
  fmap _ DateTimeToDate = DateTimeToDate
  fmap _ DateTimeFromDate = DateTimeFromDate
  fmap _ DateTimeLastDayOfMonth = DateTimeLastDayOfMonth

  fmap _ DateTimeGetJulianDay = DateTimeGetJulianDay
  fmap _ DateTimeSetJulianDay = DateTimeSetJulianDay


  fmap _ Regex = Regex
  fmap _ (RegexLit cs) = RegexLit cs
  fmap _ RegexShow = RegexShow
  fmap _ RegexMatch = RegexMatch
  fmap _ RegexScan = RegexScan
  fmap _ RegexSplit = RegexSplit
  fmap _ RegexReplace = RegexReplace
  fmap _ RegexReplix = RegexReplix
  fmap _ RegexParse = RegexParse
  fmap _ RegexToText = RegexToText

  fmap _ Rational = Rational
  fmap _ (RationalLit cs) = RationalLit cs
  fmap _ RationalShow = RationalShow
  fmap _ RationalFromDouble = RationalFromDouble
  fmap _ RationalToDouble = RationalToDouble
  fmap _ RationalFromRational = RationalFromRational
  fmap f (RationalPercent e1 e2) = RationalPercent (fmap f e1) (fmap f e2)
  fmap _ RationalParse = RationalParse


  fmap _ NaturalParse = NaturalParse
  fmap _ NaturalToBits = NaturalToBits
  fmap _ NaturalGcd = NaturalGcd
  fmap _ IntegerAdd = IntegerAdd
  fmap _ IntegerMultiply = IntegerMultiply
  fmap _ IntegerAnd = IntegerAnd
  fmap _ IntegerXor = IntegerXor
  fmap _ IntegerParse = IntegerParse
  fmap _ DoubleParse = DoubleParse
  fmap _ TextToLower = TextToLower
  fmap _ TextToUpper = TextToUpper
  fmap _ TextUnpack = TextUnpack
  fmap _ TextPack = TextPack
  fmap _ TextToList = TextToList
  fmap _ TextLength = TextLength
  fmap _ TextCompare = TextCompare
  fmap _ ListPermutations = ListPermutations
  fmap _ ListChoose = ListChoose
  fmap _ ListFixed = ListFixed
  fmap f (ListFixedLit e seqE) = ListFixedLit (fmap f e) (fmap (fmap f) seqE)
  fmap _ ListFixedFromList = ListFixedFromList
  fmap _ ListFixedToList = ListFixedToList
  fmap _ ListFixedHead = ListFixedHead
  fmap _ ListFixedTail = ListFixedTail

  fmap _ (Sym t) = Sym t
  fmap _ (SymLit t) = SymLit t
  fmap _ SymFromText = SymFromText
  fmap _ SymToText = SymToText

  fmap _ SZ = SZ
  fmap _ SS = SS
  fmap _ SZLit = SZLit
  fmap f (SSLit e) = SSLit (fmap f e)
  fmap _ SSFromNonZero = SSFromNonZero
  fmap _ SSToNonZero = SSToNonZero
  fmap _ SSToNatural = SSToNatural
  fmap _ SSAdd = SSAdd
  fmap _ SSSubtract = SSSubtract
  fmap _ SSEqual = SSEqual
  fmap _ SSLessThan = SSLessThan

  fmap _ Proof = Proof
  fmap _ ProofLit = ProofLit
  fmap _ ProofToBool = ProofToBool
  fmap _ ProofFromBool = ProofFromBool

  fmap _ PVoid = PVoid
  fmap _ PVoidUndefined = PVoidUndefined
  fmap _ PVoidError = PVoidError
  fmap _ PVoidKindUndefined = PVoidKindUndefined

  fmap f (Note s e1) = Note s (fmap f e1)
  fmap f (Record a) = Record $ fmap f <$> a
  fmap f (RecordLit a) = RecordLit $ fmap f <$> a
  fmap f expression = Lens.over unsafeSubExpressions (fmap f) expression
  {-# INLINABLE fmap #-}

instance Applicative (Expr s) where
    pure = Embed

    (<*>) = Control.Monad.ap

instance Monad (Expr s) where
    return = pure

    expression >>= k = case expression of
        Embed a    -> k a
        Let a b    -> Let (adaptBinding a) (b >>= k)
        Note a b   -> Note a (b >>= k)
        Record a -> Record $ bindRecordKeyValues <$> a
        RecordLit a -> RecordLit $ bindRecordKeyValues <$> a
        _ -> Lens.over unsafeSubExpressions (>>= k) expression
      where
        bindRecordKeyValues (RecordField s0 e) = RecordField s0 (e >>= k)

        adaptBinding (Binding src0 c src1 d src2 e) =
            Binding src0 c src1 (fmap adaptBindingAnnotation d) src2 (e >>= k)

        adaptBindingAnnotation (src3, f) = (src3, f >>= k)

instance Bifunctor Expr where
    first k (Note a b   ) = Note (k a) (first k b)
    first _ (Embed a    ) = Embed a
    first k (Let a b    ) = Let (first k a) (first k b)
    first k (Record a   ) = Record $ first k <$> a
    first k (RecordLit a) = RecordLit $ first k <$> a
    first k  expression  = Lens.over unsafeSubExpressions (first k) expression

    second = fmap

instance IsString (Expr s a) where
    fromString str = Var (fromString str)

-- | Generates a syntactically valid Dhall program
instance Pretty a => Pretty (Expr s a) where
    pretty = Pretty.unAnnotate . prettyExpr

{-
Instead of converting explicitly between 'Expr's and 'MultiLet', it might
be nicer to use a pattern synonym:

> pattern MultiLet' :: NonEmpty (Binding s a) -> Expr s a -> Expr s a
> pattern MultiLet' as b <- (multiLetFromExpr -> Just (MultiLet as b)) where
>   MultiLet' as b = wrapInLets as b
>
> multiLetFromExpr :: Expr s a -> Maybe (MultiLet s a)
> multiLetFromExpr = \case
>     Let x mA a b -> Just (multiLet x mA a b)
>     _ -> Nothing

This works in principle, but GHC as of v8.8.1 doesn't handle it well:
https://gitlab.haskell.org/ghc/ghc/issues/17096

This should be fixed by GHC-8.10, so it might be worth revisiting then.
-}

{-| Generate a 'MultiLet' from the contents of a 'Let'.

    In the resulting @'MultiLet' bs e@, @e@ is guaranteed not to be a 'Let',
    but it might be a @('Note' … ('Let' …))@.

    Given parser output, 'multiLet' consolidates @let@s that formed a
    let-block in the original source.
-}
multiLet :: Binding s a -> Expr s a -> MultiLet s a
multiLet b0 = \case
    Let b1 e1 ->
        let MultiLet bs e = multiLet b1 e1
        in  MultiLet (NonEmpty.cons b0 bs) e
    e -> MultiLet (b0 :| []) e

{-| Wrap let-'Binding's around an 'Expr'.

'wrapInLets' can be understood as an inverse for 'multiLet':

> let MultiLet bs e1 = multiLet b e0
>
> wrapInLets bs e1 == Let b e0
-}
wrapInLets :: Foldable f => f (Binding s a) -> Expr s a -> Expr s a
wrapInLets bs e = foldr Let e bs

{-| This type represents 1 or more nested `Let` bindings that have been
    coalesced together for ease of manipulation
-}
data MultiLet s a = MultiLet (NonEmpty (Binding s a)) (Expr s a)

-- | A traversal over the immediate sub-expressions of an expression.
subExpressions
    :: Applicative f => (Expr s a -> f (Expr s a)) -> Expr s a -> f (Expr s a)
subExpressions _ (Embed a) = pure (Embed a)
subExpressions f (Note a b) = Note a <$> f b
subExpressions f (Let a b) = Let <$> bindingExprs f a <*> f b
subExpressions f (Record a) = Record <$> traverse (recordFieldExprs f) a
subExpressions f (RecordLit a) = RecordLit <$> traverse (recordFieldExprs f) a
subExpressions f expression = unsafeSubExpressions f expression
{-# INLINABLE subExpressions #-}

{-| An internal utility used to implement transformations that require changing
    one of the type variables of the `Expr` type

    This utility only works because the implementation is partial, not
    handling the `Let`, `Note`, or `Embed` cases, which need to be handled by
    the caller.
-}
unsafeSubExpressions
    :: Applicative f => (Expr s a -> f (Expr t b)) -> Expr s a -> f (Expr t b)
unsafeSubExpressions _ (Const c) = pure (Const c)
unsafeSubExpressions _ (Var v) = pure (Var v)
unsafeSubExpressions f (Lam a b c) = Lam a <$> f b <*> f c
unsafeSubExpressions f (Pi a b c) = Pi a <$> f b <*> f c
unsafeSubExpressions f (App a b) = App <$> f a <*> f b
unsafeSubExpressions f (Annot a b) = Annot <$> f a <*> f b
unsafeSubExpressions _ Bool = pure Bool
unsafeSubExpressions _ (BoolLit b) = pure (BoolLit b)
unsafeSubExpressions f (BoolAnd a b) = BoolAnd <$> f a <*> f b
unsafeSubExpressions f (BoolOr a b) = BoolOr <$> f a <*> f b
unsafeSubExpressions f (BoolEQ a b) = BoolEQ <$> f a <*> f b
unsafeSubExpressions f (BoolNE a b) = BoolNE <$> f a <*> f b
unsafeSubExpressions f (BoolIf a b c) = BoolIf <$> f a <*> f b <*> f c
unsafeSubExpressions _ Natural = pure Natural
unsafeSubExpressions _ (NaturalLit n) = pure (NaturalLit n)
unsafeSubExpressions _ NaturalFold = pure NaturalFold
unsafeSubExpressions _ NaturalBuild = pure NaturalBuild
unsafeSubExpressions _ NaturalIsZero = pure NaturalIsZero
unsafeSubExpressions _ NaturalEven = pure NaturalEven
unsafeSubExpressions _ NaturalOdd = pure NaturalOdd
unsafeSubExpressions _ NaturalToInteger = pure NaturalToInteger
unsafeSubExpressions _ NaturalShow = pure NaturalShow
unsafeSubExpressions _ NaturalSubtract = pure NaturalSubtract
unsafeSubExpressions f (NaturalPlus a b) = NaturalPlus <$> f a <*> f b
unsafeSubExpressions f (NaturalTimes a b) = NaturalTimes <$> f a <*> f b
unsafeSubExpressions _ Integer = pure Integer
unsafeSubExpressions _ (IntegerLit n) = pure (IntegerLit n)
unsafeSubExpressions _ IntegerClamp = pure IntegerClamp
unsafeSubExpressions _ IntegerNegate = pure IntegerNegate
unsafeSubExpressions _ IntegerShow = pure IntegerShow
unsafeSubExpressions _ IntegerToDouble = pure IntegerToDouble
unsafeSubExpressions _ Double = pure Double
unsafeSubExpressions _ (DoubleLit n) = pure (DoubleLit n)
unsafeSubExpressions _ DoubleShow = pure DoubleShow
unsafeSubExpressions _ Text = pure Text
unsafeSubExpressions f (TextLit chunks) =
    TextLit <$> chunkExprs f chunks
unsafeSubExpressions f (TextAppend a b) = TextAppend <$> f a <*> f b
unsafeSubExpressions _ TextShow = pure TextShow
unsafeSubExpressions _ TextToLower = pure TextToLower
unsafeSubExpressions _ TextToUpper = pure TextToUpper
unsafeSubExpressions _ TextUnpack = pure TextUnpack
unsafeSubExpressions _ TextPack = pure TextPack
unsafeSubExpressions _ TextToList = pure TextToList
unsafeSubExpressions _ TextLength = pure TextLength
unsafeSubExpressions _ TextCompare = pure TextCompare
unsafeSubExpressions _ List = pure List
unsafeSubExpressions f (ListLit a b) = ListLit <$> traverse f a <*> traverse f b
unsafeSubExpressions f (ListAppend a b) = ListAppend <$> f a <*> f b
unsafeSubExpressions _ ListBuild = pure ListBuild
unsafeSubExpressions _ ListFold = pure ListFold
unsafeSubExpressions _ ListLength = pure ListLength
unsafeSubExpressions _ ListHead = pure ListHead
unsafeSubExpressions _ ListLast = pure ListLast
unsafeSubExpressions _ ListIndexed = pure ListIndexed
unsafeSubExpressions _ ListReverse = pure ListReverse
unsafeSubExpressions _ Optional = pure Optional
unsafeSubExpressions f (Some a) = Some <$> f a
unsafeSubExpressions _ None = pure None
unsafeSubExpressions f (Union a) = Union <$> traverse (traverse f) a
unsafeSubExpressions f (Combine a b c) = Combine a <$> f b <*> f c
unsafeSubExpressions f (CombineTypes a b) = CombineTypes <$> f a <*> f b
unsafeSubExpressions f (Prefer a b c) = Prefer <$> a' <*> f b <*> f c
  where
    a' = case a of
        PreferFromSource     -> pure PreferFromSource
        PreferFromWith d     -> PreferFromWith <$> f d
        PreferFromCompletion -> pure PreferFromCompletion
unsafeSubExpressions f (RecordCompletion a b) = RecordCompletion <$> f a <*> f b
unsafeSubExpressions f (Merge a b t) = Merge <$> f a <*> f b <*> traverse f t
unsafeSubExpressions f (ToMap a t) = ToMap <$> f a <*> traverse f t
unsafeSubExpressions f (Field a b) = Field <$> f a <*> pure b
unsafeSubExpressions f (Project a b) = Project <$> f a <*> traverse f b
unsafeSubExpressions f (Assert a) = Assert <$> f a
unsafeSubExpressions f (Equivalent a b) = Equivalent <$> f a <*> f b
unsafeSubExpressions f (With a b c) = With <$> f a <*> pure b <*> f c
unsafeSubExpressions f (ImportAlt l r) = ImportAlt <$> f l <*> f r
unsafeSubExpressions _ (Let {}) = unhandledConstructor "Let"
unsafeSubExpressions _ (Note {}) = unhandledConstructor "Note"
unsafeSubExpressions _ (Embed {}) = unhandledConstructor "Embed"
unsafeSubExpressions _ (Record {}) = unhandledConstructor "Record"
unsafeSubExpressions _ (RecordLit {}) = unhandledConstructor "RecordLit"

unsafeSubExpressions _ NonZero = pure NonZero
unsafeSubExpressions _ (NonZeroLit n) = pure (NonZeroLit n)
unsafeSubExpressions _ NonZeroShow = pure NonZeroShow
unsafeSubExpressions _ NonZeroClamp = pure NonZeroClamp
unsafeSubExpressions _ NonZeroDiv = pure NonZeroDiv
unsafeSubExpressions _ NonZeroMod = pure NonZeroMod
unsafeSubExpressions _ NonZeroLog = pure NonZeroLog
unsafeSubExpressions _ NonZeroAdd = pure NonZeroAdd
unsafeSubExpressions _ NonZeroMultiply = pure NonZeroMultiply
unsafeSubExpressions _ NonZeroToNatural = pure NonZeroToNatural
unsafeSubExpressions _ NonZeroToInteger = pure NonZeroToInteger
unsafeSubExpressions _ NonZeroParse = pure NonZeroParse

unsafeSubExpressions _ DateTime = pure DateTime
unsafeSubExpressions _ (DateTimeLit n) = pure (DateTimeLit n)
unsafeSubExpressions _ DateTimeShow = pure DateTimeShow
unsafeSubExpressions _ DateTimeParse = pure DateTimeParse
unsafeSubExpressions _ DateTimeFromSeconds = pure DateTimeFromSeconds
unsafeSubExpressions _ DateTimeToSeconds = pure DateTimeToSeconds

unsafeSubExpressions _ DateTimeAddYears = pure DateTimeAddYears
unsafeSubExpressions _ DateTimeAddMonths = pure DateTimeAddMonths
unsafeSubExpressions _ DateTimeAddDays = pure DateTimeAddDays
unsafeSubExpressions _ DateTimeFromWeek = pure DateTimeFromWeek
unsafeSubExpressions _ DateTimeToWeek = pure DateTimeToWeek
unsafeSubExpressions _ DateTimeToDate = pure DateTimeToDate
unsafeSubExpressions _ DateTimeFromDate = pure DateTimeFromDate
unsafeSubExpressions _ DateTimeLastDayOfMonth = pure DateTimeLastDayOfMonth

unsafeSubExpressions _ DateTimeGetJulianDay = pure DateTimeGetJulianDay
unsafeSubExpressions _ DateTimeSetJulianDay = pure DateTimeSetJulianDay

unsafeSubExpressions _ Regex = pure Regex
unsafeSubExpressions _ (RegexLit n) = pure (RegexLit n)
unsafeSubExpressions _ RegexShow = pure RegexShow
unsafeSubExpressions _ RegexMatch = pure RegexMatch
unsafeSubExpressions _ RegexScan = pure RegexScan
unsafeSubExpressions _ RegexSplit = pure RegexSplit
unsafeSubExpressions _ RegexReplace = pure RegexReplace
unsafeSubExpressions _ RegexReplix = pure RegexReplix
unsafeSubExpressions _ RegexParse = pure RegexParse
unsafeSubExpressions _ RegexToText = pure RegexToText

unsafeSubExpressions _ Rational = pure Rational
unsafeSubExpressions _ (RationalLit n) = pure (RationalLit n)
unsafeSubExpressions _ RationalShow = pure RationalShow
unsafeSubExpressions _ RationalFromDouble = pure RationalFromDouble
unsafeSubExpressions _ RationalToDouble = pure RationalToDouble
unsafeSubExpressions _ RationalFromRational = pure RationalFromRational
unsafeSubExpressions f (RationalPercent a b) = RationalPercent <$> f a <*> f b
unsafeSubExpressions _ RationalParse = pure RationalParse


unsafeSubExpressions _ NaturalParse = pure NaturalParse
unsafeSubExpressions _ NaturalToBits = pure NaturalToBits
unsafeSubExpressions _ NaturalGcd = pure NaturalGcd
unsafeSubExpressions _ IntegerAdd = pure IntegerAdd
unsafeSubExpressions _ IntegerMultiply = pure IntegerMultiply
unsafeSubExpressions _ IntegerAnd = pure IntegerAnd
unsafeSubExpressions _ IntegerXor = pure IntegerXor
unsafeSubExpressions _ IntegerParse = pure IntegerParse
unsafeSubExpressions _ DoubleParse = pure DoubleParse

unsafeSubExpressions _ ListPermutations = pure ListPermutations
unsafeSubExpressions _ ListChoose = pure ListChoose
unsafeSubExpressions _ ListFixed = pure ListFixed
unsafeSubExpressions f (ListFixedLit b c) = ListFixedLit <$> f b <*> traverse f c
unsafeSubExpressions _ ListFixedFromList = pure ListFixedFromList
unsafeSubExpressions _ ListFixedToList = pure ListFixedToList
unsafeSubExpressions _ ListFixedHead = pure ListFixedHead
unsafeSubExpressions _ ListFixedTail = pure ListFixedTail

unsafeSubExpressions _ (Sym t) = pure (Sym t)
unsafeSubExpressions _ (SymLit t) = pure (SymLit t)
unsafeSubExpressions _ SymFromText = pure SymFromText
unsafeSubExpressions _ SymToText = pure SymToText

unsafeSubExpressions _ SZ = pure SZ
unsafeSubExpressions _ SS = pure SS
unsafeSubExpressions _ SZLit = pure SZLit
unsafeSubExpressions f (SSLit b) = SSLit <$> f b

unsafeSubExpressions _ SSFromNonZero = pure SSFromNonZero
unsafeSubExpressions _ SSToNonZero = pure SSToNonZero
unsafeSubExpressions _ SSToNatural = pure SSToNatural
unsafeSubExpressions _ SSAdd = pure SSAdd
unsafeSubExpressions _ SSSubtract = pure SSSubtract
unsafeSubExpressions _ SSEqual = pure SSEqual
unsafeSubExpressions _ SSLessThan = pure SSLessThan

unsafeSubExpressions _ Proof = pure Proof
unsafeSubExpressions _ ProofLit = pure ProofLit
unsafeSubExpressions _ ProofToBool = pure ProofToBool
unsafeSubExpressions _ ProofFromBool = pure ProofFromBool

unsafeSubExpressions _ PVoid = pure PVoid
unsafeSubExpressions _ PVoidUndefined = pure PVoidUndefined
unsafeSubExpressions _ PVoidError = pure PVoidError
unsafeSubExpressions _ PVoidKindUndefined = pure PVoidKindUndefined
{-# INLINABLE unsafeSubExpressions #-}

unhandledConstructor :: Text -> a
unhandledConstructor constructor =
    internalError
        (   "Dhall.Syntax.unsafeSubExpressions: Unhandled "
        <>  constructor
        <>  " construtor"
        )

{-| Traverse over the immediate 'Expr' children in a 'Binding'.
-}
bindingExprs
  :: (Applicative f)
  => (Expr s a -> f (Expr s b))
  -> Binding s a -> f (Binding s b)
bindingExprs f (Binding s0 n s1 t s2 v) =
  Binding
    <$> pure s0
    <*> pure n
    <*> pure s1
    <*> traverse (traverse f) t
    <*> pure s2
    <*> f v
{-# INLINABLE bindingExprs #-}

{-| Traverse over the immediate 'Expr' children in a 'RecordField'.
-}
recordFieldExprs
    :: Applicative f
    => (Expr s a -> f (Expr s b))
    -> RecordField s a -> f (RecordField s b)
recordFieldExprs f (RecordField s0 e) =
    RecordField
        <$> pure s0
        <*> f e

-- | A traversal over the immediate sub-expressions in 'Chunks'.
chunkExprs
  :: Applicative f
  => (Expr s a -> f (Expr t b))
  -> Chunks s a -> f (Chunks t b)
chunkExprs f (Chunks chunks final) =
  flip Chunks final <$> traverse (traverse f) chunks
{-# INLINABLE chunkExprs #-}

{-| Internal representation of a directory that stores the path components in
    reverse order

    In other words, the directory @\/foo\/bar\/baz@ is encoded as
    @Directory { components = [ "baz", "bar", "foo" ] }@
-}
newtype Directory = Directory { components :: [Text] }
    deriving (Eq, Generic, Ord, Show, NFData)

instance Semigroup Directory where
    Directory components₀ <> Directory components₁ =
        Directory (components₁ <> components₀)

instance Pretty Directory where
    pretty (Directory {..}) = foldMap prettyPathComponent (reverse components)

prettyPathComponent :: Text -> Doc ann
prettyPathComponent text
    | Data.Text.all pathCharacter text =
        "/" <> Pretty.pretty text
    | otherwise =
        "/\"" <> Pretty.pretty text <> "\""

{-| A `File` is a `directory` followed by one additional path component
    representing the `file` name
-}
data File = File
    { directory :: Directory
    , file      :: Text
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Pretty File where
    pretty (File {..}) =
            Pretty.pretty directory
        <>  prettyPathComponent file

instance Semigroup File where
    File directory₀ _ <> File directory₁ file =
        File (directory₀ <> directory₁) file

-- | The beginning of a file path which anchors subsequent path components
data FilePrefix
    = Absolute
    -- ^ Absolute path
    | Here
    -- ^ Path relative to @.@
    | Parent
    -- ^ Path relative to @..@
    | Home
    -- ^ Path relative to @~@
    deriving (Eq, Generic, Ord, Show, NFData)

instance Pretty FilePrefix where
    pretty Absolute = ""
    pretty Here     = "."
    pretty Parent   = ".."
    pretty Home     = "~"

-- | The URI scheme
data Scheme = HTTP | HTTPS deriving (Eq, Generic, Ord, Show, NFData)

-- | This type stores all of the components of a remote import
data URL = URL
    { scheme    :: Scheme
    , authority :: Text
    , path      :: File
    , query     :: Maybe Text
    , headers   :: Maybe (Expr Src Import)
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Pretty URL where
    pretty (URL {..}) =
            schemeDoc
        <>  "://"
        <>  Pretty.pretty authority
        <>  pathDoc
        <>  queryDoc
        <>  foldMap prettyHeaders headers
      where
        prettyHeaders h = " using " <> Pretty.pretty h

        File {..} = path

        Directory {..} = directory

        pathDoc =
                foldMap prettyURIComponent (reverse components)
            <>  prettyURIComponent file

        schemeDoc = case scheme of
            HTTP  -> "http"
            HTTPS -> "https"

        queryDoc = case query of
            Nothing -> ""
            Just q  -> "?" <> Pretty.pretty q

prettyURIComponent :: Text -> Doc ann
prettyURIComponent text =
        Pretty.pretty $ URI.normalizeCase $ URI.normalizeEscape $ "/" <> Data.Text.unpack text

-- | The type of import (i.e. local vs. remote vs. environment)
data ImportType
    = Local FilePrefix File
    -- ^ Local path
    | Remote URL
    -- ^ URL of remote resource and optional headers stored in an import
    | Env  Text
    -- ^ Environment variable
    | Missing
    deriving (Eq, Generic, Ord, Show, NFData)

parent :: File
parent = File { directory = Directory { components = [ ".." ] }, file = "" }

instance Semigroup ImportType where
    Local prefix file₀ <> Local Here file₁ = Local prefix (file₀ <> file₁)

    Remote (URL { path = path₀, ..}) <> Local Here path₁ =
        Remote (URL { path = path₀ <> path₁, ..})

    Local prefix file₀ <> Local Parent file₁ =
        Local prefix (file₀ <> parent <> file₁)

    Remote (URL { path = path₀, .. }) <> Local Parent path₁ =
        Remote (URL { path = path₀ <> parent <> path₁, .. })

    import₀ <> Remote (URL { headers = headers₀, .. }) =
        Remote (URL { headers = headers₁, .. })
      where
        importHashed₀ = Import (ImportHashed Nothing import₀) Code

        headers₁ = fmap (fmap (importHashed₀ <>)) headers₀

    _ <> import₁ =
        import₁

instance Pretty ImportType where
    pretty (Local prefix file) =
        Pretty.pretty prefix <> Pretty.pretty file

    pretty (Remote url) = Pretty.pretty url

    pretty (Env env) = "env:" <> prettyEnvironmentVariable env

    pretty Missing = "missing"

-- | How to interpret the import's contents (i.e. as Dhall code or raw text)
data ImportMode = Code | RawText | Location
  deriving (Eq, Generic, Ord, Show, NFData)

-- | A `ImportType` extended with an optional hash for semantic integrity checks
data ImportHashed = ImportHashed
    { hash       :: Maybe Dhall.Crypto.SHA256Digest
    , importType :: ImportType
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Semigroup ImportHashed where
    ImportHashed _ importType₀ <> ImportHashed hash importType₁ =
        ImportHashed hash (importType₀ <> importType₁)

instance Pretty ImportHashed where
    pretty (ImportHashed  Nothing p) =
      Pretty.pretty p
    pretty (ImportHashed (Just h) p) =
      Pretty.pretty p <> " sha256:" <> Pretty.pretty (show h)

-- | Reference to an external resource
data Import = Import
    { importHashed :: ImportHashed
    , importMode   :: ImportMode
    } deriving (Eq, Generic, Ord, Show, NFData)

instance Semigroup Import where
    Import importHashed₀ _ <> Import importHashed₁ code =
        Import (importHashed₀ <> importHashed₁) code

instance Pretty Import where
    pretty (Import {..}) = Pretty.pretty importHashed <> Pretty.pretty suffix
      where
        suffix :: Text
        suffix = case importMode of
            RawText  -> " as Text"
            Location -> " as Location"
            Code     -> ""

{-| Returns `True` if the given `Char` is valid within an unquoted path
    component

    This is exported for reuse within the @"Dhall.Parser.Token"@ module
-}
pathCharacter :: Char -> Bool
pathCharacter c =
         '\x21' == c
    ||  ('\x24' <= c && c <= '\x27')
    ||  ('\x2A' <= c && c <= '\x2B')
    ||  ('\x2D' <= c && c <= '\x2E')
    ||  ('\x30' <= c && c <= '\x3B')
    ||  c == '\x3D'
    ||  ('\x40' <= c && c <= '\x5A')
    ||  ('\x5E' <= c && c <= '\x7A')
    ||  c == '\x7C'
    ||  c == '\x7E'

-- | Remove all `Note` constructors from an `Expr` (i.e. de-`Note`)
denote :: Expr s a -> Expr t a
denote = \case
    Note _ b      -> denote b
    Let a b       -> Let (denoteBinding a) (denote b)
    Embed a       -> Embed a
    Combine _ b c -> Combine Nothing (denote b) (denote c)
    Record a -> Record $ denoteRecordField <$> a
    RecordLit a -> RecordLit $ denoteRecordField <$> a
    expression -> Lens.over unsafeSubExpressions denote expression
  where
    denoteRecordField (RecordField _ e) = RecordField Nothing (denote e)
    denoteBinding (Binding _ c _ d _ e) =
        Binding Nothing c Nothing (fmap denoteBindingAnnotation d) Nothing (denote e)

    denoteBindingAnnotation (_, f) = (Nothing, denote f)

-- | The \"opposite\" of `denote`, like @first absurd@ but faster
renote :: Expr Void a -> Expr s a
renote = unsafeCoerce
{-# INLINE renote #-}

{-| Remove any outermost `Note` constructors

    This is typically used when you want to get the outermost non-`Note`
    constructor without removing internal `Note` constructors
-}
shallowDenote :: Expr s a -> Expr s a
shallowDenote (Note _ e) = shallowDenote e
shallowDenote         e  = e

-- | The set of reserved keywords according to the `keyword` rule in the grammar
reservedKeywords :: HashSet Text
reservedKeywords =
    Data.HashSet.fromList
        [
          "if"
        , "then"
        , "else"
        , "let"
        , "in"
        , "using"
        , "missing"
        , "as"
        , "Infinity"
        , "NaN"
        , "Prf"
        , "merge"
        , "Some"
        , "toMap"
        , "assert"
        , "forall"
        , "with"
        ]

-- | The set of reserved identifiers for the Dhall language
-- | Contains also all keywords from "reservedKeywords"
reservedIdentifiers :: HashSet Text
reservedIdentifiers = reservedKeywords <>
    Data.HashSet.fromList
        [ -- Builtins according to the `builtin` rule in the grammar
          "NonZero"
        , "NonZero/show"
        , "NonZero/clamp"
        , "NonZero/div"
        , "NonZero/mod"
        , "NonZero/log"
        , "NonZero/add"
        , "NonZero/multiply"
        , "NonZero/toNatural"
        , "NonZero/toInteger"
        , "NonZero/parse"

        , "DateTime"
        , "DateTime/show"
        , "DateTime/parse"
        , "DateTime/fromSeconds"
        , "DateTime/toSeconds"

        , "DateTime/addYears"
        , "DateTime/addMonths"
        , "DateTime/addDays"
        , "DateTime/fromWeek"
        , "DateTime/toWeek"
        , "DateTime/toDate"
        , "DateTime/fromDate"
        , "DateTime/lastDayOfMonth"

        , "DateTime/getJulianDay"
        , "DateTime/setJulianDay"

        , "Regex"
        , "Regex/show"
        , "Regex/match"
        , "Regex/scan"
        , "Regex/split"
        , "Regex/replace"
        , "Regex/replix"
        , "Regex/parse"
        , "Regex/toText"

        , "Rational"
        , "Rational/show"
        , "Rational/fromDouble"
        , "Rational/toDouble"
        , "Rational/fromRational"
        , "Rational/parse"

        , "Natural/fold"
        , "Natural/build"
        , "Natural/isZero"
        , "Natural/even"
        , "Natural/odd"
        , "Natural/toInteger"
        , "Natural/show"
        , "Natural/parse"
        , "Natural/toBits"
        , "Natural/subtract"
        , "Natural/gcd"
        , "Integer"
        , "Integer/add"
        , "Integer/multiply"
        , "Integer/and"
        , "Integer/xor"
        , "Integer/clamp"
        , "Integer/negate"
        , "Integer/show"
        , "Integer/toDouble"
        , "Integer/show"
        , "Integer/parse"
        , "Natural/subtract"
        , "Double/show"
        , "Double/parse"
        , "List/build"
        , "List/fold"
        , "List/length"
        , "List/head"
        , "List/last"
        , "List/indexed"
        , "List/reverse"
        , "List/permutations"
        , "List/choose"
        , "ListFixed/fromList"
        , "ListFixed/toList"
        , "ListFixed/head"
        , "ListFixed/tail"
        , "Text/show"
        , "Text/toLower"
        , "Text/toUpper"
        , "Text/unpack"
        , "Text/pack"
        , "Text/toList"
        , "Text/length"
        , "Text/compare"
        , "Bool"
        , "True"
        , "False"

        , "Sym/fromText"
        , "Sym/toText"

        , "SZ"
        , "SS"
        , "SS/fromNonZero"
        , "SS/toNonZero"
        , "SS/toNatural"
        , "SS/add"
        , "SS/subtract"
        , "SS/equal"
        , "SS/lessThan"

        , "Proof"
        , "Proof/toBool"
        , "Proof/fromBool"

        , "PVoid"
        , "PVoid/undefined"
        , "PVoid/error"
        , "PVoid/kindUndefined"

        , "Optional"
        , "None"
        , "Natural"
        , "Integer"
        , "Double"
        , "Text"
        , "List"
        , "ListFixed"
        , "Type"
        , "Kind"
        , "Sort"
        ]

-- | Same as @Data.Text.splitOn@, except always returning a `NonEmpty` result
splitOn :: Text -> Text -> NonEmpty Text
splitOn needle haystack =
    case Data.Text.splitOn needle haystack of
        []     -> "" :| []
        t : ts -> t  :| ts

-- | Split `Chunks` by lines
linesLiteral :: Chunks s a -> NonEmpty (Chunks s a)
linesLiteral (Chunks [] suffix) =
    fmap (Chunks []) (splitOn "\n" suffix)
linesLiteral (Chunks ((prefix, interpolation) : pairs₀) suffix₀) =
    foldr
        NonEmpty.cons
        (Chunks ((lastLine, interpolation) : pairs₁) suffix₁ :| chunks)
        (fmap (Chunks []) initLines)
  where
    splitLines = splitOn "\n" prefix

    initLines = NonEmpty.init splitLines
    lastLine  = NonEmpty.last splitLines

    Chunks pairs₁ suffix₁ :| chunks = linesLiteral (Chunks pairs₀ suffix₀)

-- | Flatten several `Chunks` back into a single `Chunks` by inserting newlines
unlinesLiteral :: NonEmpty (Chunks s a) -> Chunks s a
unlinesLiteral chunks =
    Data.Foldable.fold (NonEmpty.intersperse "\n" chunks)

-- | Returns `True` if the `Chunks` represents a blank line
emptyLine :: Chunks s a -> Bool
emptyLine (Chunks [] ""  ) = True
emptyLine (Chunks [] "\r") = True  -- So that `\r\n` is treated as a blank line
emptyLine  _               = False

-- | Return the leading whitespace for a `Chunks` literal
leadingSpaces :: Chunks s a -> Text
leadingSpaces chunks = Data.Text.takeWhile isSpace firstText
  where
    isSpace c = c == ' ' || c == '\t'

    firstText =
        case chunks of
            Chunks                []  suffix -> suffix
            Chunks ((prefix, _) : _ ) _      -> prefix

{-| Compute the longest shared whitespace prefix for the purposes of stripping
    leading indentation
-}
longestSharedWhitespacePrefix :: NonEmpty (Chunks s a) -> Text
longestSharedWhitespacePrefix literals =
    case fmap leadingSpaces filteredLines of
        l : ls -> Data.Foldable.foldl' sharedPrefix l ls
        []     -> ""
  where
    sharedPrefix ab ac =
        case Data.Text.commonPrefixes ab ac of
            Just (a, _b, _c) -> a
            Nothing          -> ""

    -- The standard specifies to filter out blank lines for all lines *except*
    -- for the last line
    filteredLines = newInit <> pure oldLast
      where
        oldInit = NonEmpty.init literals

        oldLast = NonEmpty.last literals

        newInit = filter (not . emptyLine) oldInit

-- | Drop the first @n@ characters for a `Chunks` literal
dropLiteral :: Int -> Chunks s a -> Chunks s a
dropLiteral n (Chunks [] suffix) =
    Chunks [] (Data.Text.drop n suffix)
dropLiteral n (Chunks ((prefix, interpolation) : rest) suffix) =
    Chunks ((Data.Text.drop n prefix, interpolation) : rest) suffix

{-| Convert a single-quoted `Chunks` literal to the equivalent double-quoted
    `Chunks` literal
-}
toDoubleQuoted :: Chunks Src a -> Chunks Src a
toDoubleQuoted literal =
    unlinesLiteral (fmap (dropLiteral indent) literals)
  where
    literals = linesLiteral literal

    longestSharedPrefix = longestSharedWhitespacePrefix literals

    indent = Data.Text.length longestSharedPrefix

makeSSExpr :: NonZero -> Expr s a
makeSSExpr (NonZeroC n) = foldr (const (App SS)) SZ ([1 .. n - 1] :: [Natural])

-- | Desugar all @with@ expressions
desugarWith :: Expr s a -> Expr s a
desugarWith = Optics.rewriteOf subExpressions rewrite
  where
    rewrite e@(With record (key :| []) value) =
        Just (Prefer (PreferFromWith e) record (RecordLit [ (key, makeRecordField value) ]))
    rewrite e@(With record (key0 :| key1 : keys) value) =
        Just
            (Prefer (PreferFromWith e) record
                (RecordLit
                    [ (key0, makeRecordField $ With (Field record key0) (key1 :| keys) value) ]
                )
            )
    rewrite _ = Nothing

_ERROR :: String
_ERROR = "\ESC[1;31mError\ESC[0m"

{-| Utility function used to throw internal errors that should never happen
    (in theory) but that are not enforced by the type system
-}
internalError :: Data.Text.Text -> forall b . b
internalError text = error (unlines
    [ _ERROR <> ": Compiler bug                                                        "
    , "                                                                                "
    , "Explanation: This error message means that there is a bug in the Dhall compiler."
    , "You didn't do anything wrong, but if you would like to see this problem fixed   "
    , "then you should report the bug at:                                              "
    , "                                                                                "
    , "https://github.com/dhall-lang/dhall-haskell/issues                              "
    , "                                                                                "
    , "Please include the following text in your bug report:                           "
    , "                                                                                "
    , "```                                                                             "
    , Data.Text.unpack text <> "                                                       "
    , "```                                                                             "
    ] )
