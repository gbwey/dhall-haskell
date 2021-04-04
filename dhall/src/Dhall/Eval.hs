{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE TupleSections        #-}

{-# OPTIONS_GHC -O #-}

{-| Eval-apply environment machine with conversion checking and quoting to
    normal forms. Fairly similar to GHCI's STG machine algorithmically, but much
    simpler, with no known call optimization or environment trimming.

    Potential optimizations without changing Expr:

    * In conversion checking, get non-shadowing variables not by linear
      Env-walking, but by keeping track of Env size, and generating names which
      are known to be illegal as source-level names (to rule out shadowing).

    * Use HashMap Text chunks for large let-definitions blocks. "Large" vs
      "Small" is fairly cheap to determine at evaluation time.

    Potential optimizations with changing Expr:

    * Use actual full de Bruijn indices in Var instead of Text counting indices.
      Then, we'd switch to full de Bruijn levels in Val as well, and use proper
      constant time non-shadowing name generation.
-}

module Dhall.Eval (
    judgmentallyEqual
  , normalize
  , alphaNormalize
  , eval
  , quote
  , envNames
  , countNames
  , conv
  , toVHPi
  , Closure(..)
  , Names(..)
  , Environment(..)
  , Val(..)
  , (~>)
  , textShow

  , dumpExpr -- remove
  , dumpVal  -- remove
  , VChunks(..)
  , choose
  , perms

  ) where

import Data.Foldable  (foldr', toList)
import Data.Sequence  (Seq, ViewL (..), ViewR (..))
import Data.Text      (Text)
import Data.Void      (Void)
import Dhall.Map      (Map)
import Dhall.Set      (Set)
import GHC.Natural    (Natural)
import Prelude        hiding (succ)

import Dhall.Syntax
    ( Binding (..)
    , Chunks (..)
    , Const (..)
    , DhallDouble (..)
    , Expr (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , Var (..)
  , NonZero(..)
  , DateTime(..)
  , dateTimeToUtc
  , utcToDateTime
  , Regex(..)
  , compileRegex
  , compileRegexUnsafe
  , mkNonZeroUnsafe
    )

import qualified Data.Bits
import qualified Data.Char
import qualified Data.Function
import qualified Data.Ord
import qualified Data.Ratio
import Data.Ratio ((%))
import qualified Data.Sequence as Sequence
import qualified Data.Set
import qualified Data.Text     as Text
import qualified Data.Time
import qualified Data.Time.Calendar.OrdinalDate
import qualified Data.Time.Calendar.WeekDate
import qualified Data.Time.Calendar
import qualified Dhall.Map     as Map
import qualified Dhall.Set
import qualified Dhall.Syntax  as Syntax
import qualified Text.Printf

import qualified Dhall.Parser.Token as Dhall.Parser.Token
import qualified Dhall.Parser.Combinators as Dhall.Parser.Combinators
import qualified Text.Megaparsec

import qualified Text.Regex.PCRE.Heavy as RH
--import Debug.Trace

data Environment a
    = Empty
    | Skip   !(Environment a) {-# UNPACK #-} !Text
    | Extend !(Environment a) {-# UNPACK #-} !Text (Val a)

deriving instance (Show a, Show (Val a -> Val a)) => Show (Environment a)

dumpEnv :: Environment a -> String
dumpEnv Empty = "Empty"
dumpEnv (Skip e t) = "Skip [" ++ Text.unpack t ++ "] env=" ++ dumpEnv e
dumpEnv (Extend e t v) = "Extend [" ++ Text.unpack t ++ "] val=" ++ dumpVal v ++ " env=" ++ dumpEnv e

errorMsg :: String
errorMsg = unlines
  [ _ERROR <> ": Compiler bug                                                        "
  , "                                                                                "
  , "An ill-typed expression was encountered during normalization.                   "
  , "Explanation: This error message means that there is a bug in the Dhall compiler."
  , "You didn't do anything wrong, but if you would like to see this problem fixed   "
  , "then you should report the bug at:                                              "
  , "                                                                                "
  , "https://github.com/dhall-lang/dhall-haskell/issues                              "
  ]
  where
    _ERROR :: String
    _ERROR = "\ESC[1;31mError\ESC[0m"


data Closure a = Closure !Text !(Environment a) !(Expr Void a)

deriving instance (Show a, Show (Val a -> Val a)) => Show (Closure a)

data VChunks a = VChunks ![(Text, Val a)] !Text

deriving instance (Show a, Show (Val a -> Val a)) => Show (VChunks a)

instance Semigroup (VChunks a) where
  VChunks xys z <> VChunks [] z' = VChunks xys (z <> z')
  VChunks xys z <> VChunks ((x', y'):xys') z' = VChunks (xys ++ (z <> x', y'):xys') z'

instance Monoid (VChunks a) where
  mempty = VChunks [] mempty

{-| Some information is lost when `eval` converts a `Lam` or a built-in function
    from the `Expr` type to a `VHLam` of the `Val` type and `quote` needs that
    information in order to reconstruct an equivalent `Expr`.  This `HLamInfo`
    type holds that extra information necessary to perform that reconstruction
-}
data HLamInfo a
  = Prim
  -- ^ Don't store any information
  | Typed !Text (Val a)
  -- ^ Store the original name and type of the variable bound by the `Lam`
  | NaturalSubtractZero
  -- ^ The original function was a @Natural/subtract 0@.  We need to preserve
  --   this information in case the @Natural/subtract@ ends up not being fully
  --   saturated, in which case we need to recover the unsaturated built-in

deriving instance (Show a, Show (Val a -> Val a)) => Show (HLamInfo a)

pattern VPrim :: (Val a -> Val a) -> Val a
pattern VPrim f = VHLam Prim f

toVHPi :: Eq a => Val a -> Maybe (Text, Val a, Val a -> Val a)
toVHPi (VPi a b@(Closure x _ _)) = Just (x, a, instantiate b)
toVHPi (VHPi x a b             ) = Just (x, a, b)
toVHPi  _                        = Nothing

data Val a
    = VConst !Const
    | VVar !Text !Int
    | VPrimVar
    | VApp !(Val a) !(Val a)

    | VLam (Val a) {-# UNPACK #-} !(Closure a)
    | VHLam !(HLamInfo a) !(Val a -> Val a)

    | VPi (Val a) {-# UNPACK #-} !(Closure a)
    | VHPi !Text (Val a) !(Val a -> Val a)

    | VBool
    | VBoolLit !Bool
    | VBoolAnd !(Val a) !(Val a)
    | VBoolOr !(Val a) !(Val a)
    | VBoolEQ !(Val a) !(Val a)
    | VBoolNE !(Val a) !(Val a)
    | VBoolIf !(Val a) !(Val a) !(Val a)

    | VNonZero
    | VNonZeroLit !NonZero
    | VNonZeroShow !(Val a)
    | VNonZeroClamp !(Val a)
    | VNonZeroDiv !(Val a) !(Val a)
    | VNonZeroMod !(Val a) !(Val a)
    | VNonZeroLog !(Val a) !(Val a)
    | VNonZeroAdd !(Val a) !(Val a)
    | VNonZeroMultiply !(Val a) !(Val a)
    | VNonZeroToNatural !(Val a)
    | VNonZeroToInteger !(Val a)
    | VNonZeroParse !(Val a)

    | VDateTime
    | VDateTimeLit !DateTime
    | VDateTimeShow !(Val a)
    | VDateTimeParse !(Val a)
    | VDateTimeFromSeconds !(Val a)
    | VDateTimeToSeconds !(Val a)

    | VDateTimeAddYears !(Val a) !(Val a)
    | VDateTimeAddMonths !(Val a) !(Val a)
    | VDateTimeAddDays !(Val a) !(Val a)
    | VDateTimeFromWeek !(Val a) !(Val a) !(Val a)
    | VDateTimeToWeek !(Val a)
    | VDateTimeToDate !(Val a) !(Val a) !(Val a) !(Val a) !(Val a) !(Val a)
    | VDateTimeFromDate !(Val a)
    | VDateTimeLastDayOfMonth !(Val a) !(Val a)

    | VDateTimeGetJulianDay !(Val a)
    | VDateTimeSetJulianDay !(Val a) !(Val a)

    | VRegex
    | VRegexLit !Regex
    | VRegexShow !(Val a)
    | VRegexMatch !(Val a) !(Val a)
    | VRegexScan !(Val a) !(Val a) !(Val a)
    | VRegexSplit !(Val a) !(Val a) !(Val a)
    | VRegexReplace !(Val a) !(Val a) !(Val a)
    | VRegexReplix !(Val a) !(Val a) !(Val a)
    | VRegexParse !(Val a)
    | VRegexToText !(Val a)

    | VRational
    | VRationalLit !Rational
    | VRationalShow !(Val a)
    | VRationalFromDouble !(Val a) !(Val a)
    | VRationalToDouble !(Val a)
    | VRationalFromRational !(Val a)
    | VRationalPercent !(Val a) !(Val a)
    | VRationalParse !(Val a)


    | VNatural
    | VNaturalLit !Natural
    | VNaturalFold !(Val a) !(Val a) !(Val a) !(Val a)
    | VNaturalBuild !(Val a)
    | VNaturalIsZero !(Val a)
    | VNaturalEven !(Val a)
    | VNaturalOdd !(Val a)
    | VNaturalToInteger !(Val a)
    | VNaturalShow !(Val a)
    | VNaturalParse !(Val a)
    | VNaturalToBits !(Val a)
    | VNaturalSubtract !(Val a) !(Val a)
    | VNaturalGcd !(Val a) !(Val a)
    | VNaturalPlus !(Val a) !(Val a)
    | VNaturalTimes !(Val a) !(Val a)

    | VInteger
    | VIntegerLit !Integer
    | VIntegerAdd !(Val a) !(Val a)
    | VIntegerMultiply !(Val a) !(Val a)
    | VIntegerAnd !(Val a) !(Val a)
    | VIntegerXor !(Val a) !(Val a)
    | VIntegerClamp !(Val a)
    | VIntegerNegate !(Val a)
    | VIntegerShow !(Val a)
    | VIntegerParse !(Val a)
    | VIntegerToDouble !(Val a)

    | VDouble
    | VDoubleLit !DhallDouble
    | VDoubleShow !(Val a)
    | VDoubleParse !(Val a)

    | VText
    | VTextLit !(VChunks a)
    | VTextAppend !(Val a) !(Val a)
    | VTextShow !(Val a)
    | VTextToLower !(Val a)
    | VTextToUpper !(Val a)
    | VTextUnpack !(Val a)
    | VTextPack !(Val a)
    | VTextToList !(Val a)
    | VTextLength !(Val a)
    | VTextCompare !(Val a) !(Val a) !(Val a)

    | VList !(Val a)
    | VListLit !(Maybe (Val a)) !(Seq (Val a))
    | VListAppend !(Val a) !(Val a)
    | VListBuild   (Val a) !(Val a)
    | VListFold    (Val a) !(Val a) !(Val a) !(Val a) !(Val a)
    | VListLength  (Val a) !(Val a)
    | VListHead    (Val a) !(Val a)
    | VListLast    (Val a) !(Val a)
    | VListIndexed (Val a) !(Val a)
    | VListReverse (Val a) !(Val a)
    | VListPermutations !(Val a) !(Val a)
    | VListChoose !(Val a) !(Val a) !(Val a)

    | VListFixed !(Val a) !(Val a)
    | VListFixedLit !(Val a) (Seq (Val a))
    | VListFixedFromList !(Val a) !(Val a) !(Val a) !(Val a) -- (n : SS (SS ... SZ)) (a : Type) (def: a) [a]
    | VListFixedToList !(Val a) !(Val a) !(Val a)
    | VListFixedHead !(Val a) !(Val a) !(Val a)
    | VListFixedTail !(Val a) !(Val a) !(Val a)

    | VSym Text

    | VSZ
    | VSS !(Val a)

    | VSymLit Text
    | VSymFromText !(Val a)
    | VSymToText !(Val a)

    | VSZLit -- do we use this?
    | VSSLit !(Val a) -- ???
    | VSSFromNonZero !(Val a)
    | VSSToNonZero !(Val a)
    | VSSToNatural !(Val a)
    | VSSAdd !(Val a) !(Val a)
    | VSSSubtract !(Val a) !(Val a)
    | VSSEqual !(Val a) !(Val a)
    | VSSLessThan !(Val a) !(Val a)

    | VProof !(Val a)
    | VProofLit
    | VProofToBool !(Val a)
    | VProofFromBool !(Val a) !(Val a)

    | VPVoid !(Val a)
    | VPVoidUndefined !(Val a)
    | VPVoidError !(Val a) !(Val a)
    | VPVoidKindUndefined !(Val a)

    | VOptional (Val a)
    | VSome (Val a)
    | VNone (Val a)
    | VRecord !(Map Text (Val a))
    | VRecordLit !(Map Text (Val a))
    | VUnion !(Map Text (Maybe (Val a)))
    | VCombine !(Maybe Text) !(Val a) !(Val a)
    | VCombineTypes !(Val a) !(Val a)
    | VPrefer !(Val a) !(Val a)
    | VMerge !(Val a) !(Val a) !(Maybe (Val a))
    | VToMap !(Val a) !(Maybe (Val a))
    | VField !(Val a) !Text
    | VInject !(Map Text (Maybe (Val a))) !Text !(Maybe (Val a))
    | VProject !(Val a) !(Either (Set Text) (Val a))
    | VAssert !(Val a)
    | VEquivalent !(Val a) !(Val a)
    | VEmbed a

-- | For use with "Text.Show.Functions".
deriving instance (Show a, Show (Val a -> Val a)) => Show (Val a)

(~>) :: Val a -> Val a -> Val a
(~>) a b = VHPi "_" a (\_ -> b)
{-# INLINE (~>) #-}

infixr 5 ~>

countEnvironment :: Text -> Environment a -> Int
countEnvironment x = go (0 :: Int)
  where
    go !acc Empty             = acc
    go  acc (Skip env x'    ) = go (if x == x' then acc + 1 else acc) env
    go  acc (Extend env x' _) = go (if x == x' then acc + 1 else acc) env

instantiate :: Eq a => Closure a -> Val a -> Val a
instantiate (Closure x env t) !u = eval (Extend env x u) t
{-# INLINE instantiate #-}

-- Out-of-env variables have negative de Bruijn levels.
vVar :: Environment a -> Var -> Val a
vVar env0 (V x i0) = go env0 i0
  where
    go (Extend env x' v) i
        | x == x' =
            if i == 0 then v else go env (i - 1)
        | otherwise =
            go env i
    go (Skip env x') i
        | x == x' =
            if i == 0 then VVar x (countEnvironment x env) else go env (i - 1)
        | otherwise =
            go env i
    go Empty i =
        VVar x (negate i - 1)

vApp :: Eq a => Val a -> Val a -> Val a
vApp !t !u =
    case t of
        VLam _ t'  -> instantiate t' u
        VHLam _ t' -> t' u
        t'        -> VApp t' u
{-# INLINE vApp #-}

vPrefer :: Eq a => Environment a -> Val a -> Val a -> Val a
vPrefer env t u =
    case (t, u) of
        (VRecordLit m, u') | null m ->
            u'
        (t', VRecordLit m) | null m ->
            t'
        (VRecordLit m, VRecordLit m') ->
            VRecordLit (Map.union m' m)
        (t', u') | conv env t' u' ->
            t'
        (t', u') ->
            VPrefer t' u'
{-# INLINE vPrefer #-}

vCombine :: Maybe Text -> Val a -> Val a -> Val a
vCombine mk t u =
    case (t, u) of
        (VRecordLit m, u') | null m ->
            u'
        (t', VRecordLit m) | null m ->
            t'
        (VRecordLit m, VRecordLit m') ->
            VRecordLit (Map.unionWith (vCombine Nothing) m m')
        (t', u') ->
            VCombine mk t' u'

vCombineTypes :: Val a -> Val a -> Val a
vCombineTypes t u =
    case (t, u) of
        (VRecord m, u') | null m ->
            u'
        (t', VRecord m) | null m ->
            t'
        (VRecord m, VRecord m') ->
            VRecord (Map.unionWith vCombineTypes m m')
        (t', u') ->
            VCombineTypes t' u'

vListAppend :: Val a -> Val a -> Val a
vListAppend t u =
    case (t, u) of
        (VListLit _ xs, u') | null xs ->
            u'
        (t', VListLit _ ys) | null ys ->
            t'
        (VListLit t' xs, VListLit _ ys) ->
            VListLit t' (xs <> ys)
        (t', u') ->
            VListAppend t' u'
{-# INLINE vListAppend #-}

vNaturalPlus :: Val a -> Val a -> Val a
vNaturalPlus t u =
    case (t, u) of
        (VNaturalLit 0, u') ->
            u'
        (t', VNaturalLit 0) ->
            t'
        (VNaturalLit m, VNaturalLit n) ->
            VNaturalLit (m + n)
        (t', u') ->
            VNaturalPlus t' u'
{-# INLINE vNaturalPlus #-}

vField :: Val a -> Text -> Val a
vField t0 k = go t0
  where
    go = \case
        VUnion m -> case Map.lookup k m of
            Just (Just _) -> VPrim $ \ ~u -> VInject m k (Just u)
            Just Nothing  -> VInject m k Nothing
            _             -> error errorMsg
        VRecordLit m
            | Just v <- Map.lookup k m -> v
            | otherwise -> error errorMsg
        VProject t _ -> go t
        VPrefer (VRecordLit m) r -> case Map.lookup k m of
            Just v -> VField (VPrefer (singletonVRecordLit v) r) k
            Nothing -> go r
        VPrefer l (VRecordLit m) -> case Map.lookup k m of
            Just v -> v
            Nothing -> go l
        VCombine mk (VRecordLit m) r -> case Map.lookup k m of
            Just v -> VField (VCombine mk (singletonVRecordLit v) r) k
            Nothing -> go r
        VCombine mk l (VRecordLit m) -> case Map.lookup k m of
            Just v -> VField (VCombine mk l (singletonVRecordLit v)) k
            Nothing -> go l
        t -> VField t k

    singletonVRecordLit v = VRecordLit (Map.singleton k v)
{-# INLINE vField #-}

vProjectByFields :: Eq a => Environment a -> Val a -> Set Text -> Val a
vProjectByFields env t ks =
    if null ks
        then VRecordLit mempty
        else case t of
            VRecordLit kvs ->
                let kvs' = Map.restrictKeys kvs (Dhall.Set.toSet ks)
                in  VRecordLit kvs'
            VProject t' _ ->
                vProjectByFields env t' ks
            VPrefer l (VRecordLit kvs) ->
                let ksSet = Dhall.Set.toSet ks

                    kvs' = Map.restrictKeys kvs ksSet

                    ks' =
                        Dhall.Set.fromSet
                            (Data.Set.difference ksSet (Map.keysSet kvs'))

                in  vPrefer env (vProjectByFields env l ks') (VRecordLit kvs')
            t' ->
                VProject t' (Left ks)

eval :: forall a. Eq a => Environment a -> Expr Void a -> Val a
eval !env t0 =
    case t0 of
        Const k ->
            VConst k
        Var v ->
            vVar env v
        Lam x a t ->
            VLam (eval env a) (Closure x env t)
        Pi x a b ->
            VPi (eval env a) (Closure x env b)
        App t u ->
            vApp (eval env t) (eval env u)
        Let (Binding _ x _ _mA _ a) b ->
            let !env' = Extend env x (eval env a)
            in  eval env' b
        Annot t _ ->
            eval env t
        Bool ->
            VBool
        BoolLit b ->
            VBoolLit b
        BoolAnd t u ->
            case (eval env t, eval env u) of
                (VBoolLit True, u')       -> u'
                (VBoolLit False, _)       -> VBoolLit False
                (t', VBoolLit True)       -> t'
                (_ , VBoolLit False)      -> VBoolLit False
                (t', u') | conv env t' u' -> t'
                (t', u')                  -> VBoolAnd t' u'
        BoolOr t u ->
            case (eval env t, eval env u) of
                (VBoolLit False, u')      -> u'
                (VBoolLit True, _)        -> VBoolLit True
                (t', VBoolLit False)      -> t'
                (_ , VBoolLit True)       -> VBoolLit True
                (t', u') | conv env t' u' -> t'
                (t', u')                  -> VBoolOr t' u'
        BoolEQ t u ->
            case (eval env t, eval env u) of
                (VBoolLit True, u')       -> u'
                (t', VBoolLit True)       -> t'
                (t', u') | conv env t' u' -> VBoolLit True
                (t', u')                  -> VBoolEQ t' u'
        BoolNE t u ->
            case (eval env t, eval env u) of
                (VBoolLit False, u')      -> u'
                (t', VBoolLit False)      -> t'
                (t', u') | conv env t' u' -> VBoolLit False
                (t', u')                  -> VBoolNE t' u'
        BoolIf b t f ->
            case (eval env b, eval env t, eval env f) of
                (VBoolLit True,  t', _ )            -> t'
                (VBoolLit False, _ , f')            -> f'
                (b', VBoolLit True, VBoolLit False) -> b'
                (_, t', f') | conv env t' f'        -> t'
                (b', t', f')                        -> VBoolIf b' t' f'

        NonZero ->
            VNonZero
        NonZeroLit n ->
            VNonZeroLit n
        NonZeroShow -> VPrim $ \case
            VNonZeroLit (NonZeroC n) -> VTextLit (VChunks [] (Text.pack ('!':show n)))
            n             -> VNonZeroShow n
        NonZeroClamp ->
            VPrim $ \case
                VNaturalLit n
                    | 0 == n    -> VNonZeroLit (mkNonZeroUnsafe 1)
                    | otherwise -> VNonZeroLit (mkNonZeroUnsafe n)
                n -> VNonZeroClamp n

        NonZeroDiv -> VPrim $ \case
            x@(VIntegerLit m) ->
                VPrim $ \case
                    VNonZeroLit (NonZeroC n) -> VIntegerLit (div m (fromIntegral n))
                    y -> VNonZeroDiv x y
            x ->
                VPrim $ \case
                    y                -> VNonZeroDiv x y

        NonZeroMod -> VPrim $ \case
            x@(VIntegerLit m) ->
                VPrim $ \case
                    VNonZeroLit(NonZeroC n) -> VIntegerLit (mod m (fromIntegral n))
                    y -> VNonZeroMod x y
            x ->
                VPrim $ \case
                    y                -> VNonZeroMod x y


        NonZeroLog -> VPrim $ \case
            x@(VNonZeroLit(NonZeroC base)) ->
                VPrim $ \case
                    VNonZeroLit(NonZeroC n) -> VNaturalLit (ceiling (logBase (fromIntegral base + 1) (fromIntegral n) :: Double))
                    y -> VNonZeroLog x y
            x ->
                VPrim $ \case
                    y                -> VNonZeroLog x y

        NonZeroAdd -> VPrim $ \case
            x@(VNonZeroLit (NonZeroC m)) ->
                VPrim $ \case
                    VNonZeroLit (NonZeroC n) -> VNonZeroLit (mkNonZeroUnsafe (m + n))
                    y -> VNonZeroAdd x y
            x ->
                VPrim $ \case
                    y                -> VNonZeroAdd x y

        NonZeroMultiply -> VPrim $ \case
            x@(VNonZeroLit (NonZeroC m)) ->
                VPrim $ \case
                    VNonZeroLit (NonZeroC n) -> VNonZeroLit (mkNonZeroUnsafe (m * n))
                    y -> VNonZeroMultiply x y
            x ->
                VPrim $ \case
                    y                -> VNonZeroMultiply x y

        NonZeroToNatural -> VPrim $ \case
            VNonZeroLit (NonZeroC n) -> VNaturalLit n
            n             -> VNonZeroToNatural n

        NonZeroToInteger -> VPrim $ \case
            VNonZeroLit (NonZeroC n) -> VIntegerLit (fromIntegral n)
            n             -> VNonZeroToInteger n

        NonZeroParse -> VPrim $ \case
            VTextLit (VChunks [] t) ->
              case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.nonZeroLiteral <* Text.Megaparsec.eof) "?" t of
                Left _ -> VNone VNonZero
                Right r -> VSome (VNonZeroLit r)
            n             -> VNonZeroParse n

        DateTime ->
            VDateTime
        DateTimeLit n ->
            VDateTimeLit n
        DateTimeShow -> VPrim $ \case
            VDateTimeLit n ->
              let x = dateTimeToUtc n
                  y = Data.Time.formatTime Data.Time.defaultTimeLocale "%FT%T" x
              in VTextLit (VChunks [] (Text.pack ('^':y)))
            n             -> VDateTimeShow n

        DateTimeParse -> VPrim $ \case
            VTextLit (VChunks [] t) ->
              case Dhall.Parser.Token.dateTimeParse (Text.unpack t) of
                Left _   -> VNone VDateTime
                Right tm -> VSome (VDateTimeLit tm)
            n            -> VDateTimeParse n

        DateTimeFromSeconds -> VPrim $ \case
            VIntegerLit n ->
               VDateTimeLit (DateTimeC n)
            n             -> VDateTimeFromSeconds n

        DateTimeToSeconds -> VPrim $ \case
            VDateTimeLit (DateTimeC n) ->
               VIntegerLit n
            n             -> VDateTimeToSeconds n

        DateTimeAddYears -> VPrim $ \case
            x@(VIntegerLit n) ->
                VPrim $ \case
                    VDateTimeLit m ->
                      let u = dateTimeToUtc m
                          d = u { Data.Time.utctDay = Data.Time.addGregorianYearsClip n (Data.Time.utctDay u) }
                      in VDateTimeLit (utcToDateTime d)
                    y -> VDateTimeAddYears x y
            x ->
                VPrim $ \case
                    y                -> VDateTimeAddYears x y

        DateTimeAddMonths -> VPrim $ \case
            x@(VIntegerLit n) ->
                VPrim $ \case
                    VDateTimeLit m ->
                      let u = dateTimeToUtc m
                          d = u { Data.Time.utctDay = Data.Time.addGregorianMonthsClip n (Data.Time.utctDay u) }
                      in VDateTimeLit (utcToDateTime d)
                    y -> VDateTimeAddMonths x y
            x ->
                VPrim $ \case
                    y                -> VDateTimeAddMonths x y

        DateTimeAddDays -> VPrim $ \case
            x@(VIntegerLit n) ->
                VPrim $ \case
                    VDateTimeLit m ->
                      let u = dateTimeToUtc m
                          d = u { Data.Time.utctDay = Data.Time.addDays n (Data.Time.utctDay u) }
                      in VDateTimeLit (utcToDateTime d)
                    y -> VDateTimeAddDays x y
            x ->
                VPrim $ \case
                    y                -> VDateTimeAddDays x y

        DateTimeFromWeek -> VPrim $ \case
            a1@(VIntegerLit y) -> VPrim $ \case
              a2@(VNonZeroLit (NonZeroC w)) -> VPrim $ \case
                VNonZeroLit (NonZeroC d) ->
                  let dy = Data.Time.Calendar.WeekDate.fromWeekDate y (fromIntegral w) (fromIntegral d)
                  in VDateTimeLit (utcToDateTime (Data.Time.UTCTime dy 0))
                a3 -> VDateTimeFromWeek a1 a2 a3
              a2 -> VPrim $ \a3 -> VDateTimeFromWeek a1 a2 a3
            a1 -> VPrim $ \a2 -> VPrim $ \a3 -> VDateTimeFromWeek a1 a2 a3

        DateTimeToWeek -> VPrim $ \case
            VDateTimeLit n ->
               let u = dateTimeToUtc n
                   (y,w,d) = Data.Time.Calendar.WeekDate.toWeekDate (Data.Time.utctDay u)
               in VRecordLit (Map.unorderedFromList
                    [ ("year", VIntegerLit y)
                    , ("week", VNonZeroLit (mkNonZeroUnsafe (fromIntegral w)) )
                    , ("day", VNaturalLit (fromIntegral d-1))
                    ])
            n             -> VDateTimeToWeek n

        DateTimeToDate -> VPrim $ \case
            a1@(VIntegerLit y) -> VPrim $ \case
              a2@(VNonZeroLit (NonZeroC m)) -> VPrim $ \case
                a3@(VNonZeroLit (NonZeroC d)) -> VPrim $ \case
                  a4@(VNaturalLit hh) -> VPrim $ \case
                    a5@(VNaturalLit mm) -> VPrim $ \case
                      VNaturalLit ss ->
                        let dy = Data.Time.fromGregorian y (fromIntegral m) (fromIntegral d)
                            hms = (min 23 hh * 3600) + (min 59 mm * 60) + (min 59 ss)
                        in VDateTimeLit (utcToDateTime (Data.Time.UTCTime dy (fromIntegral hms)))
                      a6 -> VDateTimeToDate a1 a2 a3 a4 a5 a6
                    a5 -> VPrim $ \a6 -> VDateTimeToDate a1 a2 a3 a4 a5 a6
                  a4 -> VPrim $ \a5 -> VPrim $ \a6 -> VDateTimeToDate a1 a2 a3 a4 a5 a6
                a3 -> VPrim $ \a4 -> VPrim $ \a5 -> VPrim $ \a6 -> VDateTimeToDate a1 a2 a3 a4 a5 a6
              a2 -> VPrim $ \a3 -> VPrim $ \a4 -> VPrim $ \a5 -> VPrim $ \a6 -> VDateTimeToDate a1 a2 a3 a4 a5 a6
            a1 -> VPrim $ \a2 -> VPrim $ \a3 -> VPrim $ \a4 -> VPrim $ \a5 -> VPrim $ \a6 -> VDateTimeToDate a1 a2 a3 a4 a5 a6

        DateTimeFromDate -> VPrim $ \case
            VDateTimeLit n ->
               let u = dateTimeToUtc n
                   (y,m,d) = Data.Time.toGregorian (Data.Time.utctDay u)
                   (hh,ms) = fromIntegral (truncate (Data.Time.utctDayTime u) :: Integer) `divMod` 3600
                   (mm,ss) = ms `divMod` (60 :: Integer)
               in VRecordLit (Map.unorderedFromList
                    [ ("year", VIntegerLit y)
                    , ("month", VNonZeroLit (mkNonZeroUnsafe (fromIntegral m)))
                    , ("day", VNonZeroLit (mkNonZeroUnsafe (fromIntegral d)))
                    , ("hour", VNaturalLit (fromIntegral hh))
                    , ("minute", VNaturalLit (fromIntegral mm))
                    , ("second", VNaturalLit (fromIntegral ss))
                    ])
            n             -> VDateTimeFromDate n

        DateTimeLastDayOfMonth -> VPrim $ \case
            a1@(VIntegerLit y) -> VPrim $ \case
              VNonZeroLit (NonZeroC m) ->
                  let dy = Data.Time.Calendar.gregorianMonthLength y (fromIntegral m)
                  in VNonZeroLit (mkNonZeroUnsafe (fromIntegral dy))
              a2 -> VDateTimeLastDayOfMonth a1 a2
            a1 -> VPrim $ \a2 -> VDateTimeLastDayOfMonth a1 a2

        DateTimeGetJulianDay -> VPrim $ \case
            VDateTimeLit n ->
               let u = dateTimeToUtc n
                   (_,d) = Data.Time.Calendar.OrdinalDate.toOrdinalDate (Data.Time.utctDay u)
               in VNonZeroLit (mkNonZeroUnsafe (fromIntegral d))
            n             -> VDateTimeGetJulianDay n

        DateTimeSetJulianDay -> VPrim $ \case
            x@(VIntegerLit m) ->
                VPrim $ \case
                    VNonZeroLit (NonZeroC n) ->
                      let d = Data.Time.UTCTime (Data.Time.Calendar.OrdinalDate.fromOrdinalDate m (fromIntegral n)) 0
                      in VDateTimeLit (utcToDateTime d)
                    y -> VDateTimeSetJulianDay x y
            x ->
                VPrim $ \case
                    y                -> VDateTimeSetJulianDay x y


        Regex ->
            VRegex

        RegexLit cs -> VRegexLit cs

        RegexShow -> VPrim $ \case
            VRegexLit (RegexC y) ->
              VTextLit (VChunks [] y)
            n             -> VRegexShow n


        RegexMatch -> VPrim $ \case
            x@(VRegexLit (RegexC m)) ->
                VPrim $ \case
                    VTextLit (VChunks [] n) ->
                      let r = compileRegexUnsafe m
                      in VBoolLit (n RH.=~ r)
                    y -> VRegexMatch x y
            x ->
                VPrim $ \case
                    y                -> VRegexMatch x y

        RegexScan -> VPrim $ \case
            x@(VRegexLit (RegexC m)) ->
                let emptyInnerList = VList VText
                    emptyList = let f xs = VListLit (Just (VList (VRecord (Map.unorderedFromList xs)))) mempty
                                in f [("_1", VText), ("_2", emptyInnerList)]
                in VPrim $ \case
                    y@(VTextLit (VChunks [] txt)) ->
                       VPrim $ \case
                         VNonZeroLit (NonZeroC i) ->
                            let r = compileRegexUnsafe m
                                rs = RH.scan r txt
                            in case take (fromIntegral i) rs of
                                 [] -> emptyList
                                 as@(_:_) ->
                                   let ret = flip map as $ \(w,ys') ->
                                               let zzzz = case ys' of
                                                            [] -> VListLit (Just emptyInnerList) mempty
                                                            ys@(_:_) -> VListLit Nothing (Sequence.fromList (map (\a -> VTextLit (VChunks [] a)) ys))
                                               in VRecordLit (Map.unorderedFromList [("_1", VTextLit (VChunks [] w)), ("_2", zzzz )])
                                   in VListLit Nothing (Sequence.fromList ret)
                         z -> VRegexScan x y z
                    y ->
                        VPrim $ \case
                          z -> VRegexScan x y z
            x ->
                VPrim $ \case
                    y -> VPrim $ \case
                          z -> VRegexScan x y z


        RegexSplit -> VPrim $ \case
            x@(VRegexLit (RegexC m)) ->
                let emptyList = VListLit (Just (VList VText)) mempty
                in VPrim $ \case
                    y@(VTextLit (VChunks [] txt)) ->
                       VPrim $ \case
                         VNonZeroLit (NonZeroC i) ->
                           let r = compileRegexUnsafe m
                           in case take (fromIntegral i) (RH.split r txt) of
                                [] -> emptyList
                                as@(_:_) -> VListLit Nothing (Sequence.fromList (map (\a -> VTextLit (VChunks [] a)) as))
                         z -> VRegexSplit x y z
                    y ->
                        VPrim $ \case
                          z -> VRegexSplit x y z
            x ->
                VPrim $ \case
                    y -> VPrim $ \case
                          z -> VRegexSplit x y z

        RegexReplace -> VPrim $ \case
            x@(VRegexLit (RegexC m)) ->
                  VPrim $ \case
                    y@(VTextLit (VChunks [] txt)) ->
                      VPrim $ \case
                         VTextLit (VChunks [] p) ->
                           let r = compileRegexUnsafe m
                               t = RH.gsub r txt p
                           in VTextLit (VChunks [] t)
                         z -> VRegexReplace x y z
                    y ->
                       VPrim $ \case
                          z -> VRegexReplace x y z
            x ->
                VPrim $ \case
                    y                -> VPrim $ \case
                                          z -> VRegexReplace x y z

        RegexReplix -> VPrim $ \case
            x@(VRegexLit (RegexC m)) ->
                  VPrim $ \case
                    y@(VLam VText cl) ->
                       VPrim $ \case
                         VTextLit (VChunks [] p) ->
                           let r = compileRegexUnsafe m
                               ans = let ff d = case instantiate cl (VTextLit (VChunks [] d)) of
                                                  VTextLit (VChunks [] tt) -> tt
                                                  _ -> error "eval: replix is messed up"
                                     in RH.gsub r (\(d :: Text) (_ :: [Text]) -> ff d) p
                           in VTextLit (VChunks [] ans)
                         z -> VRegexReplix x y z

                    y ->
                       VPrim $ \case
                          z -> VRegexReplix x y z
            x ->
                VPrim $ \case
                    y                -> VPrim $ \case
                                          z -> VRegexReplix x y z


        RegexParse -> VPrim $ \case
            VTextLit (VChunks [] m) ->
               case compileRegex m of
                 Left _ -> VNone VRegex
                 Right _ -> VSome (VRegexLit (RegexC m))
            y -> VRegexParse y

        RegexToText -> VPrim $ \case
            VRegexLit (RegexC y) ->
              VTextLit (VChunks [] y)
            n             -> VRegexToText n



        Rational ->
            VRational

        RationalLit r -> VRationalLit r

        RationalShow -> VPrim $ \case
            VRationalLit r ->
              VTextLit (VChunks [] (Syntax.showDhallRational r))
            n             -> VRationalShow n

        RationalFromDouble -> VPrim $ \case
            x@(VDoubleLit (DhallDouble m)) ->
                VPrim $ \case
                    VDoubleLit (DhallDouble n) ->
                       VRationalLit (Data.Ratio.approxRational m n)
                    y -> VRationalFromDouble x y
            x ->
                VPrim $ \case
                    y                -> VRationalFromDouble x y


        RationalToDouble -> VPrim $ \case
            VRationalLit m -> VDoubleLit (DhallDouble (realToFrac m))
            n -> VRationalToDouble n

        RationalFromRational -> VPrim $ \case
            VRationalLit r -> VRecordLit (Map.unorderedFromList [ ("num", VIntegerLit (Data.Ratio.numerator r))
                                                                , ("den", VNonZeroLit (Syntax.mkNonZeroUnsafe (fromIntegral (Data.Ratio.denominator r))))
                                                                ])
            x -> VRationalFromRational x

        RationalParse -> VPrim $ \case
            VTextLit (VChunks [] t) ->
              case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.rationalLiteral <* Text.Megaparsec.eof) "?" t of
                Left _ -> VNone VRational
                Right r -> VSome (VRationalLit r)
            n             -> VRationalParse n

        RationalPercent t u ->
            case (eval env t, eval env u) of
                (VIntegerLit 0, VNonZeroLit _           ) -> VRationalLit (0 % 1)
                (VIntegerLit m, VNonZeroLit (NonZeroC n)) -> VRationalLit (m % fromIntegral n)
                (t'           , u'                      ) -> VRationalPercent t' u'


        Natural ->
            VNatural
        NaturalLit n ->
            VNaturalLit n
        NaturalFold ->
            VPrim $ \n ->
            VPrim $ \natural ->
            VPrim $ \succ ->
            VPrim $ \zero ->
            let inert = VNaturalFold n natural succ zero
            in  case zero of
                VPrimVar -> inert
                _ -> case succ of
                    VPrimVar -> inert
                    _ -> case natural of
                        VPrimVar -> inert
                        _ -> case n of
                            VNaturalLit n' ->
                                -- Use an `Integer` for the loop, due to the
                                -- following issue:
                                --
                                -- https://github.com/ghcjs/ghcjs/issues/782
                                let go !acc 0 = acc
                                    go  acc m = go (vApp succ acc) (m - 1)
                                in  go zero (fromIntegral n' :: Integer)
                            _ -> inert
        NaturalBuild ->
            VPrim $ \case
                VPrimVar ->
                    VNaturalBuild VPrimVar
                t ->       t
                    `vApp` VNatural
                    `vApp` VHLam (Typed "n" VNatural) (\n -> vNaturalPlus n (VNaturalLit 1))
                    `vApp` VNaturalLit 0

        NaturalIsZero -> VPrim $ \case
            VNaturalLit n -> VBoolLit (n == 0)
            n             -> VNaturalIsZero n
        NaturalEven -> VPrim $ \case
            VNaturalLit n -> VBoolLit (even n)
            n             -> VNaturalEven n
        NaturalOdd -> VPrim $ \case
            VNaturalLit n -> VBoolLit (odd n)
            n             -> VNaturalOdd n
        NaturalToInteger -> VPrim $ \case
            VNaturalLit n -> VIntegerLit (fromIntegral n)
            n             -> VNaturalToInteger n
        NaturalShow -> VPrim $ \case
            VNaturalLit n -> VTextLit (VChunks [] (Text.pack (show n)))
            n             -> VNaturalShow n
        NaturalParse -> VPrim $ \case
            VTextLit (VChunks [] t) ->
              case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.naturalLiteral <* Text.Megaparsec.eof) "?" t of
                Left _ -> VNone VNatural
                Right r -> VSome (VNaturalLit r)
            n             -> VNaturalParse n

        NaturalToBits -> VPrim $ \case
            VNaturalLit n ->
              let mx = if n <= 0 then 0 else truncate (log (fromIntegral n) / log 2 :: Double)
                  bs = reverse $ map (VBoolLit . Data.Bits.testBit n) [ 0 .. mx ]
              in VListLit Nothing (Sequence.fromList bs)
            n             -> VNaturalToBits n

        NaturalSubtract -> VPrim $ \case
            VNaturalLit 0 ->
                VHLam NaturalSubtractZero id
            x@(VNaturalLit m) ->
                VPrim $ \case
                    VNaturalLit n
                        | n >= m ->
                            -- Use an `Integer` for the subtraction, due to the
                            -- following issue:
                            --
                            -- https://github.com/ghcjs/ghcjs/issues/782
                            VNaturalLit (fromIntegral (subtract (fromIntegral m :: Integer) (fromIntegral n :: Integer)))
                        | otherwise -> VNaturalLit 0
                    y -> VNaturalSubtract x y
            x ->
                VPrim $ \case
                    VNaturalLit 0    -> VNaturalLit 0
                    y | conv env x y -> VNaturalLit 0
                    y                -> VNaturalSubtract x y
        NaturalGcd -> VPrim $ \case
            x@(VNaturalLit m) ->
                VPrim $ \case
                    VNaturalLit n
                         -> VNaturalLit (gcd m n)
                    y -> VNaturalGcd x y
            x ->
                VPrim $ \case
                    y                -> VNaturalGcd x y

        NaturalPlus t u ->
            vNaturalPlus (eval env t) (eval env u)
        NaturalTimes t u ->
            case (eval env t, eval env u) of
                (VNaturalLit 1, u'           ) -> u'
                (t'           , VNaturalLit 1) -> t'
                (VNaturalLit 0, _            ) -> VNaturalLit 0
                (_            , VNaturalLit 0) -> VNaturalLit 0
                (VNaturalLit m, VNaturalLit n) -> VNaturalLit (m * n)
                (t'           , u'           ) -> VNaturalTimes t' u'
        Integer ->
            VInteger
        IntegerLit n ->
            VIntegerLit n

        IntegerAdd -> VPrim $ \case
            x@(VIntegerLit 0) ->
                VPrim $ \case
                    n@VIntegerLit {} -> n
                    y -> VIntegerAdd x y
            x@(VIntegerLit m) ->
                VPrim $ \case
                    VIntegerLit 0 -> x
                    VIntegerLit n -> VIntegerLit (m + n)
                    y -> VIntegerAdd x y
            x ->
                VPrim $ \case
                    y -> VIntegerAdd x y

        IntegerMultiply -> VPrim $ \case
            x@(VIntegerLit 1) ->
                VPrim $ \case
                    n@VIntegerLit {} -> n
                    y -> VIntegerMultiply x y

            x@(VIntegerLit m) ->
                VPrim $ \case
                    VIntegerLit 1 -> x
                    VIntegerLit n -> VIntegerLit (m * n)
                    y -> VIntegerMultiply x y
            x ->
                VPrim $ \case
                    y -> VIntegerMultiply x y

        IntegerAnd -> VPrim $ \case
            x@(VIntegerLit 0) ->
                VPrim $ \case
                    VIntegerLit {} -> x
                    y -> VIntegerAnd x y
            x@(VIntegerLit m) ->
                VPrim $ \case
                    z@(VIntegerLit 0) -> z
                    VIntegerLit n -> VIntegerLit (m Data.Bits..&. n)
                    y -> VIntegerAnd x y
            x ->
                VPrim $ \case
                    y -> VIntegerAnd x y

        IntegerXor -> VPrim $ \case
            x@(VIntegerLit 0) ->
                VPrim $ \case
                    n@VIntegerLit {} -> n
                    y -> VIntegerXor x y
            x@(VIntegerLit m) ->
                VPrim $ \case
                    VIntegerLit 0 -> x
                    VIntegerLit n -> VIntegerLit (Data.Bits.xor m n)
                    y -> VIntegerXor x y
            x ->
                VPrim $ \case
                    y -> VIntegerXor x y

        IntegerClamp ->
            VPrim $ \case
                VIntegerLit n
                    | 0 <= n    -> VNaturalLit (fromInteger n)
                    | otherwise -> VNaturalLit 0
                n -> VIntegerClamp n
        IntegerNegate ->
            VPrim $ \case
                VIntegerLit n -> VIntegerLit (negate n)
                n             -> VIntegerNegate n
        IntegerShow ->
            VPrim $ \case
                VIntegerLit n
                    | 0 <= n    -> VTextLit (VChunks [] (Text.pack ('+':show n)))
                    | otherwise -> VTextLit (VChunks [] (Text.pack (show n)))
                n -> VIntegerShow n

        IntegerParse ->
            VPrim $ \case
                VTextLit (VChunks [] t) ->
                  case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.integerLiteral <* Text.Megaparsec.eof) "?" t of
                    Left _ -> VNone VInteger
                    Right r -> VSome (VIntegerLit r)
                n -> VIntegerParse n

        IntegerToDouble ->
            VPrim $ \case
                VIntegerLit n -> VDoubleLit (DhallDouble (read (show n)))
                -- `(read . show)` is used instead of `fromInteger`
                -- because `read` uses the correct rounding rule.
                -- See https://gitlab.haskell.org/ghc/ghc/issues/17231.
                n             -> VIntegerToDouble n
        Double ->
            VDouble
        DoubleLit n ->
            VDoubleLit n
        DoubleShow ->
            VPrim $ \case
                VDoubleLit (DhallDouble n) -> VTextLit (VChunks [] (Text.pack (show n)))
                n                          -> VDoubleShow n

        DoubleParse ->
            VPrim $ \case
                VTextLit (VChunks [] t) ->
                  case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.doubleLiteral <* Text.Megaparsec.eof) "?" t of
                    Left _ -> VNone VDouble
                    Right r -> VSome (VDoubleLit (DhallDouble r))
                n -> VDoubleParse n

        Text ->
            VText
        TextLit cs ->
            case evalChunks cs of
                VChunks [("", t)] "" -> t
                vcs                  -> VTextLit vcs
        TextAppend t u ->
            eval env (TextLit (Chunks [("", t), ("", u)] ""))
        TextShow ->
            VPrim $ \case
                VTextLit (VChunks [] x) -> VTextLit (VChunks [] (textShow x))
                t                       -> VTextShow t

        TextToLower ->
            VPrim $ \case
                VTextLit (VChunks [] x) -> VTextLit (VChunks [] (Text.toLower x))
                t                       -> VTextToLower t
        TextToUpper ->
            VPrim $ \case
                VTextLit (VChunks [] x) -> VTextLit (VChunks [] (Text.toUpper x))
                t                       -> VTextToUpper t

        TextUnpack ->
            VPrim $ \case
                VTextLit (VChunks [] x) ->
                  case map Data.Char.ord (Text.unpack x) of
                    [] -> VListLit (Just (VList VNatural)) mempty
                    as -> VListLit Nothing (Sequence.fromList (map (VNaturalLit . fromIntegral) as))
                t                       -> VTextUnpack t

        TextPack ->
            VPrim $ \case
                t@(VListLit _ xs) ->
                  case flip traverse (toList xs) $ \case
                              VNaturalLit n -> Just (Data.Char.chr (min 0x10FFFF (fromIntegral n)))
                              _ -> Nothing of
                    Nothing -> VTextPack t
                    Just ss -> VTextLit (VChunks [] (Text.pack ss))
                t -> VTextPack t

        TextToList ->
            VPrim $ \case
                VTextLit (VChunks [] x) ->
                  case Text.chunksOf 1 x of
                    [] -> VListLit (Just (VList VText)) mempty
                    xs -> VListLit Nothing (Sequence.fromList (map (VTextLit . VChunks []) xs))
                t                       -> VTextToList t
        TextLength ->
            VPrim $ \case
                VTextLit (VChunks [] x) -> VNaturalLit (fromIntegral (Text.length x))
                t                       -> VTextLength t

        TextCompare ->
            VPrim $ \case
              m@(VBoolLit ci) ->
                VPrim $ \case
                    n@(VTextLit (VChunks [] xs)) ->
                       VPrim $ \case
                          VTextLit (VChunks [] ys) ->
                            VNaturalLit (fromIntegral (fromEnum (Data.Ord.comparing (if ci then Text.toLower else id) xs ys)))
                          o                       -> VTextCompare m n o
                    n -> VPrim $ VTextCompare m n
              m -> VPrim $ \n -> VPrim $ VTextCompare m n

        List ->
            VPrim VList
        ListLit ma ts ->
            VListLit (fmap (eval env) ma) (fmap (eval env) ts)
        ListAppend t u ->
            vListAppend (eval env t) (eval env u)
        ListBuild ->
            VPrim $ \a ->
            VPrim $ \case
                VPrimVar ->
                    VListBuild a VPrimVar
                t ->       t
                    `vApp` VList a
                    `vApp` VHLam (Typed "a" a) (\x ->
                           VHLam (Typed "as" (VList a)) (\as ->
                           vListAppend (VListLit Nothing (pure x)) as))
                    `vApp` VListLit (Just (VList a)) mempty

        ListFold ->
            VPrim $ \a ->
            VPrim $ \as ->
            VPrim $ \list ->
            VPrim $ \cons ->
            VPrim $ \nil ->
            let inert = VListFold a as list cons nil
            in  case nil of
                VPrimVar -> inert
                _ -> case cons of
                    VPrimVar -> inert
                    _ -> case list of
                        VPrimVar -> inert
                        _ -> case a of
                            VPrimVar -> inert
                            _ -> case as of
                                VListLit _ as' ->
                                    foldr' (\x b -> cons `vApp` x `vApp` b) nil as'
                                _ -> inert
        ListLength ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as -> VNaturalLit (fromIntegral (Sequence.length as))
                as            -> VListLength a as
        ListHead ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as ->
                    case Sequence.viewl as of
                        y :< _ -> VSome y
                        _      -> VNone a
                as ->
                    VListHead a as
        ListLast ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as ->
                    case Sequence.viewr as of
                        _ :> t -> VSome t
                        _      -> VNone a
                as -> VListLast a as

        ListIndexed ->
            VPrim $ \ a ->
            VPrim $ \case
                VListLit _ as ->
                    let a' =
                            if null as
                            then Just (VList (VRecord (Map.unorderedFromList [("index", VNatural), ("value", a)])))
                            else Nothing

                        as' =
                            Sequence.mapWithIndex
                                (\i t ->
                                    VRecordLit
                                        (Map.unorderedFromList
                                            [ ("index", VNaturalLit (fromIntegral i))
                                            , ("value", t)
                                            ]
                                        )
                                )
                                as

                        in  VListLit a' as'
                t ->
                    VListIndexed a t
        ListReverse ->
            VPrim $ \ ~a ->
            VPrim $ \case
                VListLit t as | null as ->
                    VListLit t as
                VListLit _ as ->
                    VListLit Nothing (Sequence.reverse as)
                t ->
                    VListReverse a t

        ListPermutations ->
            VPrim $ \ ~a ->
            VPrim $ \case
                VListLit t as | null as ->
                    VListLit (fmap VList t) as
                VListLit _ as ->
                    let ff = map (VListLit Nothing . Sequence.fromList)
                    in VListLit Nothing (Sequence.fromList . ff . perms . toList $ as)
                t ->
                    VListPermutations a t

        ListChoose ->
          VPrim $ \ ~a ->
          VPrim $ \case
            x@(VNaturalLit m) ->
                VPrim $ \case
                    VListLit _ ns
                         -> case choose (toList ns) (fromIntegral m) of
                              [] -> VListLit (Just (VList (VList a))) mempty
                              o -> VListLit Nothing
                                     (Sequence.fromList
                                       (map
                                         (\z -> VListLit (if null z then Just (VList a) else Nothing) (Sequence.fromList z))
                                       o)
                                     )

                    y -> VListChoose a x y
            x ->
                VPrim $ \case
                    y                -> VListChoose a x y

        ListFixed ->
            VPrim $ \ a -> VPrim $ \ b -> VListFixed a b
        ListFixedLit t ts ->
            VListFixedLit (eval env t) (fmap (eval env) ts)

        ListFixedFromList ->
            VPrim $ \n ->
              case getSSCntVal n of
                Right (NonZeroC cnt) ->
                  VPrim $ \ a ->
                    VPrim $ \def ->
                      VPrim $ \case
                         VListLit _ as ->
                            let (w,ws) =
                                   case Sequence.viewl as of
                                     EmptyL -> (def, Sequence.replicate (fromIntegral (cnt-1)) def)
                                     z :< zs ->
                                       let df = 1 + length zs - fromIntegral cnt
                                       in (z,) $ case compare df 0 of
                                                  LT -> zs <> Sequence.replicate (abs df) def
                                                  EQ -> zs
                                                  GT -> Sequence.take (fromIntegral (cnt-1)) zs
                            in VListFixedLit w ws
                         as -> VListFixedFromList n a def as
                Left _ -> VPrim $ \a -> VPrim $ \def -> VPrim $ \as -> VListFixedFromList n a def as

        ListFixedToList ->
            VPrim $ \ ~n ->
            VPrim $ \ ~a ->
            VPrim $ \case
                VListFixedLit b bs -> VListLit Nothing (b Sequence.:<| bs)
                as                 -> VListFixedToList n a as


        ListFixedHead ->
            VPrim $ \ ~n ->
            VPrim $ \ ~a ->
            VPrim $ \case
                VListFixedLit b _bs -> b
                x                   -> VListFixedHead n a x

        ListFixedTail ->
            VPrim $ \ ~n ->
            VPrim $ \ a ->
            VPrim $ \case
                VListFixedLit _b bs
                  | null bs   -> VListLit (Just (VList a)) mempty
                  | otherwise -> VListLit Nothing bs
                x             -> VListFixedTail n a x

        Sym t -> VSym t

        SZ -> VSZ
        SS -> VPrim VSS

        SymLit t -> VSymLit t

        SymFromText ->
           VPrim $ \case
             VTextLit (VChunks [] t) -> VSym t
             n -> VSymFromText n

        SymToText ->
           VPrim $ \case
             VSym t -> VTextLit (VChunks [] t)
             n -> VSymToText n

        SZLit -> VSZLit
        SSLit t -> VSSLit (eval env t)
        SSFromNonZero ->
           VPrim $ \case
             VNonZeroLit (NonZeroC n) ->
                foldr (const VSS) VSZ [1 .. n-1]
             n -> VSSFromNonZero n

        SSToNonZero ->
           VPrim $ \case
             VSZ -> VNonZeroLit (NonZeroC 1)
             n@(VSS _) ->
               case getSSCntVal n of
                 Left _ -> VSSToNonZero n
                 Right cnt -> VNonZeroLit cnt
             n -> VSSToNonZero n

        SSToNatural ->
           VPrim $ \case
             VSZ -> VNaturalLit 1
             n@(VSS _) ->
               case getSSCntVal n of
                 Left _ -> VSSToNatural n
                 Right cnt -> VNaturalLit (unNonZero cnt)
             n -> VSSToNatural n

        SSAdd ->
           VPrim $ \case
             m@VSZ ->
               VPrim $ \case
                 VSZ -> VSS VSZ
                 n@(VSS _) -> VSS n
                 n -> VSSAdd m n
             m@(VSS _) ->
               VPrim $ \case
                 VSZ -> VSS m
                 n@(VSS _) ->
                   case (Data.Function.on (+) unNonZero) <$> getSSCntVal m <*> getSSCntVal n of
                     Left _ -> VSSAdd m n
                     Right cnt -> foldr (const VSS) VSZ [1 .. cnt-1]
                 n -> VSSAdd m n
             m -> VPrim $ \n -> VSSAdd m n

        SSSubtract ->
           VPrim $ \case
             m@VSZ ->
               VPrim $ \case
                 n@VSZ -> VSSSubtract m n
                 VSS n -> n
                 n -> VSSSubtract m n
             m@(VSS _) ->
               VPrim $ \case
                 n@VSZ -> VSSSubtract m n
                 n@(VSS _) ->
                   case (Data.Function.on (,) unNonZero) <$> getSSCntVal m <*> getSSCntVal n of
                     Left _ -> VSSSubtract m n
                     Right (c1,c2) -> if c1 < c2 then foldr (const VSS) VSZ [1 .. c2-c1-1]
                                  else VSSSubtract m n
                 n -> VSSSubtract m n
             m -> VPrim $ \n -> VSSSubtract m n

-- todo: VProof vs VProofLit?
        SSEqual ->
           VPrim $ \case
             m@VSZ ->
               VPrim $ \case
                 VSZ -> VProof (VSym "SS/equal: SZ == SZ")
                 VSS _ -> VPVoid (VSym "SS/equal: SZ /= SS")
                 n -> VSSEqual m n
             m@(VSS _) ->
               VPrim $ \case
                 VSZ -> VPVoid (VSym "SS/equal: SS /= SZ")
                 n@(VSS _) ->
                   case (,) <$> getSSCntVal m <*> getSSCntVal n of
                     Left _ -> VSSEqual m n
                     Right (NonZeroC c1,NonZeroC c2) ->
                        let x1 = Text.pack (show c1)
                            x2 = Text.pack (show c2)
                        in if c1 == c2 then VProof (VSym ("SS/equal: " <> x1 <> " == " <> x2))
                           else VPVoid (VSym ("SS/equal: " <> x1 <> " /= " <> x2))
                 n -> VSSEqual m n
             m -> VPrim $ \n -> VSSEqual m n

-- todo: VProof vs VProofLit?
        SSLessThan ->
           VPrim $ \case
             m@VSZ ->
               VPrim $ \case
                 VSZ -> VPVoid (VSym "SS/lessThan: SZ is not less than SZ")
                 VSS _ -> VProof (VSym "SS/lessThan: SZ < SS")
                 n -> VSSLessThan m n
             m@(VSS _) ->
               VPrim $ \case
                 VSZ -> VPVoid (VSym "SS/lessThan: SS is not less than SZ")
                 n@(VSS _) ->
                   case (,) <$> getSSCntVal m <*> getSSCntVal n of
                     Left _ -> VSSLessThan m n
                     Right (NonZeroC c1,NonZeroC c2) ->
                        let x1 = Text.pack (show c1)
                            x2 = Text.pack (show c2)
                        in if c1 < c2 then VProof (VSym ("SS/lessThan: " <> x1 <> " < " <> x2))
                           else VPVoid (VSym ("SS/lessThan: " <> x1 <> " is not less than " <> x2))
                 n -> VSSLessThan m n
             m -> VPrim $ \n -> VSSLessThan m n

        Proof ->
          VPrim $ \case
--            msg@(VSym _) -> VProof msg
            m -> -- trace ("Eval: PVoid: prefer VSym eg ^^\"failed cos...\" m=" ++ dumpVal m) $
                 VProof m

        ProofLit -> VProofLit

        ProofToBool ->
           VPrim $ \case
             VProof _ -> VBoolLit True
             VPVoid _ -> VBoolLit False
             m -> VProofToBool m

        ProofFromBool ->
           VPrim $ \case
{-
             m@(VSym _) ->
               VPrim $ \case
                 VBoolLit True -> VProof m
                 VBoolLit False -> VPVoid m
                 n -> VProofFromBool m n
-}
             m -> -- we allow any type thru: it just means the errors on PVoid are not as obvious: PVoid Bool tells us less than eg PVoid ^^"index is greater than size of array"
               --trace ("Eval: ProofFromBool: prefer VSym eg ^^\"failed cos...\" m=" ++ dumpVal m) $
               VPrim $ \case
                 VBoolLit True -> VProof m
                 VBoolLit False -> VPVoid m
                 n -> VProofFromBool m n

        PVoid ->
           VPrim $ \case
--             m@(VSym _) -> VPVoid m
             m -> -- trace ("Eval: PVoid: prefer VSym eg ^^\"failed cos...\" m=" ++ dumpVal m) $
                  VPVoid m

        PVoidUndefined ->
           VPrim $ VPVoidUndefined

        PVoidError ->
           VPrim $ \a ->
             VPrim $ \b -> VPVoidError a b

        PVoidKindUndefined ->
           VPrim $ VPVoidKindUndefined

        Optional ->
            VPrim VOptional
        Some t ->
            VSome (eval env t)
        None ->
            VPrim $ \ ~a -> VNone a
        Record kts ->
            VRecord (Map.sort (eval env . recordFieldValue <$> kts))
        RecordLit kts ->
            VRecordLit (Map.sort (eval env . recordFieldValue <$> kts))
        Union kts ->
            VUnion (Map.sort (fmap (fmap (eval env)) kts))
        Combine mk t u ->
            vCombine mk (eval env t) (eval env u)
        CombineTypes t u ->
            vCombineTypes (eval env t) (eval env u)
        Prefer _ t u ->
            vPrefer env (eval env t) (eval env u)
        RecordCompletion t u ->
            eval env (Annot (Prefer PreferFromCompletion (Field t "default") u) (Field t "Type"))
        Merge x y ma ->
            case (eval env x, eval env y, fmap (eval env) ma) of
                (VRecordLit m, VInject _ k mt, _)
                    | Just f <- Map.lookup k m -> maybe f (vApp f) mt
                    | otherwise                -> error errorMsg
                (VRecordLit m, VSome t, _)
                    | Just f <- Map.lookup "Some" m -> vApp f t
                    | otherwise                     -> error errorMsg
                (VRecordLit m, VNone _, _)
                    | Just t <- Map.lookup "None" m -> t
                    | otherwise                     -> error errorMsg
                (x', y', ma') -> VMerge x' y' ma'
        ToMap x ma ->
            case (eval env x, fmap (eval env) ma) of
                (VRecordLit m, ma'@(Just _)) | null m ->
                    VListLit ma' Sequence.empty
                (VRecordLit m, _) ->
                    let entry (k, v) =
                            VRecordLit
                                (Map.unorderedFromList
                                    [ ("mapKey", VTextLit $ VChunks [] k)
                                    , ("mapValue", v)
                                    ]
                                )

                        s = (Sequence.fromList . map entry . Map.toAscList) m

                    in  VListLit Nothing s
                (x', ma') ->
                    VToMap x' ma'
        Field t k ->
            vField (eval env t) k
        Project t (Left ks) ->
            vProjectByFields env (eval env t) (Dhall.Set.sort ks)
        Project t (Right e) ->
            case eval env e of
                VRecord kts ->
                    eval env (Project t (Left (Dhall.Set.fromSet (Map.keysSet kts))))
                e' ->
                    VProject (eval env t) (Right e')
        Assert t ->
            VAssert (eval env t)
        Equivalent t u ->
            VEquivalent (eval env t) (eval env u)
        e@With{} ->
            eval env (Syntax.desugarWith e)
        Note _ e ->
            eval env e
        ImportAlt t _ ->
            eval env t
        Embed a ->
            VEmbed a
  where
    evalChunks :: Chunks Void a -> VChunks a
    evalChunks (Chunks xys z) = foldr' cons nil xys
      where
        cons (x, t) vcs =
            case eval env t of
                VTextLit vcs' -> VChunks [] x <> vcs' <> vcs
                t'            -> VChunks [(x, t')] mempty <> vcs

        nil = VChunks [] z
    {-# INLINE evalChunks #-}


eqListBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqListBy f = go
  where
    go (x:xs) (y:ys) | f x y = go xs ys
    go [] [] = True
    go _  _  = False
{-# INLINE eqListBy #-}

eqMapsBy :: Ord k => (v -> v -> Bool) -> Map k v -> Map k v -> Bool
eqMapsBy f mL mR =
    Map.size mL == Map.size mR
    && eqListBy eq (Map.toAscList mL) (Map.toAscList mR)
  where
    eq (kL, vL) (kR, vR) = kL == kR && f vL vR
{-# INLINE eqMapsBy #-}

eqMaybeBy :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Bool
eqMaybeBy f = go
  where
    go (Just x) (Just y) = f x y
    go Nothing  Nothing  = True
    go _        _        = False
{-# INLINE eqMaybeBy #-}

-- | Utility that powers the @Text/show@ built-in
textShow :: Text -> Text
textShow text = "\"" <> Text.concatMap f text <> "\""
  where
    f '"'  = "\\\""
    f '$'  = "\\u0024"
    f '\\' = "\\\\"
    f '\b' = "\\b"
    f '\n' = "\\n"
    f '\r' = "\\r"
    f '\t' = "\\t"
    f '\f' = "\\f"
    f c | c <= '\x1F' = Text.pack (Text.Printf.printf "\\u%04x" (Data.Char.ord c))
        | otherwise   = Text.singleton c

conv :: forall a. Eq a => Environment a -> Val a -> Val a -> Bool
conv !env t0 t0' =
      case (t0, t0') of
        (VConst k, VConst k') ->
            k == k'
        (VVar x i, VVar x' i') ->
            x == x' && i == i'
        (VLam _ (freshClosure -> (x, v, t)), VLam _ t' ) ->
            convSkip x (instantiate t v) (instantiate t' v)
        (VLam _ (freshClosure -> (x, v, t)), VHLam _ t') ->
            convSkip x (instantiate t v) (t' v)
        (VLam _ (freshClosure -> (x, v, t)), t'        ) ->
            convSkip x (instantiate t v) (vApp t' v)
        (VHLam _ t, VLam _ (freshClosure -> (x, v, t'))) ->
            convSkip x (t v) (instantiate t' v)
        (VHLam _ t, VHLam _ t'                    ) ->
            let (x, v) = fresh "x" in convSkip x (t v) (t' v)
        (VHLam _ t, t'                            ) ->
            let (x, v) = fresh "x" in convSkip x (t v) (vApp t' v)
        (t, VLam _ (freshClosure -> (x, v, t'))) ->
            convSkip x (vApp t v) (instantiate t' v)
        (t, VHLam _ t'  ) ->
            let (x, v) = fresh "x" in convSkip x (vApp t v) (t' v)
        (VApp t u, VApp t' u') ->
            conv env t t' && conv env u u'
        (VPi a b, VPi a' (freshClosure -> (x, v, b'))) ->
            conv env a a' && convSkip x (instantiate b v) (instantiate b' v)
        (VPi a b, VHPi (fresh -> (x, v)) a' b') ->
            conv env a a' && convSkip x (instantiate b v) (b' v)
        (VHPi _ a b, VPi a' (freshClosure -> (x, v, b'))) ->
            conv env a a' && convSkip x (b v) (instantiate b' v)
        (VHPi _ a b, VHPi (fresh -> (x, v)) a' b') ->
            conv env a a' && convSkip x (b v) (b' v)
        (VBool, VBool) ->
            True
        (VBoolLit b, VBoolLit b') ->
            b == b'
        (VBoolAnd t u, VBoolAnd t' u') ->
            conv env t t' && conv env u u'
        (VBoolOr t u, VBoolOr t' u') ->
            conv env t t' && conv env u u'
        (VBoolEQ t u, VBoolEQ t' u') ->
            conv env t t' && conv env u u'
        (VBoolNE t u, VBoolNE t' u') ->
            conv env t t' && conv env u u'
        (VBoolIf t u v, VBoolIf t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'

        (VNonZero, VNonZero) ->
            True
        (VNonZeroLit n, VNonZeroLit n') ->
            n == n'
        (VNonZeroShow t, VNonZeroShow t') ->
            conv env t t'
        (VNonZeroClamp t, VNonZeroClamp t') ->
            conv env t t'
        (VNonZeroDiv t u, VNonZeroDiv t' u') ->
            conv env t t' && conv env u u'
        (VNonZeroMod t u, VNonZeroMod t' u') ->
            conv env t t' && conv env u u'
        (VNonZeroLog t u, VNonZeroLog t' u') ->
            conv env t t' && conv env u u'
        (VNonZeroAdd t u, VNonZeroAdd t' u') ->
            conv env t t' && conv env u u'
        (VNonZeroMultiply t u, VNonZeroMultiply t' u') ->
            conv env t t' && conv env u u'
        (VNonZeroToNatural t, VNonZeroToNatural t') ->
            conv env t t'
        (VNonZeroToInteger t, VNonZeroToInteger t') ->
            conv env t t'
        (VNonZeroParse t, VNonZeroParse t') ->
            conv env t t'

        (VDateTime, VDateTime) ->
            True
        (VDateTimeLit n, VDateTimeLit n') ->
            n == n'
        (VDateTimeShow t, VDateTimeShow t') ->
            conv env t t'
        (VDateTimeParse t, VDateTimeParse t') ->
            conv env t t'
        (VDateTimeFromSeconds t, VDateTimeFromSeconds t') ->
            conv env t t'
        (VDateTimeToSeconds t, VDateTimeToSeconds t') ->
            conv env t t'

        (VDateTimeAddYears t u, VDateTimeAddYears t' u') ->
            conv env t t' && conv env u u'
        (VDateTimeAddMonths t u, VDateTimeAddMonths t' u') ->
            conv env t t' && conv env u u'
        (VDateTimeAddDays t u, VDateTimeAddDays t' u') ->
            conv env t t' && conv env u u'

        (VDateTimeFromWeek t u v, VDateTimeFromWeek t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VDateTimeToWeek t, VDateTimeToWeek t') ->
            conv env t t'
        (VDateTimeToDate t u v w x y, VDateTimeToDate t' u' v' w' x' y') ->
            conv env t t' && conv env u u' && conv env v v' && conv env w w' && conv env x x' && conv env y y'
        (VDateTimeFromDate t, VDateTimeFromDate t') ->
            conv env t t'
        (VDateTimeLastDayOfMonth t u, VDateTimeLastDayOfMonth t' u') ->
            conv env t t' && conv env u u'

        (VDateTimeGetJulianDay t, VDateTimeGetJulianDay t') ->
            conv env t t'
        (VDateTimeSetJulianDay t u, VDateTimeSetJulianDay t' u') ->
            conv env t t' && conv env u u'


        (VRegex, VRegex) ->
            True
        (VRegexLit t, VRegexLit t') ->
            t == t'
        (VRegexShow t, VRegexShow t') ->
            conv env t t'
        (VRegexMatch t u, VRegexMatch t' u') ->
            conv env t t' && conv env u u'
        (VRegexScan t u v, VRegexScan t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VRegexSplit t u v, VRegexSplit t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VRegexReplace t u v, VRegexReplace t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VRegexReplix t u v, VRegexReplix t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VRegexParse t, VRegexParse t') ->
            conv env t t'
        (VRegexToText t, VRegexToText t') ->
            conv env t t'

        (VRational, VRational) ->
            True
        (VRationalLit t, VRationalLit t') ->
            t == t'
        (VRationalShow t, VRationalShow t') ->
            conv env t t'
        (VRationalFromDouble t u, VRationalFromDouble t' u') ->
            conv env t t' && conv env u u'
        (VRationalToDouble t, VRationalToDouble t') ->
            conv env t t'
        (VRationalFromRational t, VRationalFromRational t') ->
            conv env t t'
        (VRationalPercent t u, VRationalPercent t' u') ->
            conv env t t' && conv env u u'
        (VRationalParse t, VRationalParse t') ->
            conv env t t'

        (VNatural, VNatural) ->
            True
        (VNaturalLit n, VNaturalLit n') ->
            n == n'
        (VNaturalFold t _ u v, VNaturalFold t' _ u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VNaturalBuild t, VNaturalBuild t') ->
            conv env t t'
        (VNaturalIsZero t, VNaturalIsZero t') ->
            conv env t t'
        (VNaturalEven t, VNaturalEven t') ->
            conv env t t'
        (VNaturalOdd t, VNaturalOdd t') ->
            conv env t t'
        (VNaturalToInteger t, VNaturalToInteger t') ->
            conv env t t'
        (VNaturalShow t, VNaturalShow t') ->
            conv env t t'
        (VNaturalParse t, VNaturalParse t') ->
            conv env t t'
        (VNaturalToBits t, VNaturalToBits t') ->
            conv env t t'
        (VNaturalSubtract x y, VNaturalSubtract x' y') ->
            conv env x x' && conv env y y'
        (VNaturalGcd x y, VNaturalGcd x' y') ->
            conv env x x' && conv env y y'
        (VNaturalPlus t u, VNaturalPlus t' u') ->
            conv env t t' && conv env u u'
        (VNaturalTimes t u, VNaturalTimes t' u') ->
            conv env t t' && conv env u u'
        (VInteger, VInteger) ->
            True
        (VIntegerLit t, VIntegerLit t') ->
            t == t'
        (VIntegerAdd t u, VIntegerAdd t' u') ->
            conv env t t' && conv env u u'
        (VIntegerMultiply t u, VIntegerMultiply t' u') ->
            conv env t t' && conv env u u'
        (VIntegerAnd t u, VIntegerAnd t' u') ->
            conv env t t' && conv env u u'
        (VIntegerXor t u, VIntegerXor t' u') ->
            conv env t t' && conv env u u'
        (VIntegerClamp t, VIntegerClamp t') ->
            conv env t t'
        (VIntegerNegate t, VIntegerNegate t') ->
            conv env t t'
        (VIntegerShow t, VIntegerShow t') ->
            conv env t t'
        (VIntegerParse t, VIntegerParse t') ->
            conv env t t'
        (VIntegerToDouble t, VIntegerToDouble t') ->
            conv env t t'
        (VDouble, VDouble) ->
            True
        (VDoubleLit n, VDoubleLit n') ->
            n == n'
        (VDoubleShow t, VDoubleShow t') ->
            conv env t t'
        (VDoubleParse t, VDoubleParse t') ->
            conv env t t'
        (VText, VText) ->
            True
        (VTextLit cs, VTextLit cs') ->
            convChunks cs cs'
        (VTextAppend t u, VTextAppend t' u') ->
            conv env t t' && conv env u u'
        (VTextShow t, VTextShow t') ->
            conv env t t'
        (VTextToLower t, VTextToLower t') ->
            conv env t t'
        (VTextToUpper t, VTextToUpper t') ->
            conv env t t'
        (VTextUnpack t, VTextUnpack t') ->
            conv env t t'
        (VTextPack t, VTextPack t') ->
            conv env t t'
        (VTextToList t, VTextToList t') ->
            conv env t t'
        (VTextLength t, VTextLength t') ->
            conv env t t'
        (VTextCompare t u v, VTextCompare t' u' v') ->
            conv env t t' && conv env u u' && conv env v v'
        (VList a, VList a') ->
            conv env a a'
        (VListLit _ xs, VListLit _ xs') ->
            eqListBy (conv env) (toList xs) (toList xs')
        (VListAppend t u, VListAppend t' u') ->
            conv env t t' && conv env u u'
        (VListBuild _ t, VListBuild _ t') ->
            conv env t t'
        (VListLength a t, VListLength a' t') ->
            conv env a a' && conv env t t'
        (VListHead _ t, VListHead _ t') ->
            conv env t t'
        (VListLast _ t, VListLast _ t') ->
            conv env t t'
        (VListIndexed _ t, VListIndexed _ t') ->
            conv env t t'
        (VListReverse _ t, VListReverse _ t') ->
            conv env t t'
        (VListPermutations _ t, VListPermutations _ t') ->
            conv env t t'
        (VListChoose _ x y, VListChoose _ x' y') ->
            conv env x x' && conv env y y'
        (VListFold a l _ t u, VListFold a' l' _ t' u') ->
            conv env a a' && conv env l l' && conv env t t' && conv env u u'
        (VListFixed a b, VListFixed a' b') ->
            conv env a a' && conv env b b'
        (VListFixedLit x xs, VListFixedLit x' xs') ->
            conv env x x' && eqListBy (conv env) (toList xs) (toList xs')
        (VListFixedFromList n a d t, VListFixedFromList n' a' d' t') ->
            conv env n n' && conv env a a' && conv env d d' && conv env t t'
        (VListFixedToList _ a t, VListFixedToList _ a' t') ->
            conv env a a' && conv env t t'
        (VListFixedHead _ a t, VListFixedHead _ a' t') ->
            conv env a a' && conv env t t'
        (VListFixedTail _ a t, VListFixedTail _ a' t') ->
            conv env a a' && conv env t t'

        (VSym t, VSym t') ->
            t == t'
        (VSymLit t , VSymLit t') ->
            t == t'
        (VSymFromText a, VSymFromText a') ->
            conv env a a'
        (VSymToText a, VSymToText a') ->
            conv env a a'

        (VSZ, VSZ) ->
            True
        (VSS a, VSS a') ->
            conv env a a'

        (VSZLit, VSZLit) ->
            True
        (VSSLit a , VSSLit a') ->
            conv env a a'
        (VSSFromNonZero a, VSSFromNonZero a') ->
            conv env a a'
        (VSSToNonZero a, VSSToNonZero a') ->
            conv env a a'
        (VSSToNatural a, VSSToNatural a') ->
            conv env a a'
        (VSSAdd a b, VSSAdd a' b') ->
            conv env a a' && conv env b b'
        (VSSSubtract a b, VSSSubtract a' b') ->
            conv env a a' && conv env b b'
        (VSSEqual a b, VSSEqual a' b') ->
            conv env a a' && conv env b b'
        (VSSLessThan a b, VSSLessThan a' b') ->
            conv env a a' && conv env b b'

        (VProof _a, VProof _a') ->
            True
        (VProofLit, VProofLit) ->
            True
        (VProofToBool a, VProofToBool a') ->
            conv env a a'
        (VProofFromBool _a b, VProofFromBool _a' b') ->
            conv env b b'

        (VPVoid _a, VPVoid _a') ->
            True
        (VPVoidUndefined a, VPVoidUndefined a') ->
            conv env a a'
        (VPVoidError a b, VPVoidError a' b') ->
            conv env a a' && conv env b b'
        (VPVoidKindUndefined a, VPVoidKindUndefined a') ->
            conv env a a'

        (VOptional a, VOptional a') ->
            conv env a a'
        (VSome t, VSome t') ->
            conv env t t'
        (VNone _, VNone _) ->
            True
        (VRecord m, VRecord m') ->
            eqMapsBy (conv env) m m'
        (VRecordLit m, VRecordLit m') ->
            eqMapsBy (conv env) m m'
        (VUnion m, VUnion m') ->
            eqMapsBy (eqMaybeBy (conv env)) m m'
        (VCombine _ t u, VCombine _ t' u') ->
            conv env t t' && conv env u u'
        (VCombineTypes t u, VCombineTypes t' u') ->
            conv env t t' && conv env u u'
        (VPrefer t u, VPrefer t' u') ->
            conv env t t' && conv env u u'
        (VMerge t u _, VMerge t' u' _) ->
            conv env t t' && conv env u u'
        (VToMap t _, VToMap t' _) ->
            conv env t t'
        (VField t k, VField t' k') ->
            conv env t t' && k == k'
        (VProject t (Left ks), VProject t' (Left ks')) ->
            conv env t t' && ks == ks'
        (VProject t (Right e), VProject t' (Right e')) ->
            conv env t t' && conv env e e'
        (VAssert t, VAssert t') ->
            conv env t t'
        (VEquivalent t u, VEquivalent t' u') ->
            conv env t t' && conv env u u'
        (VInject m k mt, VInject m' k' mt') ->
            eqMapsBy (eqMaybeBy (conv env)) m m' && k == k' && eqMaybeBy (conv env) mt mt'
        (VEmbed a, VEmbed a') ->
            a == a'
        (_, _) ->
            False
  where
    fresh :: Text -> (Text, Val a)
    fresh x = (x, VVar x (countEnvironment x env))
    {-# INLINE fresh #-}

    freshClosure :: Closure a -> (Text, Val a, Closure a)
    freshClosure closure@(Closure x _ _) = (x, snd (fresh x), closure)
    {-# INLINE freshClosure #-}

    convChunks :: VChunks a -> VChunks a -> Bool
    convChunks (VChunks xys z) (VChunks xys' z') =
      eqListBy (\(x, y) (x', y') -> x == x' && conv env y y') xys xys' && z == z'
    {-# INLINE convChunks #-}

    convSkip :: Text -> Val a -> Val a -> Bool
    convSkip x = conv (Skip env x)
    {-# INLINE convSkip #-}

judgmentallyEqual :: Eq a => Expr s a -> Expr t a -> Bool
judgmentallyEqual (Syntax.denote -> t) (Syntax.denote -> u) =
    conv Empty (eval Empty t) (eval Empty u)

data Names
  = EmptyNames
  | Bind !Names {-# UNPACK #-} !Text
  deriving Show

dumpNames :: Names -> String
dumpNames EmptyNames = "EmptyNames"
dumpNames (Bind nms t) = "Bind [" ++ Text.unpack t ++ "] " ++ dumpNames nms

envNames :: Environment a -> Names
envNames Empty = EmptyNames
envNames (Skip   env x  ) = Bind (envNames env) x
envNames (Extend env x _) = Bind (envNames env) x

countNames :: Text -> Names -> Int
countNames x = go 0
  where
    go !acc EmptyNames         = acc
    go  acc (Bind env x') = go (if x == x' then acc + 1 else acc) env

-- | Quote a value into beta-normal form.
quote :: forall a. Eq a => Names -> Val a -> Expr Void a
quote !env !t0 =
    case t0 of
        VConst k ->
            Const k
        VVar !x !i ->
            Var (V x (countNames x env - i - 1))
        VApp t u ->
            quote env t `qApp` u
        VLam a (freshClosure -> (x, v, t)) ->
            Lam x (quote env a) (quoteBind x (instantiate t v))
        VHLam i t ->
            case i of
                Typed (fresh -> (x, v)) a -> Lam x (quote env a) (quoteBind x (t v))
                Prim                      -> quote env (t VPrimVar)
                NaturalSubtractZero       -> App NaturalSubtract (NaturalLit 0)

        VPi a (freshClosure -> (x, v, b)) ->
            Pi x (quote env a) (quoteBind x (instantiate b v))
        VHPi (fresh -> (x, v)) a b ->
            Pi x (quote env a) (quoteBind x (b v))
        VBool ->
            Bool
        VBoolLit b ->
            BoolLit b
        VBoolAnd t u ->
            BoolAnd (quote env t) (quote env u)
        VBoolOr t u ->
            BoolOr (quote env t) (quote env u)
        VBoolEQ t u ->
            BoolEQ (quote env t) (quote env u)
        VBoolNE t u ->
            BoolNE (quote env t) (quote env u)
        VBoolIf t u v ->
            BoolIf (quote env t) (quote env u) (quote env v)
        VNonZero ->
            NonZero
        VNonZeroLit n ->
            NonZeroLit n
        VNonZeroShow t ->
            NonZeroShow `qApp` t
        VNonZeroClamp t ->
            NonZeroClamp `qApp` t
        VNonZeroDiv t u ->
            NonZeroDiv `qApp` t `qApp` u
        VNonZeroMod t u ->
            NonZeroMod `qApp` t `qApp` u
        VNonZeroLog t u ->
            NonZeroLog `qApp` t `qApp` u
        VNonZeroAdd t u ->
            NonZeroAdd `qApp` t `qApp` u
        VNonZeroMultiply t u ->
            NonZeroMultiply `qApp` t `qApp` u
        VNonZeroToNatural t ->
            NonZeroToNatural `qApp` t
        VNonZeroToInteger t ->
            NonZeroToInteger `qApp` t
        VNonZeroParse t ->
            NonZeroParse `qApp` t

        VDateTime ->
            DateTime
        VDateTimeLit n ->
            DateTimeLit n
        VDateTimeShow t ->
            DateTimeShow `qApp` t
        VDateTimeParse t ->
            DateTimeParse `qApp` t
        VDateTimeFromSeconds t ->
            DateTimeFromSeconds `qApp` t
        VDateTimeToSeconds t ->
            DateTimeToSeconds `qApp` t

        VDateTimeAddYears t u ->
            DateTimeAddYears `qApp` t `qApp` u
        VDateTimeAddMonths t u ->
            DateTimeAddMonths `qApp` t `qApp` u
        VDateTimeAddDays t u ->
            DateTimeAddDays `qApp` t `qApp` u

        VDateTimeFromWeek t u v ->
            DateTimeFromWeek `qApp` t `qApp` u `qApp` v
        VDateTimeToWeek t ->
            DateTimeToWeek `qApp` t
        VDateTimeToDate t u v w x y ->
            DateTimeToDate `qApp` t `qApp` u `qApp` v `qApp` w `qApp` x `qApp` y
        VDateTimeFromDate t ->
            DateTimeFromDate `qApp` t
        VDateTimeLastDayOfMonth t u ->
            DateTimeLastDayOfMonth `qApp` t `qApp` u

        VDateTimeGetJulianDay t ->
            DateTimeGetJulianDay `qApp` t
        VDateTimeSetJulianDay t u ->
            DateTimeSetJulianDay `qApp` t `qApp` u

        VRegex ->
            Regex
        VRegexLit r ->
            RegexLit r
        VRegexShow t ->
            RegexShow `qApp` t
        VRegexMatch t u ->
            RegexMatch `qApp` t `qApp` u
        VRegexScan t u v ->
            RegexScan `qApp` t `qApp` u `qApp` v
        VRegexSplit t u v ->
            RegexSplit `qApp` t `qApp` u `qApp` v
        VRegexReplace t u v ->
            RegexReplace `qApp` t `qApp` u `qApp` v
        VRegexReplix t u v ->
            RegexReplix `qApp` t `qApp` u `qApp` v
        VRegexParse t ->
            RegexParse `qApp` t
        VRegexToText t ->
            RegexToText `qApp` t

        VRational ->
            Rational
        VRationalLit r ->
            RationalLit r
        VRationalShow t ->
            RationalShow `qApp` t
        VRationalFromDouble t u ->
            RationalFromDouble `qApp` t `qApp` u
        VRationalToDouble t ->
            RationalToDouble `qApp` t
        VRationalFromRational t ->
            RationalFromRational `qApp` t
        VRationalPercent t u ->
            RationalPercent (quote env t) (quote env u)
        VRationalParse t ->
            RationalParse `qApp` t

        VNatural ->
            Natural
        VNaturalLit n ->
            NaturalLit n
        VNaturalFold a t u v ->
            NaturalFold `qApp` a `qApp` t `qApp` u `qApp` v
        VNaturalBuild t ->
            NaturalBuild `qApp` t
        VNaturalIsZero t ->
            NaturalIsZero `qApp` t
        VNaturalEven t ->
            NaturalEven `qApp` t
        VNaturalOdd t ->
            NaturalOdd `qApp` t
        VNaturalToInteger t ->
            NaturalToInteger `qApp` t
        VNaturalShow t ->
            NaturalShow `qApp` t
        VNaturalParse t ->
            NaturalParse `qApp` t
        VNaturalToBits t ->
            NaturalToBits `qApp` t
        VNaturalPlus t u ->
            NaturalPlus (quote env t) (quote env u)
        VNaturalTimes t u ->
            NaturalTimes (quote env t) (quote env u)
        VNaturalSubtract x y ->
            NaturalSubtract `qApp` x `qApp` y
        VNaturalGcd x y ->
            NaturalGcd `qApp` x `qApp` y
        VInteger ->
            Integer
        VIntegerLit n ->
            IntegerLit n
        VIntegerAdd x y ->
            IntegerAdd `qApp` x `qApp` y
        VIntegerMultiply x y ->
            IntegerMultiply `qApp` x `qApp` y
        VIntegerAnd x y ->
            IntegerAnd `qApp` x `qApp` y
        VIntegerXor x y ->
            IntegerXor `qApp` x `qApp` y
        VIntegerClamp t ->
            IntegerClamp `qApp` t
        VIntegerNegate t ->
            IntegerNegate `qApp` t
        VIntegerShow t ->
            IntegerShow `qApp` t
        VIntegerParse t ->
            IntegerParse `qApp` t
        VIntegerToDouble t ->
            IntegerToDouble `qApp` t
        VDouble ->
            Double
        VDoubleLit n ->
            DoubleLit n
        VDoubleShow t ->
            DoubleShow `qApp` t
        VDoubleParse t ->
            DoubleParse `qApp` t
        VText ->
            Text
        VTextLit (VChunks xys z) ->
            TextLit (Chunks (fmap (fmap (quote env)) xys) z)
        VTextAppend t u ->
            TextAppend (quote env t) (quote env u)
        VTextShow t ->
            TextShow `qApp` t
        VTextToLower t ->
            TextToLower `qApp` t
        VTextToUpper t ->
            TextToUpper `qApp` t
        VTextUnpack t ->
            TextUnpack `qApp` t
        VTextPack t ->
            TextPack `qApp` t
        VTextToList t ->
            TextToList `qApp` t
        VTextLength t ->
            TextLength `qApp` t
        VTextCompare t u v ->
            TextCompare `qApp` t `qApp` u `qApp` v
        VList t ->
            List `qApp` t
        VListLit ma ts ->
            ListLit (fmap (quote env) ma) (fmap (quote env) ts)
        VListAppend t u ->
            ListAppend (quote env t) (quote env u)
        VListBuild a t ->
            ListBuild `qApp` a `qApp` t
        VListFold a l t u v ->
            ListFold `qApp` a `qApp` l `qApp` t `qApp` u `qApp` v
        VListLength a t ->
            ListLength `qApp` a `qApp` t
        VListHead a t ->
            ListHead `qApp` a `qApp` t
        VListLast a t ->
            ListLast `qApp` a `qApp` t
        VListIndexed a t ->
            ListIndexed `qApp` a `qApp` t
        VListReverse a t ->
            ListReverse `qApp` a `qApp` t
        VListPermutations a t ->
            ListPermutations `qApp` a `qApp` t
        VListChoose a x y ->
            ListChoose `qApp` a `qApp` x `qApp` y
        VListFixed t u ->
            ListFixed `qApp` t `qApp` u
        VListFixedLit t ts ->
            ListFixedLit (quote env t) (fmap (quote env) ts)
        VListFixedFromList n a d t  ->
            ListFixedFromList `qApp` n `qApp` a `qApp` d `qApp` t
        VListFixedToList n a t ->
            ListFixedToList `qApp` n `qApp` a `qApp` t
        VListFixedHead n a t ->
            ListFixedHead `qApp` n `qApp` a `qApp` t
        VListFixedTail n a t ->
            ListFixedTail `qApp` n `qApp` a `qApp` t

        VSym t -> Sym t
        VSymLit t -> SymLit t
        VSymFromText t -> SymFromText `qApp` t
        VSymToText t -> SymToText `qApp` t

        VSZ -> SZ
        VSS a -> SS `qApp` a
        VSZLit -> SZLit
        VSSLit t -> SSLit (quote env t)

        VSSFromNonZero t -> SSFromNonZero `qApp` t
        VSSToNonZero t -> SSToNonZero `qApp` t
        VSSToNatural t -> SSToNatural `qApp` t
        VSSAdd t u -> SSAdd `qApp` t `qApp` u
        VSSSubtract t u -> SSSubtract `qApp` t `qApp` u
        VSSEqual t u -> SSEqual `qApp` t `qApp` u
        VSSLessThan t u -> SSLessThan `qApp` t `qApp` u

        VProof t -> Proof `qApp` t
        VProofLit -> ProofLit
        VProofToBool t -> ProofToBool `qApp` t
        VProofFromBool t u -> ProofFromBool `qApp` t `qApp` u

        VPVoid t -> PVoid `qApp` t
        VPVoidUndefined t -> PVoidUndefined `qApp` t
        VPVoidError t u -> PVoidError `qApp` t `qApp` u
        VPVoidKindUndefined t -> PVoidKindUndefined `qApp` t

        VOptional a ->
            Optional `qApp` a
        VSome t ->
            Some (quote env t)
        VNone t ->
            None `qApp` t
        VRecord m ->
            Record (fmap quoteRecordField m)
        VRecordLit m ->
            RecordLit (fmap quoteRecordField m)
        VUnion m ->
            Union (fmap (fmap (quote env)) m)
        VCombine mk t u ->
            Combine mk (quote env t) (quote env u)
        VCombineTypes t u ->
            CombineTypes (quote env t) (quote env u)
        VPrefer t u ->
            Prefer PreferFromSource (quote env t) (quote env u)
        VMerge t u ma ->
            Merge (quote env t) (quote env u) (fmap (quote env) ma)
        VToMap t ma ->
            ToMap (quote env t) (fmap (quote env) ma)
        VField t k ->
            Field (quote env t) k
        VProject t p ->
            Project (quote env t) (fmap (quote env) p)
        VAssert t ->
            Assert (quote env t)
        VEquivalent t u ->
            Equivalent (quote env t) (quote env u)
        VInject m k Nothing ->
            Field (Union (fmap (fmap (quote env)) m)) k
        VInject m k (Just t) ->
            Field (Union (fmap (fmap (quote env)) m)) k `qApp` t
        VEmbed a ->
            Embed a
        VPrimVar ->
            error errorMsg
  where
    fresh :: Text -> (Text, Val a)
    fresh x = (x, VVar x (countNames x env))
    {-# INLINE fresh #-}

    freshClosure :: Closure a -> (Text, Val a, Closure a)
    freshClosure closure@(Closure x _ _) = (x, snd (fresh x), closure)
    {-# INLINE freshClosure #-}

    quoteBind :: Text -> Val a -> Expr Void a
    quoteBind x = quote (Bind env x)
    {-# INLINE quoteBind #-}

    qApp :: Expr Void a -> Val a -> Expr Void a
    qApp t VPrimVar = t
    qApp t u        = App t (quote env u)
    {-# INLINE qApp #-}

    quoteRecordField :: Val a -> RecordField Void a
    quoteRecordField = Syntax.makeRecordField . quote env
    {-# INLINE quoteRecordField #-}

-- | Normalize an expression in an environment of values. Any variable pointing out of
--   the environment is treated as opaque free variable.
nf :: Eq a => Environment a -> Expr s a -> Expr t a
nf !env = Syntax.renote . quote (envNames env) . eval env . Syntax.denote

normalize :: Eq a => Expr s a -> Expr t a
normalize = nf Empty

alphaNormalize :: Expr s a -> Expr s a
alphaNormalize = goEnv EmptyNames
  where
    goVar :: Names -> Text -> Int -> Expr s a
    goVar e topX topI = go 0 e topI
      where
        go !acc (Bind env x) !i
          | x == topX = if i == 0 then Var (V "_" acc) else go (acc + 1) env (i - 1)
          | otherwise = go (acc + 1) env i
        go _ EmptyNames i = Var (V topX i)

    goEnv :: Names -> Expr s a -> Expr s a
    goEnv !e0 t0 =
        case t0 of
            Const k ->
                Const k
            Var (V x i) ->
                goVar e0 x i
            Lam x t u ->
                Lam "_" (go t) (goBind x u)
            Pi x a b ->
                Pi "_" (go a) (goBind x b)
            App t u ->
                App (go t) (go u)
            Let (Binding src0 x src1 mA src2 a) b ->
                Let (Binding src0 "_" src1 (fmap (fmap go) mA) src2 (go a)) (goBind x b)
            Annot t u ->
                Annot (go t) (go u)
            Bool ->
                Bool
            BoolLit b ->
                BoolLit b
            BoolAnd t u ->
                BoolAnd (go t) (go u)
            BoolOr t u ->
                BoolOr  (go t) (go u)
            BoolEQ t u ->
                BoolEQ  (go t) (go u)
            BoolNE t u ->
                BoolNE  (go t) (go u)
            BoolIf b t f ->
                BoolIf  (go b) (go t) (go f)
            NonZero ->
                NonZero
            NonZeroLit n ->
                NonZeroLit n
            NonZeroShow ->
                NonZeroShow
            NonZeroClamp ->
                NonZeroClamp
            NonZeroDiv ->
                NonZeroDiv
            NonZeroMod ->
                NonZeroMod
            NonZeroLog ->
                NonZeroLog
            NonZeroAdd ->
                NonZeroAdd
            NonZeroMultiply ->
                NonZeroMultiply
            NonZeroToNatural ->
                NonZeroToNatural
            NonZeroToInteger ->
                NonZeroToInteger
            NonZeroParse ->
                NonZeroParse

            DateTime ->
                DateTime
            DateTimeLit n ->
                DateTimeLit n
            DateTimeShow ->
                DateTimeShow
            DateTimeParse ->
                DateTimeParse
            DateTimeFromSeconds ->
                DateTimeFromSeconds
            DateTimeToSeconds ->
                DateTimeToSeconds
            DateTimeAddYears ->
                DateTimeAddYears
            DateTimeAddMonths ->
                DateTimeAddMonths
            DateTimeAddDays ->
                DateTimeAddDays
            DateTimeFromWeek ->
                DateTimeFromWeek
            DateTimeToWeek ->
                DateTimeToWeek
            DateTimeToDate ->
                DateTimeToDate
            DateTimeFromDate ->
                DateTimeFromDate
            DateTimeLastDayOfMonth ->
                DateTimeLastDayOfMonth

            DateTimeSetJulianDay ->
                DateTimeSetJulianDay
            DateTimeGetJulianDay ->
                DateTimeGetJulianDay

            Regex ->
                Regex
            RegexLit n ->
                RegexLit n
            RegexShow ->
                RegexShow
            RegexMatch ->
                RegexMatch
            RegexScan ->
                RegexScan
            RegexSplit ->
                RegexSplit
            RegexReplace ->
                RegexReplace
            RegexReplix ->
                RegexReplix
            RegexParse ->
                RegexParse
            RegexToText ->
                RegexToText

            Rational ->
                Rational
            RationalLit n ->
                RationalLit n
            RationalShow ->
                RationalShow
            RationalFromDouble ->
                RationalFromDouble
            RationalToDouble ->
                RationalToDouble
            RationalFromRational ->
                RationalFromRational
            RationalPercent t u ->
                RationalPercent (go t) (go u)
            RationalParse ->
                RationalParse


            Natural ->
                Natural
            NaturalLit n ->
                NaturalLit n
            NaturalFold ->
                NaturalFold
            NaturalBuild ->
                NaturalBuild
            NaturalIsZero ->
                NaturalIsZero
            NaturalEven ->
                NaturalEven
            NaturalOdd ->
                NaturalOdd
            NaturalToInteger ->
                NaturalToInteger
            NaturalShow ->
                NaturalShow
            NaturalParse ->
                NaturalParse
            NaturalToBits ->
                NaturalToBits
            NaturalSubtract ->
                NaturalSubtract
            NaturalGcd ->
                NaturalGcd
            NaturalPlus t u ->
                NaturalPlus (go t) (go u)
            NaturalTimes t u ->
                NaturalTimes (go t) (go u)
            Integer ->
                Integer
            IntegerLit n ->
                IntegerLit n
            IntegerAdd ->
                IntegerAdd
            IntegerMultiply ->
                IntegerMultiply
            IntegerAnd ->
                IntegerAnd
            IntegerXor ->
                IntegerXor
            IntegerClamp ->
                IntegerClamp
            IntegerNegate ->
                IntegerNegate
            IntegerShow ->
                IntegerShow
            IntegerParse ->
                IntegerParse
            IntegerToDouble ->
                IntegerToDouble
            Double ->
                Double
            DoubleLit n ->
                DoubleLit n
            DoubleShow ->
                DoubleShow
            DoubleParse ->
                DoubleParse
            Text ->
                Text
            TextLit cs ->
                TextLit (goChunks cs)
            TextAppend t u ->
                TextAppend (go t) (go u)
            TextShow ->
                TextShow
            TextToLower ->
                TextToLower
            TextToUpper ->
                TextToUpper
            TextUnpack ->
                TextUnpack
            TextPack ->
                TextPack
            TextToList ->
                TextToList
            TextLength ->
                TextLength
            TextCompare ->
                TextCompare
            List ->
                List
            ListLit ma ts ->
                ListLit (fmap go ma) (fmap go ts)
            ListAppend t u ->
                ListAppend (go t) (go u)
            ListBuild ->
                ListBuild
            ListFold ->
                ListFold
            ListLength ->
                ListLength
            ListHead ->
                ListHead
            ListLast ->
                ListLast
            ListIndexed ->
                ListIndexed
            ListReverse ->
                ListReverse
            ListPermutations ->
                ListPermutations
            ListChoose ->
                ListChoose
            ListFixed ->
                ListFixed
            ListFixedLit t ts ->
                ListFixedLit (go t) (fmap go ts)
            ListFixedFromList ->
                ListFixedFromList
            ListFixedToList ->
                ListFixedToList
            ListFixedHead ->
                ListFixedHead
            ListFixedTail ->
                ListFixedTail

            Sym t -> Sym t
            SymLit t -> SymLit t

            SymFromText -> SymFromText
            SymToText -> SymToText

            SZ -> SZ
            SS -> SS
            SZLit -> SZLit
            SSLit t -> SSLit (go t)

            SSFromNonZero -> SSFromNonZero
            SSToNonZero -> SSToNonZero
            SSToNatural -> SSToNatural
            SSAdd -> SSAdd
            SSSubtract -> SSSubtract
            SSEqual -> SSEqual
            SSLessThan -> SSLessThan

            Proof -> Proof
            ProofLit -> ProofLit
            ProofToBool -> ProofToBool
            ProofFromBool -> ProofFromBool

            PVoid -> PVoid
            PVoidUndefined -> PVoidUndefined
            PVoidError -> PVoidError
            PVoidKindUndefined -> PVoidKindUndefined

            Optional ->
                Optional
            Some t ->
                Some (go t)
            None ->
                None
            Record kts ->
                Record (goRecordField <$> kts)
            RecordLit kts ->
                RecordLit (goRecordField <$> kts)
            Union kts ->
                Union (fmap (fmap go) kts)
            Combine m t u ->
                Combine m (go t) (go u)
            CombineTypes t u ->
                CombineTypes (go t) (go u)
            Prefer b t u ->
                Prefer b (go t) (go u)
            RecordCompletion t u ->
                RecordCompletion (go t) (go u)
            Merge x y ma ->
                Merge (go x) (go y) (fmap go ma)
            ToMap x ma ->
                ToMap (go x) (fmap go ma)
            Field t k ->
                Field (go t) k
            Project t ks ->
                Project (go t) (fmap go ks)
            Assert t ->
                Assert (go t)
            Equivalent t u ->
                Equivalent (go t) (go u)
            With e k v ->
                With (go e) k (go v)
            Note s e ->
                Note s (go e)
            ImportAlt t u ->
                ImportAlt (go t) (go u)
            Embed a ->
                Embed a
      where
        go                     = goEnv e0
        goBind x               = goEnv (Bind e0 x)
        goChunks (Chunks ts x) = Chunks (fmap (fmap go) ts) x
        goRecordField (RecordField s0 e) = RecordField s0 (go e)
dumpExpr :: Expr s a -> String
dumpExpr = \case
 Const cc -> "Const " ++ show cc
 Var {} -> "Var"
 With {} -> "With"
 Lam {} -> "Lam"
 Pi {} -> "Pi"
 App {} -> "App"
 Let {} -> "Let"
 Annot {} -> "Annot"
 Bool {} -> "Bool"
 BoolLit {} -> "BoolLit"
 BoolAnd {} -> "BoolAnd"
 BoolOr {} -> "BoolOr"
 BoolEQ {} -> "BoolEQ"
 BoolNE {} -> "BoolNE"
 BoolIf {} -> "BoolIf"
 NonZero {} -> "NonZero"
 NonZeroLit {} -> "NonZeroLit"
 NonZeroShow {} -> "NonZeroShow"
 NonZeroClamp {} -> "NonZeroClamp"
 NonZeroDiv {} -> "NonZeroDiv"
 NonZeroMod {} -> "NonZeroMod"
 NonZeroLog {} -> "NonZeroLog"
 NonZeroAdd {} -> "NonZeroAdd"
 NonZeroMultiply {} -> "NonZeroMultiply"
 NonZeroToNatural {} -> "NonZeroToNatural"
 NonZeroToInteger {} -> "NonZeroToInteger"
 NonZeroParse {} -> "NonZeroParse"
 DateTime {} -> "DateTime"
 DateTimeLit {} -> "DateTimeLit"
 DateTimeShow {} -> "DateTimeShow"
 DateTimeParse {} -> "DateTimeParse"
 DateTimeFromSeconds {} -> "DateTimeFromSeconds"
 DateTimeToSeconds {} -> "DateTimeToSeconds"
 DateTimeAddYears {} -> "DateTimeAddYears"
 DateTimeAddMonths {} -> "DateTimeAddMonths"
 DateTimeAddDays {} -> "DateTimeAddDays"
 DateTimeFromWeek {} -> "DateTimeFromWeek"
 DateTimeToWeek {} -> "DateTimeToWeek"
 DateTimeToDate {} -> "DateTimeToDate"
 DateTimeFromDate {} -> "DateTimeFromDate"
 DateTimeLastDayOfMonth {} -> "DateTimeLastDayOfMonth"
 DateTimeGetJulianDay {} -> "DateTimeGetJulianDay"
 DateTimeSetJulianDay {} -> "DateTimeSetJulianDay"
 Regex {} -> "Regex"
 RegexLit {} -> "RegexLit"
 RegexShow {} -> "RegexShow"
 RegexMatch {} -> "RegexMatch"
 RegexScan {} -> "RegexScan"
 RegexSplit {} -> "RegexSplit"
 RegexReplace {} -> "RegexReplace"
 RegexReplix {} -> "RegexReplix"
 RegexParse {} -> "RegexParse"
 RegexToText {} -> "RegexToText"
 Rational {} -> "Rational"
 RationalLit {} -> "RationalLit"
 RationalShow {} -> "RationalShow"
 RationalFromDouble {} -> "RationalFromDouble"
 RationalToDouble {} -> "RationalToDouble"
 RationalFromRational {} -> "RationalFromRational"
 RationalPercent {} -> "RationalPercent"
 RationalParse {} -> "RationalParse"
 Natural {} -> "Natural"
 NaturalLit {} -> "NaturalLit"
 NaturalFold {} -> "NaturalFold"
 NaturalBuild {} -> "NaturalBuild"
 NaturalIsZero {} -> "NaturalIsZero"
 NaturalEven {} -> "NaturalEven"
 NaturalOdd {} -> "NaturalOdd"
 NaturalToInteger {} -> "NaturalToInteger"
 NaturalShow {} -> "NaturalShow"
 NaturalParse {} -> "NaturalParse"
 NaturalToBits {} -> "NaturalToBits"
 NaturalSubtract {} -> "NaturalSubtract"
 NaturalGcd {} -> "NaturalGcd"
 NaturalPlus {} -> "NaturalPlus"
 NaturalTimes {} -> "NaturalTimes"
 Integer {} -> "Integer"
 IntegerLit {} -> "IntegerLit"
 IntegerAdd {} -> "IntegerAdd"
 IntegerMultiply {} -> "IntegerMultiply"
 IntegerAnd {} -> "IntegerAnd"
 IntegerXor {} -> "IntegerXor"
 IntegerClamp {} -> "IntegerClamp"
 IntegerNegate {} -> "IntegerNegate"
 IntegerShow {} -> "IntegerShow"
 IntegerParse {} -> "IntegerParse"
 IntegerToDouble {} -> "IntegerToDouble"
 Double {} -> "Double"
 DoubleLit {} -> "DoubleLit"
 DoubleShow {} -> "DoubleShow"
 DoubleParse {} -> "DoubleParse"
 Text {} -> "Text"
 TextLit {} -> "TextLit"
 TextAppend {} -> "TextAppend"
 TextShow {} -> "TextShow"
 TextToLower {} -> "TextToLower"
 TextToUpper {} -> "TextToUpper"
 TextUnpack {} -> "TextUnpack"
 TextPack {} -> "TextPack"
 TextToList {} -> "TextToList"
 TextLength {} -> "TextLength"
 TextCompare {} -> "TextCompare"
 List {} -> "List"
 ListLit {} -> "ListLit"
 ListAppend {} -> "ListAppend"
 ListBuild {} -> "ListBuild"
 ListFold {} -> "ListFold"
 ListLength {} -> "ListLength"
 ListHead {} -> "ListHead"
 ListLast {} -> "ListLast"
 ListIndexed {} -> "ListIndexed"
 ListReverse {} -> "ListReverse"
 ListPermutations {} -> "ListPermutations"
 ListChoose {} -> "ListChoose"
 ListFixed {} -> "ListFixed"
 ListFixedLit {} -> "ListFixedLit"
 ListFixedFromList {} -> "ListFixedFromList"
 ListFixedToList {} -> "ListFixedToList"
 ListFixedHead {} -> "ListFixedHead"
 ListFixedTail {} -> "ListFixedTail"

 Sym t -> "Sym " ++ Text.unpack t
 SymLit t -> "SymLit " ++ Text.unpack t
 SymFromText {} -> "SymFromText"
 SymToText {} -> "SymToText"

 SZ {} -> "SZ"
 SS {} -> "SS"

 SZLit {} -> "SZLit"
 SSLit {} -> "SSLit"
 SSFromNonZero {} -> "SSFromNonZero"
 SSToNonZero {} -> "SSToNonZero"
 SSToNatural {} -> "SSToNatural"
 SSAdd {} -> "SSAdd"
 SSSubtract {} -> "SSSubtract"
 SSEqual {} -> "SSEqual"
 SSLessThan {} -> "SSLessThan"

 Proof {} -> "Proof"
 ProofLit {} -> "ProofLit"
 ProofToBool {} -> "ProofToBool"
 ProofFromBool {} -> "ProofFromBool"

 PVoid {} -> "PVoid"
 PVoidUndefined {} -> "PVoidUndefined"
 PVoidError {} -> "PVoidError"
 PVoidKindUndefined {} -> "PVoidKindUndefined"

 Optional {} -> "Optional"
 Some {} -> "Some"
 None {} -> "None"
 Record m -> "Record " ++ Map.foldMapWithKey (\k a -> "\n\tkey=" ++ Text.unpack k ++ " expr=" ++ dumpExpr (recordFieldValue a)) m
 RecordLit m -> "RecordLit " ++ Map.foldMapWithKey (\k a -> "\n\tkey=" ++ Text.unpack k ++ " expr=" ++ dumpExpr (recordFieldValue a)) m
 Union {} -> "Union"
 Combine {} -> "Combine"
 CombineTypes {} -> "CombineTypes"
 Prefer {} -> "Prefer"
 RecordCompletion {} -> "RecordCompletion"
 Merge {} -> "Merge"
 ToMap {} -> "ToMap"
 Field {} -> "Field"
 Project {} -> "Project"
 Assert {} -> "Assert"
 Equivalent {} -> "Equivalent"
 Note {} -> "Note"
 ImportAlt {} -> "ImportAlt"
 Embed {} -> "Embed"

dumpVal :: Val a -> String
dumpVal = \case
 VConst cc -> "VConst " ++ show cc
 VVar {} -> "VVar"
 VPrimVar {} -> "VPrimVar"
 VApp {} -> "VApp"
 VLam {} -> "VLam"
 VHLam {} -> "VHLam"
 VPi {} -> "VPi"
 VHPi {} -> "VHPi"
 VBool {} -> "VBool"
 VBoolLit {} -> "VBoolLit"
 VBoolAnd {} -> "VBoolAnd"
 VBoolOr {} -> "VBoolOr"
 VBoolEQ {} -> "VBoolEQ"
 VBoolNE {} -> "VBoolNE"
 VBoolIf {} -> "VBoolIf"
 VNonZero {} -> "VNonZero"
 VNonZeroLit {} -> "VNonZeroLit"
 VNonZeroShow {} -> "VNonZeroShow"
 VNonZeroClamp {} -> "VNonZeroClamp"
 VNonZeroDiv {} -> "VNonZeroDiv"
 VNonZeroMod {} -> "VNonZeroMod"
 VNonZeroLog {} -> "VNonZeroLog"
 VNonZeroAdd {} -> "VNonZeroAdd"
 VNonZeroMultiply {} -> "VNonZeroMultiply"
 VNonZeroToNatural {} -> "VNonZeroToNatural"
 VNonZeroToInteger {} -> "VNonZeroToInteger"
 VNonZeroParse {} -> "VNonZeroParse"
 VDateTime {} -> "VDateTime"
 VDateTimeLit {} -> "VDateTimeLit"
 VDateTimeShow {} -> "VDateTimeShow"
 VDateTimeParse {} -> "VDateTimeParse"
 VDateTimeFromSeconds {} -> "VDateTimeFromSeconds"
 VDateTimeToSeconds {} -> "VDateTimeToSeconds"
 VDateTimeAddYears {} -> "VDateTimeAddYears"
 VDateTimeAddMonths {} -> "VDateTimeAddMonths"
 VDateTimeAddDays {} -> "VDateTimeAddDays"
 VDateTimeFromWeek {} -> "VDateTimeFromWeek"
 VDateTimeToWeek {} -> "VDateTimeToWeek"
 VDateTimeToDate {} -> "VDateTimeToDate"
 VDateTimeFromDate {} -> "VDateTimeFromDate"
 VDateTimeLastDayOfMonth {} -> "VDateTimeLastDayOfMonth"
 VDateTimeGetJulianDay {} -> "VDateTimeGetJulianDay"
 VDateTimeSetJulianDay {} -> "VDateTimeSetJulianDay"
 VRegex {} -> "VRegex"
 VRegexLit {} -> "VRegexLit"
 VRegexShow {} -> "VRegexShow"
 VRegexMatch {} -> "VRegexMatch"
 VRegexScan {} -> "VRegexScan"
 VRegexSplit {} -> "VRegexSplit"
 VRegexReplace {} -> "VRegexReplace"
 VRegexReplix {} -> "VRegexReplix"
 VRegexParse {} -> "VRegexParse"
 VRegexToText {} -> "VRegexToText"
 VRational {} -> "VRational"
 VRationalLit {} -> "VRationalLit"
 VRationalShow {} -> "VRationalShow"
 VRationalFromDouble {} -> "VRationalFromDouble"
 VRationalToDouble {} -> "VRationalToDouble"
 VRationalFromRational {} -> "VRationalFromRational"
 VRationalPercent {} -> "VRationalPercent"
 VRationalParse {} -> "VRationalParse"
 VNatural {} -> "VNatural"
 VNaturalLit {} -> "VNaturalLit"
 VNaturalFold {} -> "VNaturalFold"
 VNaturalBuild {} -> "VNaturalBuild"
 VNaturalIsZero {} -> "VNaturalIsZero"
 VNaturalEven {} -> "VNaturalEven"
 VNaturalOdd {} -> "VNaturalOdd"
 VNaturalToInteger {} -> "VNaturalToInteger"
 VNaturalShow {} -> "VNaturalShow"
 VNaturalParse {} -> "VNaturalParse"
 VNaturalToBits {} -> "VNaturalToBits"
 VNaturalSubtract {} -> "VNaturalSubtract"
 VNaturalGcd {} -> "VNaturalGcd"
 VNaturalPlus {} -> "VNaturalPlus"
 VNaturalTimes {} -> "VNaturalTimes"
 VInteger {} -> "VInteger"
 VIntegerLit {} -> "VIntegerLit"
 VIntegerAdd {} -> "VIntegerAdd"
 VIntegerMultiply {} -> "VIntegerMultiply"
 VIntegerAnd {} -> "VIntegerAnd"
 VIntegerXor {} -> "VIntegerXor"
 VIntegerClamp {} -> "VIntegerClamp"
 VIntegerNegate {} -> "VIntegerNegate"
 VIntegerShow {} -> "VIntegerShow"
 VIntegerParse {} -> "VIntegerParse"
 VIntegerToDouble {} -> "VIntegerToDouble"
 VDouble {} -> "VDouble"
 VDoubleLit {} -> "VDoubleLit"
 VDoubleShow {} -> "VDoubleShow"
 VDoubleParse {} -> "VDoubleParse"
 VText {} -> "VText"
 VTextLit {} -> "VTextLit"
 VTextAppend {} -> "VTextAppend"
 VTextShow {} -> "VTextShow"
 VTextToLower {} -> "VTextToLower"
 VTextToUpper {} -> "VTextToUpper"
 VTextUnpack {} -> "VTextUnpack"
 VTextPack {} -> "VTextPack"
 VTextToList {} -> "VTextToList"
 VTextLength {} -> "VTextLength"
 VTextCompare {} -> "VTextCompare"
 VList {} -> "VList"
 VListLit {} -> "VListLit"
 VListAppend {} -> "VListAppend"
 VListBuild {} -> "VListBuild"
 VListFold {} -> "VListFold"
 VListLength {} -> "VListLength"
 VListHead {} -> "VListHead"
 VListLast {} -> "VListLast"
 VListIndexed {} -> "VListIndexed"
 VListReverse {} -> "VListReverse"
 VListPermutations {} -> "VListPermutations"
 VListChoose {} -> "VListChoose"
 VListFixed {} -> "VListFixed"
 VListFixedLit {} -> "VListFixedLit"
 VListFixedFromList {} -> "VListFixedFromList"
 VListFixedToList {} -> "VListFixedToList"
 VListFixedHead {} -> "VListFixedHead"
 VListFixedTail {} -> "VListFixedTail"

 VSym t -> "VSym " ++ Text.unpack t
 VSymLit t -> "VSymLit " ++ Text.unpack t
 VSymFromText {} -> "VSymFromText"
 VSymToText {} -> "VSymToText"

 VSZ {} -> "VSZ"
 VSS {} -> "VSS"
 VSZLit {} -> "VSZLit"
 VSSLit {} -> "VSSLit"

 VSSFromNonZero {} -> "VSSFromNonZero"
 VSSToNonZero {} -> "VSSToNonZero"
 VSSToNatural {} -> "VSSToNatural"
 VSSAdd {} -> "VSSAdd"
 VSSSubtract {} -> "VSSSubtract"
 VSSEqual {} -> "VSSEqual"
 VSSLessThan {} -> "VSSLessThan"

 VProof a -> "VProof a=" ++ dumpVal a
 VProofLit {} -> "VProofLit"
 VProofToBool a -> "VProofToBool a=" ++ dumpVal a
 VProofFromBool a b -> "VProofFromBool a=" ++ dumpVal a ++ " b=" ++ dumpVal b

 VPVoid a -> "VPVoid  a=" ++ dumpVal a
 VPVoidUndefined a -> "VPVoidUndefined a=" ++ dumpVal a
 VPVoidError a b -> "VPVoidError a=" ++ dumpVal a ++ " b=" ++ dumpVal b
 VPVoidKindUndefined a -> "VPVoidKindUndefined a=" ++ dumpVal a

 VOptional {} -> "VOptional"
 VSome {} -> "VSome"
 VNone {} -> "VNone"
 VRecord m -> "VRecord " ++ Map.foldMapWithKey (\k a -> "\n\tkey=" ++ Text.unpack k ++ " val=" ++ dumpVal a) m
 VRecordLit m -> "VRecordLit " ++ Map.foldMapWithKey (\k a -> "\n\tkey=" ++ Text.unpack k ++ " val=" ++ dumpVal a) m
 VUnion {} -> "VUnion"
 VCombine {} -> "VCombine"
 VCombineTypes {} -> "VCombineTypes"
 VPrefer {} -> "VPrefer"
 VMerge {} -> "VMerge"
 VToMap {} -> "VToMap"
 VField v t -> "VField " ++ dumpVal v ++ " t=" ++ Text.unpack t
 VInject {} -> "VInject"
 VProject {} -> "VProject"
 VAssert {} -> "VAssert"
 VEquivalent {} -> "VEquivalent"
 VEmbed {} -> "VEmbed"

getSSCntVal :: Val a -> Either String NonZero
getSSCntVal n =
  Data.Function.fix
    (\f cnt -> \case
                  VSZ -> Right (mkNonZeroUnsafe cnt)
                  VSS m -> f (cnt+1) m
                  x -> Left $ "getSSCntVal expected VSS or VSZ but found " ++ dumpVal x
    ) 1 n

choose :: [a] -> Int -> [[a]]
choose _   0    = [[]]
choose []  _    = []
choose (x:xs) n = map (x:) (choose xs (n-1)) ++ choose xs n

select :: [a] -> [(a,[a])]
select [] = []
select (a:as) = (a,as) : [ (b,a:bs) | (b,bs) <- select as ]

perms :: [a] -> [[a]]
perms [] = [[]]
perms xs = [ y:zs | (y,ys) <- select xs, zs <- perms ys]