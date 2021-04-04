-- remove tracing
{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TupleSections      #-}
{-# LANGUAGE LambdaCase          #-}

module Dhall.Normalize (
      alphaNormalize
    , normalize
    , normalizeWith
    , normalizeWithM
    , Normalizer
    , NormalizerM
    , ReifiedNormalizer (..)
    , judgmentallyEqual
    , subst
    , shift
    , isNormalized
    , isNormalizedWith
    , freeIn
    , getSSCntExpr
    , makeSSExpr
    ) where

import Control.Applicative   (empty)
import qualified Data.Bits
import qualified Data.Char
import Data.Foldable
import Data.Functor.Identity (Identity (..))
import qualified Data.Ord
import Data.Sequence         (ViewL (..), ViewR (..))
import Data.Traversable
import Instances.TH.Lift     ()
import Prelude               hiding (succ)

import qualified Data.Ratio
import Data.Ratio ((%))
import Dhall.Syntax
    ( Binding (Binding)
    , Chunks (..)
    , DhallDouble (..)
    , Expr (..)
    , PreferAnnotation (..)
    , RecordField (..)
    , Var (..)
    , NonZero(..)
    , DateTime(..)
    , Regex(..)
    , compileRegex
    , compileRegexUnsafe
    , dateTimeToUtc
    , utcToDateTime
    , makeSSExpr
    , mkNonZeroUnsafe
    )

import qualified Data.Sequence
import qualified Data.Set
import qualified Data.Text
import qualified Data.Text.Encoding
import qualified Data.Time
import qualified Data.Time.Calendar
import qualified Data.Time.Calendar.WeekDate
import qualified Data.Time.Calendar.OrdinalDate
import qualified Dhall.Eval    as Eval
import qualified Dhall.Map
import qualified Dhall.Set
import qualified Dhall.Syntax  as Syntax
import qualified Lens.Family   as Lens

import qualified Dhall.Parser.Token as Dhall.Parser.Token
import qualified Dhall.Parser.Combinators as Dhall.Parser.Combinators
import qualified Text.Megaparsec

import qualified Text.Regex.PCRE.Heavy as RH
--import Debug.Trace

{-| Returns `True` if two expressions are α-equivalent and β-equivalent and
    `False` otherwise

    `judgmentallyEqual` can fail with an `error` if you compare ill-typed
    expressions
-}
judgmentallyEqual :: Eq a => Expr s a -> Expr t a -> Bool
judgmentallyEqual = Eval.judgmentallyEqual
{-# INLINE judgmentallyEqual #-}

{-| `shift` is used by both normalization and type-checking to avoid variable
    capture by shifting variable indices

    For example, suppose that you were to normalize the following expression:

> λ(a : Type) → λ(x : a) → (λ(y : a) → λ(x : a) → y) x

    If you were to substitute @y@ with @x@ without shifting any variable
    indices, then you would get the following incorrect result:

> λ(a : Type) → λ(x : a) → λ(x : a) → x  -- Incorrect normalized form

    In order to substitute @x@ in place of @y@ we need to `shift` @x@ by @1@ in
    order to avoid being misinterpreted as the @x@ bound by the innermost
    lambda.  If we perform that `shift` then we get the correct result:

> λ(a : Type) → λ(x : a) → λ(x : a) → x@1

    As a more worked example, suppose that you were to normalize the following
    expression:

>     λ(a : Type)
> →   λ(f : a → a → a)
> →   λ(x : a)
> →   λ(x : a)
> →   (λ(x : a) → f x x@1) x@1

    The correct normalized result would be:

>     λ(a : Type)
> →   λ(f : a → a → a)
> →   λ(x : a)
> →   λ(x : a)
> →   f x@1 x

    The above example illustrates how we need to both increase and decrease
    variable indices as part of substitution:

    * We need to increase the index of the outer @x\@1@ to @x\@2@ before we
      substitute it into the body of the innermost lambda expression in order
      to avoid variable capture.  This substitution changes the body of the
      lambda expression to @(f x\@2 x\@1)@

    * We then remove the innermost lambda and therefore decrease the indices of
      both @x@s in @(f x\@2 x\@1)@ to @(f x\@1 x)@ in order to reflect that one
      less @x@ variable is now bound within that scope

    Formally, @(shift d (V x n) e)@ modifies the expression @e@ by adding @d@ to
    the indices of all variables named @x@ whose indices are greater than
    @(n + m)@, where @m@ is the number of bound variables of the same name
    within that scope

    In practice, @d@ is always @1@ or @-1@ because we either:

    * increment variables by @1@ to avoid variable capture during substitution
    * decrement variables by @1@ when deleting lambdas after substitution

    @n@ starts off at @0@ when substitution begins and increments every time we
    descend into a lambda or let expression that binds a variable of the same
    name in order to avoid shifting the bound variables by mistake.
-}
shift :: Int -> Var -> Expr s a -> Expr s a
shift d (V x n) (Var (V x' n')) = Var (V x' n'')
  where
    n'' = if x == x' && n <= n' then n' + d else n'
shift d (V x n) (Lam x' _A b) = Lam x' _A' b'
  where
    _A' = shift d (V x n ) _A
    b'  = shift d (V x n') b
      where
        n' = if x == x' then n + 1 else n
shift d (V x n) (Pi x' _A _B) = Pi x' _A' _B'
  where
    _A' = shift d (V x n ) _A
    _B' = shift d (V x n') _B
      where
        n' = if x == x' then n + 1 else n
shift d (V x n) (Let (Binding src0 f src1 mt src2 r) e) =
    Let (Binding src0 f src1 mt' src2 r') e'
  where
    e' = shift d (V x n') e
      where
        n' = if x == f then n + 1 else n

    mt' = fmap (fmap (shift d (V x n))) mt
    r'  =             shift d (V x n)  r
shift d v expression = Lens.over Syntax.subExpressions (shift d v) expression

{-| Substitute all occurrences of a variable with an expression

> subst x C B  ~  B[x := C]
-}
subst :: Var -> Expr s a -> Expr s a -> Expr s a
subst _ _ (Const a) = Const a
subst (V x n) e (Lam y _A b) = Lam y _A' b'
  where
    _A' = subst (V x n )                  e  _A
    b'  = subst (V x n') (shift 1 (V y 0) e)  b
    n'  = if x == y then n + 1 else n
subst (V x n) e (Pi y _A _B) = Pi y _A' _B'
  where
    _A' = subst (V x n )                  e  _A
    _B' = subst (V x n') (shift 1 (V y 0) e) _B
    n'  = if x == y then n + 1 else n
subst v e (Var v') = if v == v' then e else Var v'
subst (V x n) e (Let (Binding src0 f src1 mt src2 r) b) =
    Let (Binding src0 f src1 mt' src2 r') b'
  where
    b' = subst (V x n') (shift 1 (V f 0) e) b
      where
        n' = if x == f then n + 1 else n

    mt' = fmap (fmap (subst (V x n) e)) mt
    r'  =             subst (V x n) e  r
subst x e expression = Lens.over Syntax.subExpressions (subst x e) expression

{-| This function is used to determine whether folds like @Natural/fold@ or
    @List/fold@ should be lazy or strict in their accumulator based on the type
    of the accumulator

    If this function returns `True`, then they will be strict in their
    accumulator since we can guarantee an upper bound on the amount of work to
    normalize the accumulator on each step of the loop.  If this function
    returns `False` then they will be lazy in their accumulator and only
    normalize the final result at the end of the fold
-}
boundedType :: Expr s a -> Bool
boundedType Bool             = True
boundedType Natural          = True
boundedType NonZero          = True
boundedType DateTime         = True
boundedType Regex            = True
boundedType Rational         = True
boundedType Integer          = True
boundedType Double           = True
boundedType Text             = True
boundedType (App List _)     = False
boundedType (App ListFixed _) = False

boundedType (App (Sym _) _) = False

boundedType SZ = True
boundedType (App SS _) = False
boundedType (App Proof t) = boundedType t
boundedType (App PVoid t) = boundedType t

boundedType (App Optional t) = boundedType t
boundedType (Record kvs)     = all (boundedType . recordFieldValue) kvs
boundedType (Union kvs)      = all (all boundedType) kvs
boundedType _                = False

{-| α-normalize an expression by renaming all bound variables to @\"_\"@ and
    using De Bruijn indices to distinguish them

>>> alphaNormalize (Lam "a" (Const Type) (Lam "b" (Const Type) (Lam "x" "a" (Lam "y" "b" "x"))))
Lam "_" (Const Type) (Lam "_" (Const Type) (Lam "_" (Var (V "_" 1)) (Lam "_" (Var (V "_" 1)) (Var (V "_" 1)))))

    α-normalization does not affect free variables:

>>> alphaNormalize "x"
Var (V "x" 0)

-}
alphaNormalize :: Expr s a -> Expr s a
alphaNormalize = Eval.alphaNormalize
{-# INLINE alphaNormalize #-}

{-| Reduce an expression to its normal form, performing beta reduction

    `normalize` does not type-check the expression.  You may want to type-check
    expressions before normalizing them since normalization can convert an
    ill-typed expression into a well-typed expression.

    `normalize` can also fail with `error` if you normalize an ill-typed
    expression
-}
normalize :: Eq a => Expr s a -> Expr t a
normalize = Eval.normalize
{-# INLINE normalize #-}

{-| Reduce an expression to its normal form, performing beta reduction and applying
    any custom definitions.

    `normalizeWith` is designed to be used with function `typeWith`. The `typeWith`
    function allows typing of Dhall functions in a custom typing context whereas
    `normalizeWith` allows evaluating Dhall expressions in a custom context.

    To be more precise `normalizeWith` applies the given normalizer when it finds an
    application term that it cannot reduce by other means.

    Note that the context used in normalization will determine the properties of normalization.
    That is, if the functions in custom context are not total then the Dhall language, evaluated
    with those functions is not total either.

    `normalizeWith` can fail with an `error` if you normalize an ill-typed
    expression
-}
normalizeWith :: Eq a => Maybe (ReifiedNormalizer a) -> Expr s a -> Expr t a
normalizeWith (Just ctx) t = runIdentity (normalizeWithM (getReifiedNormalizer ctx) t)
normalizeWith _          t = Eval.normalize t

{-| This function generalizes `normalizeWith` by allowing the custom normalizer
    to use an arbitrary `Monad`

    `normalizeWithM` can fail with an `error` if you normalize an ill-typed
    expression
-}
normalizeWithM
    :: (Monad m, Eq a) => NormalizerM m a -> Expr s a -> m (Expr t a)
normalizeWithM ctx e0 = loop (Syntax.denote e0)
 where
 loop e =  case e of
    Const k -> pure (Const k)
    Var v -> pure (Var v)
    Lam x _A b -> Lam x <$> _A' <*> b'
      where
        _A' = loop _A
        b'  = loop b
    Pi x _A _B -> Pi x <$> _A' <*> _B'
      where
        _A' = loop _A
        _B' = loop _B
    App f a -> do
      res <- ctx (App f a)
      case res of
          Just e1 -> loop e1
          Nothing -> do
              f' <- loop f
              a' <- loop a
              case f' of
                Lam x _A b₀ -> do

                    let a₂ = shift 1 (V x 0) a'
                    let b₁ = subst (V x 0) a₂ b₀
                    let b₂ = shift (-1) (V x 0) b₁

                    loop b₂
                _ ->
                  case App f' a' of
                    App NonZeroShow (NonZeroLit (NonZeroC n)) ->
                        pure (TextLit (Chunks [] (Data.Text.pack ('!' : show n))))

                    App NonZeroClamp (NaturalLit n)
                        | n > 0 -> pure (NonZeroLit (NonZeroC n))
                        | otherwise -> pure (NonZeroLit (NonZeroC 1))

                    App (App NonZeroDiv (IntegerLit x)) (NonZeroLit (NonZeroC y))
                        -> pure (IntegerLit (div x (fromIntegral y)))

                    App (App NonZeroMod (IntegerLit x)) (NonZeroLit (NonZeroC y))
                        -> pure (IntegerLit (mod x (fromIntegral y)))

                    App (App NonZeroLog (NonZeroLit (NonZeroC base))) (NonZeroLit (NonZeroC n))
                        -> pure (NaturalLit (ceiling (logBase (fromIntegral base + 1) (fromIntegral n) :: Double)))

                    App (App NonZeroAdd (NonZeroLit (NonZeroC x))) (NonZeroLit (NonZeroC y))
                        -> pure (NonZeroLit (mkNonZeroUnsafe (x + y)))

                    App (App NonZeroMultiply (NonZeroLit (NonZeroC x))) (NonZeroLit (NonZeroC y))
                        -> pure (NonZeroLit (mkNonZeroUnsafe (x * y)))

                    App NonZeroToNatural (NonZeroLit (NonZeroC n)) -> pure (NaturalLit n)

                    App NonZeroToInteger (NonZeroLit (NonZeroC n)) -> pure (IntegerLit (fromIntegral n))

                    App NonZeroParse (TextLit (Chunks [] t)) -> loop o
                      where
                        o = case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.nonZeroLiteral <* Text.Megaparsec.eof) "?" t of
                              Left _ -> App None NonZero
                              Right r -> Some (NonZeroLit r)

                    App DateTimeShow (DateTimeLit n) ->
                        let x = dateTimeToUtc n
                            y = Data.Time.formatTime Data.Time.defaultTimeLocale "%FT%T" x
                        in pure (TextLit (Chunks [] (Data.Text.pack ('^':y))))

                    App DateTimeParse (TextLit (Chunks [] t)) -> loop o
                      where
                        o = case Dhall.Parser.Token.dateTimeParse (Data.Text.unpack t) of
                              Left _   -> App None DateTime
                              Right tm -> Some (DateTimeLit tm)

                    App DateTimeFromSeconds (IntegerLit n) -> pure (DateTimeLit (DateTimeC n))
                    App DateTimeToSeconds (DateTimeLit (DateTimeC n)) -> pure (IntegerLit n)

                    App (App DateTimeAddYears (IntegerLit n)) (DateTimeLit m)
                        -> let u = dateTimeToUtc m
                               d = u { Data.Time.utctDay = Data.Time.addGregorianYearsClip n (Data.Time.utctDay u) }
                           in pure $ DateTimeLit (utcToDateTime d)

                    App (App DateTimeAddMonths (IntegerLit n)) (DateTimeLit m)
                        -> let u = dateTimeToUtc m
                               d = u { Data.Time.utctDay = Data.Time.addGregorianMonthsClip n (Data.Time.utctDay u) }
                           in pure $ DateTimeLit (utcToDateTime d)

                    App (App DateTimeAddDays (IntegerLit n)) (DateTimeLit m)
                        -> let u = dateTimeToUtc m
                               d = u { Data.Time.utctDay = Data.Time.addDays n (Data.Time.utctDay u) }
                           in pure $ DateTimeLit (utcToDateTime d)

                    App (App (App DateTimeFromWeek (IntegerLit y)) (NonZeroLit (NonZeroC w))) (NonZeroLit (NonZeroC d)) ->
                      let dy = Data.Time.Calendar.WeekDate.fromWeekDate y (fromIntegral w) (fromIntegral d)
                      in pure (DateTimeLit (utcToDateTime (Data.Time.UTCTime dy 0)))

                    App DateTimeToWeek (DateTimeLit n) ->
                      let u = dateTimeToUtc n
                          (y,w,d) = Data.Time.Calendar.WeekDate.toWeekDate (Data.Time.utctDay u)
                      in pure $ RecordLit (Dhall.Map.unorderedFromList
                           [ ("year", Syntax.makeRecordField $ IntegerLit y)
                           , ("week", Syntax.makeRecordField $ NonZeroLit (mkNonZeroUnsafe (fromIntegral w)))
                           , ("day", Syntax.makeRecordField $ NaturalLit (fromIntegral d-1))
                           ])

                    App (App (App (App (App (App DateTimeToDate (IntegerLit y)) (NonZeroLit (NonZeroC m))) (NonZeroLit (NonZeroC d))) (NaturalLit hh)) (NaturalLit mm)) (NaturalLit ss) ->
                      let dy = Data.Time.fromGregorian y (fromIntegral m) (fromIntegral d)
                          hms = (min 23 hh * 3600) + (min 59 mm * 60) + (min 59 ss)
                      in pure (DateTimeLit (utcToDateTime (Data.Time.UTCTime dy (fromIntegral hms))))

                    App DateTimeFromDate (DateTimeLit n) ->
                      let u = dateTimeToUtc n
                          (y,m,d) = Data.Time.toGregorian (Data.Time.utctDay u)
                          (hh,ms) = fromIntegral (truncate (Data.Time.utctDayTime u) :: Integer) `divMod` 3600
                          (mm,ss) = ms `divMod` (60 :: Integer)
                      in pure $ RecordLit (Dhall.Map.unorderedFromList
                            [ ("year", Syntax.makeRecordField $ IntegerLit y)
                            , ("month", Syntax.makeRecordField $ NonZeroLit (mkNonZeroUnsafe (fromIntegral m)) )
                            , ("day", Syntax.makeRecordField $ NonZeroLit (mkNonZeroUnsafe (fromIntegral d)))
                            , ("hour", Syntax.makeRecordField $ NaturalLit (fromIntegral hh))
                            , ("minute", Syntax.makeRecordField $ NaturalLit (fromIntegral mm))
                            , ("second", Syntax.makeRecordField $ NaturalLit (fromIntegral ss))
                            ])

                    App (App DateTimeLastDayOfMonth (IntegerLit y)) (NonZeroLit (NonZeroC m)) ->
                      let dy = Data.Time.Calendar.gregorianMonthLength y (fromIntegral m)
                      in pure (NonZeroLit (mkNonZeroUnsafe (fromIntegral dy)))

                    App DateTimeGetJulianDay (DateTimeLit n) ->
                      let u = dateTimeToUtc n
                          (_,d) = Data.Time.Calendar.OrdinalDate.toOrdinalDate (Data.Time.utctDay u)
                      in pure $ NonZeroLit (mkNonZeroUnsafe (fromIntegral d))

                    App (App DateTimeSetJulianDay (IntegerLit m)) (NonZeroLit (NonZeroC n))
                        -> let d = Data.Time.UTCTime (Data.Time.Calendar.OrdinalDate.fromOrdinalDate m (fromIntegral n)) 0
                           in pure $ DateTimeLit (utcToDateTime d)

                    App RegexShow (RegexLit (RegexC y)) ->
                        pure (TextLit (Chunks [] y))

                    App (App RegexMatch (RegexLit (RegexC m))) (TextLit (Chunks [] n)) ->
                        let r = compileRegexUnsafe m
                            v = Data.Text.Encoding.encodeUtf8 n
                        in pure (BoolLit (v RH.=~ r))

                    App (App (App RegexScan (RegexLit (RegexC m))) (TextLit (Chunks [] n))) (NonZeroLit (NonZeroC i)) -> loop o
                      where
                        o = let emptyInnerList = ListLit (Just Text) mempty
                                emptyList = let inner xs = ListLit (Just (Record (Dhall.Map.unorderedFromList xs))) mempty
                                            in inner [("_1", Syntax.makeRecordField $ Text), ("_2", Syntax.makeRecordField $ emptyInnerList)]
                            in let r = compileRegexUnsafe m
                               in case take (fromIntegral i) (RH.scan r n) of
                                     [] -> emptyList
                                     as@(_:_) ->
                                       let ret = flip map as $ \(x,ys') ->
                                                   let zzzz = case ys' of
                                                                [] -> emptyInnerList
                                                                ys@(_:_) -> ListLit Nothing (Data.Sequence.fromList (map (\v -> TextLit (Chunks [] v)) ys))
                                                   in RecordLit (Dhall.Map.unorderedFromList [("_1", Syntax.makeRecordField $ TextLit (Chunks [] x)), ("_2", Syntax.makeRecordField $ zzzz)])
                                       in ListLit Nothing (Data.Sequence.fromList ret)

                    App (App (App RegexSplit (RegexLit (RegexC m))) (TextLit (Chunks [] n))) (NonZeroLit (NonZeroC i)) -> loop o
                      where
                        o = let emptyList = ListLit (Just Text) mempty
                                r = compileRegexUnsafe m
                            in case take (fromIntegral i) (RH.split r n) of
                                 [] -> emptyList
                                 as@(_:_) -> ListLit Nothing (Data.Sequence.fromList (map (\v -> TextLit (Chunks [] v)) as))

                    App (App (App RegexReplace (RegexLit (RegexC m))) (TextLit (Chunks [] n))) (TextLit (Chunks [] p)) -> loop o
                      where
                        o = let r = compileRegexUnsafe m
                                t = RH.gsub r n p
                            in TextLit (Chunks [] t)

                    -- cant normalize further cos of callback
                    -- App (App (App RegexReplix (RegexLit (RegexC m))) fn@(Lam _ Text _)) (TextLit (Chunks [] p))

                    App RegexParse (TextLit (Chunks [] m)) -> loop o
                      where
                        o = case compileRegex m of
                              Left _ -> App None Regex
                              Right _ -> Some (RegexLit (RegexC m))

                    App RegexToText (RegexLit (RegexC y)) ->
                        pure (TextLit (Chunks [] y))

                    App RationalShow (RationalLit y) ->
                        pure (TextLit (Chunks [] (Syntax.showDhallRational y)))

                    App (App RationalFromDouble (DoubleLit (DhallDouble m))) (DoubleLit (DhallDouble n)) ->
                        pure (RationalLit (Data.Ratio.approxRational m n))

                    App RationalToDouble (RationalLit y) ->
                        pure (DoubleLit (DhallDouble (realToFrac y)))

                    App RationalFromRational (RationalLit r) ->
                        pure (RecordLit (Dhall.Map.unorderedFromList
                              [ ("num", Syntax.makeRecordField $ IntegerLit (Data.Ratio.numerator r))
                              , ("den", Syntax.makeRecordField $ NonZeroLit (Syntax.mkNonZeroUnsafe (fromIntegral (Data.Ratio.denominator r))))
                              ]
                        ))
                    App RationalParse (TextLit (Chunks [] t)) -> loop o
                      where
                        o = case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.rationalLiteral <* Text.Megaparsec.eof) "?" t of
                              Left _ -> App None Rational
                              Right r -> Some (RationalLit r)

                    App (App (App (App NaturalFold (NaturalLit n0)) t) succ') zero -> do
                      t' <- loop t
                      if boundedType t' then strict else lazy
                      where
                        -- Use an `Integer` for the loop, due to the following
                        -- issue:
                        --
                        -- https://github.com/ghcjs/ghcjs/issues/782
                        strict =       strictLoop (fromIntegral n0 :: Integer)
                        lazy   = loop (  lazyLoop (fromIntegral n0 :: Integer))

                        strictLoop 0 = loop zero
                        strictLoop !n = App succ' <$> strictLoop (n - 1) >>= loop

                        lazyLoop 0 = zero
                        lazyLoop !n = App succ' (lazyLoop (n - 1))
                    App NaturalBuild g -> loop (App (App (App g Natural) succ) zero)
                      where
                        succ = Lam "n" Natural (NaturalPlus "n" (NaturalLit 1))

                        zero = NaturalLit 0
                    App NaturalIsZero (NaturalLit n) -> pure (BoolLit (n == 0))
                    App NaturalEven (NaturalLit n) -> pure (BoolLit (even n))
                    App NaturalOdd (NaturalLit n) -> pure (BoolLit (odd n))
                    App NaturalToInteger (NaturalLit n) -> pure (IntegerLit (toInteger n))
                    App NaturalShow (NaturalLit n) ->
                        pure (TextLit (Chunks [] (Data.Text.pack (show n))))
                    App NaturalParse (TextLit (Chunks [] t)) -> loop o
                      where
                        o = case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.naturalLiteral <* Text.Megaparsec.eof) "?" t of
                              Left _ -> App None Natural
                              Right r -> Some (NaturalLit r)

                    App NaturalToBits (NaturalLit n) -> loop o
                      where
                        o = let mx = if n <= 0 then 0 else truncate (log (fromIntegral n) / log 2 :: Double)
                                bs = reverse $ map (BoolLit . Data.Bits.testBit n) [ 0 .. mx ]
                            in ListLit Nothing (Data.Sequence.fromList bs)


                    App (App NaturalSubtract (NaturalLit x)) (NaturalLit y)
                        -- Use an `Integer` for the subtraction, due to the
                        -- following issue:
                        --
                        -- https://github.com/ghcjs/ghcjs/issues/782
                        | y >= x ->
                            pure (NaturalLit (fromIntegral (subtract (fromIntegral x :: Integer) (fromIntegral y :: Integer))))
                        | otherwise ->
                            pure (NaturalLit 0)
                    App (App NaturalSubtract (NaturalLit 0)) y -> pure y
                    App (App NaturalSubtract _) (NaturalLit 0) -> pure (NaturalLit 0)
                    App (App NaturalSubtract x) y | Eval.judgmentallyEqual x y -> pure (NaturalLit 0)

                    App (App NaturalGcd (NaturalLit x)) (NaturalLit y)
                        -> pure (NaturalLit (gcd x y))

                    App (App IntegerAdd (IntegerLit x)) (IntegerLit y)
                        -> pure (IntegerLit (x + y))
                    App (App IntegerAdd (IntegerLit 0)) y -> pure y
                    App (App IntegerAdd x) (IntegerLit 0) -> pure x

                    App (App IntegerMultiply (IntegerLit x)) (IntegerLit y)
                        -> pure (IntegerLit (x * y))
                    App (App IntegerMultiply (IntegerLit 1)) y -> pure y
                    App (App IntegerMultiply x) (IntegerLit 1) -> pure x

                    App (App IntegerAnd (IntegerLit x)) (IntegerLit y)
                        -> pure (IntegerLit (x Data.Bits..&. y))
                    App (App IntegerAnd z@(IntegerLit 0)) _ -> pure z
                    App (App IntegerAnd _) z@(IntegerLit 0) -> pure z

                    App (App IntegerXor (IntegerLit x)) (IntegerLit y)
                        -> pure (IntegerLit (Data.Bits.xor x y))
                    App (App IntegerXor (IntegerLit 0)) y -> pure y
                    App (App IntegerXor x) (IntegerLit 0) -> pure x

                    App IntegerClamp (IntegerLit n)
                        | 0 <= n -> pure (NaturalLit (fromInteger n))
                        | otherwise -> pure (NaturalLit 0)

                    App IntegerNegate (IntegerLit n) ->
                        pure (IntegerLit (negate n))
                    App IntegerShow (IntegerLit n)
                        | 0 <= n    -> pure (TextLit (Chunks [] ("+" <> Data.Text.pack (show n))))
                        | otherwise -> pure (TextLit (Chunks [] (Data.Text.pack (show n))))
                    -- `(read . show)` is used instead of `fromInteger` because `read` uses
                    -- the correct rounding rule.
                    -- See https://gitlab.haskell.org/ghc/ghc/issues/17231.
                    App IntegerParse (TextLit (Chunks [] t)) -> loop o
                      where
                        o = case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.integerLiteral <* Text.Megaparsec.eof) "?" t of
                              Left _ -> App None Integer
                              Right r -> Some (IntegerLit r)
                    App IntegerToDouble (IntegerLit n) -> pure (DoubleLit ((DhallDouble . read . show) n))
                    App DoubleShow (DoubleLit (DhallDouble n)) ->
                        pure (TextLit (Chunks [] (Data.Text.pack (show n))))
                    App DoubleParse (TextLit (Chunks [] t)) -> loop o
                      where
                        o = case Text.Megaparsec.parse (Dhall.Parser.Combinators.unParser Dhall.Parser.Token.doubleLiteral <* Text.Megaparsec.eof) "?" t of
                              Left _ -> App None Double
                              Right r -> Some (DoubleLit (DhallDouble r))
                    App (App ListBuild _A₀) g -> loop (App (App (App g list) cons) nil)
                      where
                        _A₁ = shift 1 "a" _A₀

                        list = App List _A₀

                        cons =
                            Lam "a" _A₀
                                (Lam "as"
                                    (App List _A₁)
                                    (ListAppend (ListLit Nothing (pure "a")) "as")
                                )

                        nil = ListLit (Just (App List _A₀)) empty
                    App (App (App (App (App ListFold _) (ListLit _ xs)) t) cons) nil -> do
                      t' <- loop t
                      if boundedType t' then strict else lazy
                      where
                        strict =       foldr strictCons strictNil xs
                        lazy   = loop (foldr   lazyCons   lazyNil xs)

                        strictNil = loop nil
                        lazyNil   =      nil

                        strictCons y ys =
                          App (App cons y) <$> ys >>= loop
                        lazyCons   y ys =       App (App cons y) ys
                    App (App ListLength _) (ListLit _ ys) ->
                        pure (NaturalLit (fromIntegral (Data.Sequence.length ys)))
                    App (App ListHead t) (ListLit _ ys) -> loop o
                      where
                        o = case Data.Sequence.viewl ys of
                                y :< _ -> Some y
                                _      -> App None t
                    App (App ListLast t) (ListLit _ ys) -> loop o
                      where
                        o = case Data.Sequence.viewr ys of
                                _ :> y -> Some y
                                _      -> App None t
                    App (App ListIndexed _A₀) (ListLit _ as₀) -> loop (ListLit t as₁)
                      where
                        as₁ = Data.Sequence.mapWithIndex adapt as₀

                        _A₂ = Record (Dhall.Map.fromList kts)
                          where
                            kts = [ ("index", Syntax.makeRecordField Natural)
                                  , ("value", Syntax.makeRecordField _A₀)
                                  ]

                        t | null as₀  = Just (App List _A₂)
                          | otherwise = Nothing

                        adapt n a_ =
                            RecordLit (Dhall.Map.fromList kvs)
                          where
                            kvs = [ ("index", Syntax.makeRecordField $ NaturalLit (fromIntegral n))
                                  , ("value", Syntax.makeRecordField a_)
                                  ]
                    App (App ListReverse _) (ListLit t xs) ->
                        loop (ListLit t (Data.Sequence.reverse xs))
                    App (App ListPermutations _) (ListLit t xs) ->
                       if null xs then loop (ListLit (fmap (App List) t) mempty)
                       else
                        let ff = map (ListLit Nothing . Data.Sequence.fromList)
                        in loop (ListLit t (Data.Sequence.fromList . ff . Eval.perms . toList $ xs))

                    App (App (App ListChoose t) (NaturalLit x)) (ListLit _ xs)
                        -> pure $ case Eval.choose (toList xs) (fromIntegral x) of
                          [] -> ListLit (Just (App List t)) mempty
                          o -> ListLit Nothing (Data.Sequence.fromList
                                 (map (\z -> ListLit
                                               (if null z then Just t else Nothing)
                                               (Data.Sequence.fromList z)
                                      ) o
                                  )
                               )

                    App (App (App (App ListFixedFromList sz') _a) def') (ListLit _ as) -> do
                        def <- loop def'
                        sz <- loop sz'
                        let NonZeroC cnt = either error id (getSSCntExpr "Normalize: ListFixedFromList" sz)
                        let (w,ws) =
                               case Data.Sequence.viewl as of
                                 EmptyL -> (def, Data.Sequence.replicate (fromIntegral (cnt-1)) def)
                                 z :< zs ->
                                   let df = 1 + length zs - fromIntegral cnt
                                   in (z,) $ case compare df 0 of
                                              LT -> zs <> Data.Sequence.replicate (abs df) def
                                              EQ -> zs
                                              GT -> Data.Sequence.take (fromIntegral (cnt-1)) zs
                        loop (ListFixedLit w ws)

                    App (App (App ListFixedToList _) _) (ListFixedLit x xs) ->
                        loop (ListLit Nothing (x Data.Sequence.:<| xs))

                    App (App (App ListFixedHead _) _) (ListFixedLit x _xs) ->
                        loop x

                    App (App (App ListFixedTail _) t) (ListFixedLit _x xs) ->
                      loop o
                      where o = if null xs then ListLit (Just t) mempty
                                else ListLit Nothing xs

                    App SymFromText (TextLit (Chunks [] t)) -> do
                        pure (Sym t)

                    App SymToText (Sym t) ->
                        loop (TextLit (Chunks [] t))

                    App SSFromNonZero (NonZeroLit n) -> do
                        pure (makeSSExpr n)

                    App SSToNonZero SZ ->
                        loop (NonZeroLit (mkNonZeroUnsafe 1))

                    App SSToNonZero z@(App SS _) ->
                       let cnt = either error id (getSSCntExpr "Normalize: SSToNonZero" z)
                       in loop (NonZeroLit cnt)

                    App SSToNatural SZ ->
                        loop (NaturalLit 1)

                    App SSToNatural z@(App SS _) ->
                       let cnt = either error unNonZero (getSSCntExpr "Normalize: SSToNatural" z)
                       in loop (NaturalLit cnt)

                    App (App SSAdd SZ) SZ -> loop (App SS SZ)
                    App (App SSAdd SZ) n@(App SS _) -> loop (App SS n)
                    App (App SSAdd m@(App SS _)) SZ -> loop (App SS m)
                    App (App SSAdd m@(App SS _)) n@(App SS _) ->
                       let (x,y) = getBothSSCntExpr "SS/add" m n
                       in loop (makeSSExpr (mkNonZeroUnsafe (fromIntegral (x+y))))

                    --App (App SSSubtract SZ) SZ
                    App (App SSSubtract SZ) (App SS n) -> loop n
                    --App (App SSSubtract m@(App SS _)) SZ
                    z@(App (App SSSubtract m@(App SS _)) n@(App SS _)) ->
                       let (x,y) = getBothSSCntExpr "SS/subtract" m n
                       in if x < y then loop (makeSSExpr (mkNonZeroUnsafe (fromIntegral (subtract x y))))
                           else pure z

                    App (App SSEqual SZ) SZ -> loop (App Proof (Sym "SS/equal: SZ == SZ"))
                    App (App SSEqual SZ) (App SS _) -> loop (App PVoid (Sym "SS/equal: SZ /= SS"))
                    App (App SSEqual (App SS _)) SZ -> loop (App PVoid (Sym "SS/equal: SS /= SZ"))
                    App (App SSEqual m@(App SS _)) n@(App SS _) ->
                       let (x,y) = getBothSSCntExpr "SS/equal" m n
                           x1 = Data.Text.pack (show x)
                           x2 = Data.Text.pack (show y)
                       in if x == y then loop (App Proof (Sym ("SS/equal " <> x1 <> " == " <> x2)))
                          else loop (App PVoid (Sym ("SS/equal " <> x1 <> " /= " <> x2)))

                    App (App SSLessThan SZ) SZ -> loop (App PVoid (Sym "SS/lessThan: SZ is not less than SZ"))
                    App (App SSLessThan SZ) (App SS _) -> loop (App Proof (Sym "SS/lessThan: SZ < SS"))
                    App (App SSLessThan (App SS _)) SZ -> loop (App PVoid (Sym "SS/lessThan: SS is not less than SZ"))
                    App (App SSLessThan m@(App SS _)) n@(App SS _) ->
                       let (x,y) = getBothSSCntExpr "SS/lessThan" m n
                           x1 = Data.Text.pack (show x)
                           x2 = Data.Text.pack (show y)
                       in if x < y then loop (App Proof (Sym ("SS/lessThan: " <> x1 <> " < " <> x2)))
                          else loop (App PVoid (Sym ("SS/lessThan: " <> x1 <> " is not less than " <> x2)))

                    App ProofToBool (App Proof _) -> loop (BoolLit True)
                    App ProofToBool (App PVoid _) -> loop (BoolLit False)

--                    App (App ProofFromBool msg@(Sym _)) (BoolLit True) -> loop (App Proof msg)
--                    App (App ProofFromBool msg@(Sym _)) (BoolLit False) -> loop (App PVoid msg)

                    App (App ProofFromBool msg) (BoolLit True) ->
                      -- trace ("Normalize: ProofFromBool True: prefer Sym eg ^^\"failed cos...\" m=" ++ Eval.dumpExpr msg) $
                      loop (App Proof msg)
                    App (App ProofFromBool msg) (BoolLit False) ->
                      -- trace ("Normalize: ProofFromBool False: prefer Sym eg ^^\"failed cos...\" m=" ++ Eval.dumpExpr msg) $
                      loop (App PVoid msg)

                    z@(App PVoidUndefined _) ->
                      pure z

                    z@(App (App PVoidError _) _) ->
                      pure z

                    z@(App PVoidKindUndefined _) ->
                      pure z

                    App TextShow (TextLit (Chunks [] oldText)) ->
                        loop (TextLit (Chunks [] newText))
                      where
                        newText = Eval.textShow oldText

                    App TextToLower (TextLit (Chunks [] oldText)) ->
                        loop (TextLit (Chunks [] newText))
                      where
                        newText = Data.Text.toLower oldText

                    App TextToUpper (TextLit (Chunks [] oldText)) ->
                        loop (TextLit (Chunks [] newText))
                      where
                        newText = Data.Text.toUpper oldText

                    App TextUnpack (TextLit (Chunks [] oldText)) ->
                        loop o
                      where
                        o = case map (NaturalLit . fromIntegral . Data.Char.ord) (Data.Text.unpack oldText) of
                              [] -> ListLit (Just Natural) mempty
                              xs -> ListLit Nothing (Data.Sequence.fromList xs)

                    -- cant normalize further as List has to be NaturalLit which we cant guarantee
                    -- App TextPack (ListLit _ xs)

                    App TextToList (TextLit (Chunks [] xs)) ->
                        loop o
                      where
                        o = case Data.Text.chunksOf 1 xs of
                              [] -> ListLit (Just Text) mempty
                              as -> ListLit Nothing (Data.Sequence.fromList (map (TextLit . Chunks []) as))

                    App TextLength (TextLit (Chunks [] xs)) ->
                        loop (NaturalLit (fromIntegral (Data.Text.length xs)))

                    App (App (App TextCompare (BoolLit ci)) (TextLit (Chunks [] xs))) (TextLit (Chunks [] ys)) ->
                        loop (NaturalLit (fromIntegral (fromEnum (Data.Ord.comparing (if ci then Data.Text.toLower else id) xs ys))))

                    _ -> do
                        res2 <- ctx (App f' a')
                        case res2 of
                            Nothing -> pure (App f' a')
                            Just app' -> loop app'
    Let (Binding _ f _ _ _ r) b -> loop b''
      where
        r'  = shift   1  (V f 0) r
        b'  = subst (V f 0) r' b
        b'' = shift (-1) (V f 0) b'
    Annot x _ -> loop x
    Bool -> pure Bool
    BoolLit b -> pure (BoolLit b)
    BoolAnd x y -> decide <$> loop x <*> loop y
      where
        decide (BoolLit True )  r              = r
        decide (BoolLit False)  _              = BoolLit False
        decide  l              (BoolLit True ) = l
        decide  _              (BoolLit False) = BoolLit False
        decide  l               r
            | Eval.judgmentallyEqual l r = l
            | otherwise                  = BoolAnd l r
    BoolOr x y -> decide <$> loop x <*> loop y
      where
        decide (BoolLit False)  r              = r
        decide (BoolLit True )  _              = BoolLit True
        decide  l              (BoolLit False) = l
        decide  _              (BoolLit True ) = BoolLit True
        decide  l               r
            | Eval.judgmentallyEqual l r = l
            | otherwise                  = BoolOr l r
    BoolEQ x y -> decide <$> loop x <*> loop y
      where
        decide (BoolLit True )  r              = r
        decide  l              (BoolLit True ) = l
        decide  l               r
            | Eval.judgmentallyEqual l r = BoolLit True
            | otherwise                  = BoolEQ l r
    BoolNE x y -> decide <$> loop x <*> loop y
      where
        decide (BoolLit False)  r              = r
        decide  l              (BoolLit False) = l
        decide  l               r
            | Eval.judgmentallyEqual l r = BoolLit False
            | otherwise                  = BoolNE l r
    BoolIf bool true false -> decide <$> loop bool <*> loop true <*> loop false
      where
        decide (BoolLit True )  l              _              = l
        decide (BoolLit False)  _              r              = r
        decide  b              (BoolLit True) (BoolLit False) = b
        decide  b               l              r
            | Eval.judgmentallyEqual l r = l
            | otherwise                  = BoolIf b l r

    NonZero -> pure NonZero
    NonZeroLit n -> pure (NonZeroLit n)
    NonZeroShow -> pure NonZeroShow
    NonZeroClamp -> pure NonZeroClamp
    NonZeroDiv -> pure NonZeroDiv
    NonZeroMod -> pure NonZeroMod
    NonZeroLog -> pure NonZeroLog
    NonZeroAdd -> pure NonZeroAdd
    NonZeroMultiply -> pure NonZeroMultiply
    NonZeroToNatural -> pure NonZeroToNatural
    NonZeroToInteger -> pure NonZeroToInteger
    NonZeroParse -> pure NonZeroParse

    DateTime -> pure DateTime
    DateTimeLit n -> pure (DateTimeLit n)
    DateTimeShow -> pure DateTimeShow
    DateTimeParse -> pure DateTimeParse
    DateTimeFromSeconds -> pure DateTimeFromSeconds
    DateTimeToSeconds -> pure DateTimeToSeconds

    DateTimeAddYears -> pure DateTimeAddYears
    DateTimeAddMonths -> pure DateTimeAddMonths
    DateTimeAddDays -> pure DateTimeAddDays
    DateTimeFromWeek -> pure DateTimeFromWeek
    DateTimeToWeek -> pure DateTimeToWeek
    DateTimeToDate -> pure DateTimeToDate
    DateTimeFromDate -> pure DateTimeFromDate
    DateTimeLastDayOfMonth -> pure DateTimeLastDayOfMonth

    DateTimeGetJulianDay -> pure DateTimeGetJulianDay
    DateTimeSetJulianDay -> pure DateTimeSetJulianDay

    Regex -> pure Regex
    RegexLit n -> pure (RegexLit n)
    RegexShow -> pure RegexShow
    RegexMatch -> pure RegexMatch
    RegexScan -> pure RegexScan
    RegexSplit -> pure RegexSplit
    RegexReplace -> pure RegexReplace
    RegexReplix -> pure RegexReplix
    RegexParse -> pure RegexParse
    RegexToText -> pure RegexToText

    Rational -> pure Rational
    RationalLit n -> pure (RationalLit n)
    RationalShow -> pure RationalShow
    RationalFromDouble -> pure RationalFromDouble
    RationalToDouble -> pure RationalToDouble
    RationalFromRational -> pure RationalFromRational
    RationalPercent x y -> decide <$> loop x <*> loop y
      where
        decide (IntegerLit 0) (NonZeroLit _)              = RationalLit (0 % 1)
        decide (IntegerLit m)   (NonZeroLit (NonZeroC n)) = RationalLit (m % fromIntegral n)
        decide l                r                         = RationalPercent l r
    RationalParse -> pure RationalParse

    Natural -> pure Natural
    NaturalLit n -> pure (NaturalLit n)
    NaturalFold -> pure NaturalFold
    NaturalBuild -> pure NaturalBuild
    NaturalIsZero -> pure NaturalIsZero
    NaturalEven -> pure NaturalEven
    NaturalOdd -> pure NaturalOdd
    NaturalToInteger -> pure NaturalToInteger
    NaturalShow -> pure NaturalShow
    NaturalParse -> pure NaturalParse
    NaturalToBits -> pure NaturalToBits
    NaturalSubtract -> pure NaturalSubtract
    NaturalGcd -> pure NaturalGcd
    NaturalPlus x y -> decide <$> loop x <*> loop y
      where
        decide (NaturalLit 0)  r             = r
        decide  l             (NaturalLit 0) = l
        decide (NaturalLit m) (NaturalLit n) = NaturalLit (m + n)
        decide  l              r             = NaturalPlus l r
    NaturalTimes x y -> decide <$> loop x <*> loop y
      where
        decide (NaturalLit 1)  r             = r
        decide  l             (NaturalLit 1) = l
        decide (NaturalLit 0)  _             = NaturalLit 0
        decide  _             (NaturalLit 0) = NaturalLit 0
        decide (NaturalLit m) (NaturalLit n) = NaturalLit (m * n)
        decide  l              r             = NaturalTimes l r
    Integer -> pure Integer
    IntegerLit n -> pure (IntegerLit n)
    IntegerAdd -> pure IntegerAdd
    IntegerMultiply -> pure IntegerMultiply
    IntegerAnd -> pure IntegerAnd
    IntegerXor -> pure IntegerXor
    IntegerClamp -> pure IntegerClamp
    IntegerNegate -> pure IntegerNegate
    IntegerShow -> pure IntegerShow
    IntegerParse -> pure IntegerParse
    IntegerToDouble -> pure IntegerToDouble
    Double -> pure Double
    DoubleLit n -> pure (DoubleLit n)
    DoubleShow -> pure DoubleShow
    DoubleParse -> pure DoubleParse
    Text -> pure Text
    TextLit (Chunks xys z) -> do
        chunks' <- mconcat <$> chunks
        case chunks' of
            Chunks [("", x)] "" -> pure x
            c                   -> pure (TextLit c)
      where
        chunks =
          ((++ [Chunks [] z]) . concat) <$> traverse process xys

        process (x, y) = do
          y' <- loop y
          case y' of
            TextLit c -> pure [Chunks [] x, c]
            _         -> pure [Chunks [(x, y')] mempty]
    TextAppend x y -> loop (TextLit (Chunks [("", x), ("", y)] ""))
    TextShow -> pure TextShow
    TextToLower -> pure TextToLower
    TextToUpper -> pure TextToUpper
    TextUnpack -> pure TextUnpack
    TextPack -> pure TextPack
    TextToList -> pure TextToList
    TextLength -> pure TextLength
    TextCompare -> pure TextCompare
    List -> pure List
    ListLit t es
        | Data.Sequence.null es -> ListLit <$> t' <*> pure Data.Sequence.empty
        | otherwise             -> ListLit Nothing <$> es'
      where
        t'  = traverse loop t
        es' = traverse loop es
    ListAppend x y -> decide <$> loop x <*> loop y
      where
        decide (ListLit _ m)  r            | Data.Sequence.null m = r
        decide  l            (ListLit _ n) | Data.Sequence.null n = l
        decide (ListLit t m) (ListLit _ n)                        = ListLit t (m <> n)
        decide  l             r                                   = ListAppend l r
    ListBuild -> pure ListBuild
    ListFold -> pure ListFold
    ListLength -> pure ListLength
    ListHead -> pure ListHead
    ListLast -> pure ListLast
    ListIndexed -> pure ListIndexed
    ListReverse -> pure ListReverse
    ListPermutations -> pure ListPermutations
    ListChoose -> pure ListChoose
    ListFixed -> pure ListFixed
    ListFixedLit x y -> ListFixedLit <$> x' <*> y'
      where
        x' = loop x
        y' = traverse loop y
    ListFixedFromList -> pure ListFixedFromList
    ListFixedToList -> pure ListFixedToList
    ListFixedHead -> pure ListFixedHead
    ListFixedTail -> pure ListFixedTail

    Sym t -> pure (Sym t)
    SymLit t -> pure (SymLit t)
    SymFromText -> pure SymFromText
    SymToText -> pure SymToText

    SZ -> pure SZ
    SS -> pure SS

    SZLit -> pure SZLit
    SSLit x -> SSLit <$> x'
      where
        x' = loop x

    SSFromNonZero -> pure SSFromNonZero
    SSToNonZero -> pure SSToNonZero
    SSToNatural -> pure SSToNatural
    SSAdd -> pure SSAdd
    SSSubtract -> pure SSSubtract
    SSEqual -> pure SSEqual
    SSLessThan -> pure SSLessThan

    Proof -> pure Proof
    ProofLit -> pure ProofLit
    ProofToBool -> pure ProofToBool
    ProofFromBool -> pure ProofFromBool

    PVoid -> pure PVoid
    PVoidUndefined -> pure PVoidUndefined
    PVoidError -> pure PVoidError
    PVoidKindUndefined -> pure PVoidKindUndefined

    Optional -> pure Optional
    Some a -> Some <$> a'
      where
        a' = loop a
    None -> pure None
    Record kts -> Record . Dhall.Map.sort <$> kts'
      where
        f (RecordField s0 expr) = RecordField s0 <$> loop expr
        kts' = traverse f kts
    RecordLit kvs -> RecordLit . Dhall.Map.sort <$> kvs'
      where
        f (RecordField s0 expr) = RecordField s0 <$> loop expr
        kvs' = traverse f kvs
    Union kts -> Union . Dhall.Map.sort <$> kts'
      where
        kts' = traverse (traverse loop) kts
    Combine mk x y -> decide <$> loop x <*> loop y
      where
        decide (RecordLit m) r | Data.Foldable.null m =
            r
        decide l (RecordLit n) | Data.Foldable.null n =
            l
        decide (RecordLit m) (RecordLit n) =
            RecordLit (Dhall.Map.unionWith f m n)
          where
            f (RecordField _ expr) (RecordField _ expr') =
              Syntax.makeRecordField $ decide expr expr'
        decide l r =
            Combine mk l r
    CombineTypes x y -> decide <$> loop x <*> loop y
      where
        decide (Record m) r | Data.Foldable.null m =
            r
        decide l (Record n) | Data.Foldable.null n =
            l
        decide (Record m) (Record n) =
            Record (Dhall.Map.unionWith f m n)
          where
            f (RecordField _ expr) (RecordField _ expr') =
              Syntax.makeRecordField $ decide expr expr'
        decide l r =
            CombineTypes l r
    Prefer _ x y -> decide <$> loop x <*> loop y
      where
        decide (RecordLit m) r | Data.Foldable.null m =
            r
        decide l (RecordLit n) | Data.Foldable.null n =
            l
        decide (RecordLit m) (RecordLit n) =
            RecordLit (Dhall.Map.union n m)
        decide l r | Eval.judgmentallyEqual l r =
            l
        decide l r =
            Prefer PreferFromSource l r
    RecordCompletion x y ->
        loop (Annot (Prefer PreferFromCompletion (Field x "default") y) (Field x "Type"))
    Merge x y t      -> do
        x' <- loop x
        y' <- loop y
        case x' of
            RecordLit kvsX ->
                case y' of
                    Field (Union ktsY) kY ->
                        case Dhall.Map.lookup kY ktsY of
                            Just Nothing ->
                                case recordFieldValue <$> Dhall.Map.lookup kY kvsX of
                                    Just vX -> return vX
                                    Nothing -> Merge x' y' <$> t'
                            _ ->
                                Merge x' y' <$> t'
                    App (Field (Union ktsY) kY) vY ->
                        case Dhall.Map.lookup kY ktsY of
                            Just (Just _) ->
                                case recordFieldValue <$> Dhall.Map.lookup kY kvsX of
                                    Just vX -> loop (App vX vY)
                                    Nothing -> Merge x' y' <$> t'
                            _ ->
                                Merge x' y' <$> t'
                    Some a ->
                        case recordFieldValue <$> Dhall.Map.lookup "Some" kvsX of
                            Just vX -> loop (App vX a)
                            Nothing -> Merge x' y' <$> t'
                    App None _ ->
                        case recordFieldValue <$> Dhall.Map.lookup "None" kvsX of
                            Just vX -> return vX
                            Nothing -> Merge x' y' <$> t'
                    _ -> Merge x' y' <$> t'
            _ -> Merge x' y' <$> t'
      where
        t' = traverse loop t
    ToMap x t        -> do
        x' <- loop x
        t' <- traverse loop t
        case x' of
            RecordLit kvsX -> do
                let entry (key, value) =
                        RecordLit
                            (Dhall.Map.fromList
                                [ ("mapKey"  , Syntax.makeRecordField $ TextLit (Chunks [] key))
                                , ("mapValue", Syntax.makeRecordField value                  )
                                ]
                            )

                let keyValues = Data.Sequence.fromList (map entry (Dhall.Map.toList $ recordFieldValue <$> kvsX))

                let listType = case t' of
                        Just _ | null keyValues ->
                            t'
                        _ ->
                            Nothing

                return (ListLit listType keyValues)
            _ ->
                return (ToMap x' t')
    Field r x        -> do
        let singletonRecordLit v = RecordLit (Dhall.Map.singleton x v)

        r' <- loop r
        case r' of
            RecordLit kvs ->
                case Dhall.Map.lookup x kvs of
                    Just v  -> pure $ recordFieldValue v
                    Nothing -> Field <$> (RecordLit <$> traverse (Syntax.recordFieldExprs loop) kvs) <*> pure x
            Project r_ _ -> loop (Field r_ x)
            Prefer _ (RecordLit kvs) r_ -> case Dhall.Map.lookup x kvs of
                Just v -> pure (Field (Prefer PreferFromSource (singletonRecordLit v) r_) x)
                Nothing -> loop (Field r_ x)
            Prefer _ l (RecordLit kvs) -> case Dhall.Map.lookup x kvs of
                Just v -> pure $ recordFieldValue v
                Nothing -> loop (Field l x)
            Combine m (RecordLit kvs) r_ -> case Dhall.Map.lookup x kvs of
                Just v -> pure (Field (Combine m (singletonRecordLit v) r_) x)
                Nothing -> loop (Field r_ x)
            Combine m l (RecordLit kvs) -> case Dhall.Map.lookup x kvs of
                Just v -> pure (Field (Combine m l (singletonRecordLit v)) x)
                Nothing -> loop (Field l x)
            _ -> pure (Field r' x)
    Project x (Left fields)-> do
        x' <- loop x
        let fieldsSet = Dhall.Set.toSet fields
        case x' of
            RecordLit kvs ->
                pure (RecordLit (Dhall.Map.restrictKeys kvs fieldsSet))
            Project y _ ->
                loop (Project y (Left fields))
            Prefer _ l (RecordLit rKvs) -> do
                let rKs = Dhall.Map.keysSet rKvs
                let l' = Project l (Left (Dhall.Set.fromSet (Data.Set.difference fieldsSet rKs)))
                let r' = RecordLit (Dhall.Map.restrictKeys rKvs fieldsSet)
                loop (Prefer PreferFromSource l' r')
            _ | null fields -> pure (RecordLit mempty)
              | otherwise   -> pure (Project x' (Left (Dhall.Set.sort fields)))
    Project r (Right e1) -> do
        e2 <- loop e1

        case e2 of
            Record kts ->
                loop (Project r (Left (Dhall.Set.fromSet (Dhall.Map.keysSet kts))))
            _ -> do
                r' <- loop r
                pure (Project r' (Right e2))
    Assert t -> do
        t' <- loop t

        pure (Assert t')
    Equivalent l r -> do
        l' <- loop l
        r' <- loop r
        pure (Equivalent l' r')
    With e' k v ->
        loop (Syntax.desugarWith (With e' k v))
    Note _ e' -> loop e'
    ImportAlt l _r -> loop l
    Embed a -> pure (Embed a)

-- | Use this to wrap you embedded functions (see `normalizeWith`) to make them
--   polymorphic enough to be used.
type NormalizerM m a = forall s. Expr s a -> m (Maybe (Expr s a))

-- | An variation on `NormalizerM` for pure normalizers
type Normalizer a = NormalizerM Identity a

-- | A reified 'Normalizer', which can be stored in structures without
-- running into impredicative polymorphism.
newtype ReifiedNormalizer a = ReifiedNormalizer
  { getReifiedNormalizer :: Normalizer a }

-- | Check if an expression is in a normal form given a context of evaluation.
--   Unlike `isNormalized`, this will fully normalize and traverse through the expression.
--
--   It is much more efficient to use `isNormalized`.
--
--  `isNormalizedWith` can fail with an `error` if you check an ill-typed
--  expression
isNormalizedWith :: (Eq s, Eq a) => Normalizer a -> Expr s a -> Bool
isNormalizedWith ctx e = e == normalizeWith (Just (ReifiedNormalizer ctx)) e

-- | Quickly check if an expression is in normal form
--
-- Given a well-typed expression @e@, @'isNormalized' e@ is equivalent to
-- @e == 'normalize' e@.
--
-- Given an ill-typed expression, 'isNormalized' may fail with an error, or
-- evaluate to either False or True!
isNormalized :: Eq a => Expr s a -> Bool
isNormalized e0 = loop (Syntax.denote e0)
  where
    loop e = case e of
      Const _ -> True
      Var _ -> True
      Lam _ a b -> loop a && loop b
      Pi _ a b -> loop a && loop b
      App f a -> loop f && loop a && case App f a of
          App (Lam _ _ _) _ -> False

          App NonZeroShow (NonZeroLit _) -> False
          App NonZeroClamp (NaturalLit _) -> False

          App (App NonZeroDiv (IntegerLit _)) (NonZeroLit _) -> False

          App (App NonZeroMod (IntegerLit _)) (NonZeroLit _) -> False
          App (App NonZeroLog (NonZeroLit _)) (NonZeroLit _) -> False
          App (App NonZeroAdd (NonZeroLit _)) (NonZeroLit _) -> False
          App (App NonZeroMultiply (NonZeroLit _)) (NonZeroLit _) -> False

          App NonZeroToNatural (NonZeroLit _) -> False
          App NonZeroToInteger (NonZeroLit _) -> False
          App NonZeroParse (TextLit (Chunks [] _)) -> False

          App DateTimeShow (DateTimeLit _) -> False
          App DateTimeParse (TextLit (Chunks [] _)) -> False
          App DateTimeFromSeconds (IntegerLit _) -> False
          App DateTimeToSeconds (DateTimeLit _) -> False

          App (App DateTimeAddYears (IntegerLit _)) (DateTimeLit _) -> False
          App (App DateTimeAddMonths (IntegerLit _)) (DateTimeLit _) -> False
          App (App DateTimeAddDays (IntegerLit _)) (DateTimeLit _) -> False

          App (App (App DateTimeFromWeek (IntegerLit _)) (NonZeroLit _)) (NonZeroLit _) -> False
          App DateTimeToWeek (DateTimeLit _) -> False
          App (App (App (App (App (App DateTimeToDate (IntegerLit _)) (NonZeroLit _)) (NonZeroLit _)) (NaturalLit _)) (NaturalLit _)) (NaturalLit _) -> False
          App DateTimeFromDate (DateTimeLit _) -> False
          App (App DateTimeLastDayOfMonth (IntegerLit _)) (NonZeroLit _) -> False

          App DateTimeGetJulianDay (DateTimeLit _) -> False
          App (App DateTimeSetJulianDay (IntegerLit _)) (NaturalLit _) -> False

          App RegexShow (RegexLit _) -> False

          App (App RegexMatch (RegexLit _)) (TextLit (Chunks [] _)) -> False
          App (App (App RegexScan (RegexLit _)) (TextLit (Chunks [] _))) (NonZeroLit _) -> False
          App (App (App RegexSplit (RegexLit _)) (TextLit (Chunks [] _))) (NonZeroLit _) -> False
          App (App (App RegexReplace (RegexLit _)) (TextLit (Chunks [] _))) (TextLit (Chunks [] _)) -> False
          App (App (App RegexReplix (RegexLit _)) (TextLit (Chunks [] _))) (TextLit (Chunks [] _)) -> False

          App RegexParse (TextLit (Chunks [] _)) -> False
          App RegexToText (RegexLit _) -> False

          App RationalShow (RationalLit _) -> False
          App (App RationalFromDouble (DoubleLit _)) (DoubleLit _) -> False
          App RationalToDouble (RationalLit _) -> False
          App RationalFromRational (RationalLit _) -> False
          App RationalParse (TextLit (Chunks [] _)) -> False

          App (App (App (App NaturalFold (NaturalLit _)) _) _) _ -> False
          App NaturalBuild _ -> False
          App NaturalIsZero (NaturalLit _) -> False
          App NaturalEven (NaturalLit _) -> False
          App NaturalOdd (NaturalLit _) -> False
          App NaturalShow (NaturalLit _) -> False
          App NaturalParse (TextLit (Chunks [] _)) -> False
          App NaturalToBits (NaturalLit _) -> False

          App (App NaturalSubtract (NaturalLit _)) (NaturalLit _) -> False
          App (App NaturalSubtract (NaturalLit 0)) _ -> False
          App (App NaturalSubtract _) (NaturalLit 0) -> False
          App (App NaturalSubtract x) y -> not (Eval.judgmentallyEqual x y)

          App (App NaturalGcd (NaturalLit _)) (NaturalLit _) -> False

          App NaturalToInteger (NaturalLit _) -> False
          App IntegerNegate (IntegerLit _) -> False

          App (App IntegerAdd (IntegerLit _)) (IntegerLit _) -> False
          App (App IntegerMultiply (IntegerLit _)) (IntegerLit _) -> False

          App (App IntegerAnd (IntegerLit _)) (IntegerLit _) -> False
          App (App IntegerXor (IntegerLit _)) (IntegerLit _) -> False

          App IntegerClamp (IntegerLit _) -> False
          App IntegerShow (IntegerLit _) -> False
          App IntegerParse (TextLit (Chunks [] _)) -> False
          App IntegerToDouble (IntegerLit _) -> False
          App DoubleShow (DoubleLit _) -> False
          App DoubleParse (TextLit (Chunks [] _)) -> False
          App (App ListBuild _) _ -> False
          App (App (App (App (App (App ListFold _) (ListLit _ _)) _) _) _) _ -> False
          App (App ListLength _) (ListLit _ _) -> False
          App (App ListHead _) (ListLit _ _) -> False
          App (App ListLast _) (ListLit _ _) -> False
          App (App ListIndexed _) (ListLit _ _) -> False
          App (App ListReverse _) (ListLit _ _) -> False
          App (App ListPermutations _) (ListLit _ _) -> False
          App (App (App ListChoose _) (NaturalLit _)) (ListLit _ _) -> False
          App TextShow (TextLit (Chunks [] _)) -> False
          App TextToLower (TextLit (Chunks [] _)) -> False
          App TextToUpper (TextLit (Chunks [] _)) -> False
          App TextUnpack (TextLit (Chunks [] _)) -> False
          App TextPack (ListLit _ _) -> True
          App TextToList (TextLit (Chunks [] _)) -> False
          App TextLength (TextLit (Chunks [] _)) -> False
          App (App TextLength (TextLit (Chunks [] _))) (TextLit (Chunks [] _)) -> False
          App (App (App (App ListFixedFromList SZ) (NonZeroLit _)) _) (ListLit _ _) -> False
          App (App (App (App ListFixedFromList (App SS _)) (NonZeroLit _)) _) (ListLit _ _) -> False
          App (App (App ListFixedToList SZ) _) (ListFixedLit _ _) -> False
          App (App (App ListFixedToList (App SS _)) _) (ListFixedLit _ _) -> False
          App (App (App ListFixedHead SZ) _) (ListFixedLit _ _) -> False
          App (App (App ListFixedHead (App SS _)) _) (ListFixedLit _ _) -> False
          App (App (App ListFixedTail SZ) _) (ListFixedLit _ _) -> False
          App (App (App ListFixedTail SZ) _) (ListFixedLit _ _) -> False

          App SymFromText (TextLit (Chunks [] _)) -> False
          App SymToText (Sym _) -> False

          App SSFromNonZero (NonZeroLit _) -> False
          App SSToNonZero SZ -> False
          App SSToNonZero (App SS _) -> False
          App SSToNatural SZ -> False
          App SSToNatural (App SS _) -> False
          App (App SSAdd SZ) SZ -> False
          App (App SSAdd SZ) (App SS _) -> False
          App (App SSAdd (App SS _)) SZ -> False
          App (App SSAdd (App SS _)) (App SS _) -> False

          -- App (App SSSubtract SZ) SZ -> False
          App (App SSSubtract SZ) (App SS _) -> False
          --App (App SSSubtract (App SS _)) SZ -> False
          App (App SSSubtract (App SS x)) (App SS y) -> loop (App (App SSSubtract x) y)

          App (App SSEqual SZ) SZ -> False
          App (App SSEqual SZ) (App SS _) -> False
          App (App SSEqual (App SS _)) SZ -> False
          App (App SSLessThan (App SS _)) (App SS _) -> False
          App (App SSLessThan SZ) SZ -> False
          App (App SSLessThan SZ) (App SS _) -> False
          App (App SSLessThan (App SS _)) SZ -> False
          App (App SSLessThan (App SS _)) (App SS _) -> False
          App ProofToBool (App Proof _) -> False
          App ProofToBool (App Proof _) -> False
          App (App ProofFromBool _) (BoolLit _) -> False

          App PVoidUndefined _ -> True
          App (App PVoidError _) _ -> True
          App PVoidKindUndefined _ -> True
          _ -> True
      Let _ _ -> False
      Annot _ _ -> False
      Bool -> True
      BoolLit _ -> True
      BoolAnd x y -> loop x && loop y && decide x y
        where
          decide (BoolLit _)  _          = False
          decide  _          (BoolLit _) = False
          decide  l           r          = not (Eval.judgmentallyEqual l r)
      BoolOr x y -> loop x && loop y && decide x y
        where
          decide (BoolLit _)  _          = False
          decide  _          (BoolLit _) = False
          decide  l           r          = not (Eval.judgmentallyEqual l r)
      BoolEQ x y -> loop x && loop y && decide x y
        where
          decide (BoolLit True)  _             = False
          decide  _             (BoolLit True) = False
          decide  l              r             = not (Eval.judgmentallyEqual l r)
      BoolNE x y -> loop x && loop y && decide x y
        where
          decide (BoolLit False)  _               = False
          decide  _              (BoolLit False ) = False
          decide  l               r               = not (Eval.judgmentallyEqual l r)
      BoolIf x y z ->
          loop x && loop y && loop z && decide x y z
        where
          decide (BoolLit _)  _              _              = False
          decide  _          (BoolLit True) (BoolLit False) = False
          decide  _           l              r              = not (Eval.judgmentallyEqual l r)

      NonZero -> True
      NonZeroLit _ -> True
      NonZeroShow -> True
      NonZeroClamp -> True
      NonZeroDiv -> True
      NonZeroMod -> True
      NonZeroLog -> True
      NonZeroAdd -> True
      NonZeroMultiply -> True
      NonZeroToNatural -> True
      NonZeroToInteger -> True
      NonZeroParse -> True

      DateTime -> True
      DateTimeLit _ -> True
      DateTimeShow -> True
      DateTimeParse -> True
      DateTimeFromSeconds -> True
      DateTimeToSeconds -> True

      DateTimeAddYears -> True
      DateTimeAddMonths -> True
      DateTimeAddDays -> True
      DateTimeFromWeek -> True
      DateTimeToWeek -> True
      DateTimeToDate -> True
      DateTimeFromDate -> True
      DateTimeLastDayOfMonth -> True

      DateTimeGetJulianDay -> True
      DateTimeSetJulianDay -> True

      Regex -> True
      RegexLit _ -> True
      RegexShow -> True
      RegexMatch -> True
      RegexScan -> True
      RegexSplit -> True
      RegexReplace -> True
      RegexReplix -> True
      RegexParse -> True
      RegexToText -> True

      Rational -> True
      RationalLit _ -> True
      RationalShow -> True
      RationalFromDouble -> True
      RationalToDouble -> True
      RationalFromRational -> True
      RationalPercent x y -> loop x && loop y && decide x y
        where
          decide (IntegerLit 0) (NonZeroLit _) = False
          decide (IntegerLit _) (NonZeroLit _) = False
          decide  _             _              = True
      RationalParse -> True

      Natural -> True
      NaturalLit _ -> True
      NaturalFold -> True
      NaturalBuild -> True
      NaturalIsZero -> True
      NaturalEven -> True
      NaturalOdd -> True
      NaturalShow -> True
      NaturalParse -> True
      NaturalToBits -> True
      NaturalSubtract -> True
      NaturalGcd -> True
      ListPermutations -> True
      ListChoose -> True
      NaturalToInteger -> True
      NaturalPlus x y -> loop x && loop y && decide x y
        where
          decide (NaturalLit 0)  _             = False
          decide  _             (NaturalLit 0) = False
          decide (NaturalLit _) (NaturalLit _) = False
          decide  _              _             = True
      NaturalTimes x y -> loop x && loop y && decide x y
        where
          decide (NaturalLit 0)  _             = False
          decide  _             (NaturalLit 0) = False
          decide (NaturalLit 1)  _             = False
          decide  _             (NaturalLit 1) = False
          decide (NaturalLit _) (NaturalLit _) = False
          decide  _              _             = True
      Integer -> True
      IntegerLit _ -> True
      IntegerAdd -> True
      IntegerMultiply -> True
      IntegerAnd -> True
      IntegerXor -> True
      IntegerClamp -> True
      IntegerNegate -> True
      IntegerShow -> True
      IntegerParse -> True
      IntegerToDouble -> True
      Double -> True
      DoubleLit _ -> True
      DoubleShow -> True
      DoubleParse -> True
      Text -> True
      TextLit (Chunks [("", _)] "") -> False
      TextLit (Chunks xys _) -> all (all check) xys
        where
          check y = loop y && case y of
              TextLit _ -> False
              _         -> True
      TextAppend _ _ -> False
      TextShow -> True
      TextToLower -> True
      TextToUpper -> True
      TextUnpack -> True
      TextPack -> True
      TextToList -> True
      TextLength -> True
      TextCompare -> True
      List -> True
      ListLit t es -> all loop t && all loop es
      ListAppend x y -> loop x && loop y && decide x y
        where
          decide (ListLit _ m)  _            | Data.Sequence.null m = False
          decide  _            (ListLit _ n) | Data.Sequence.null n = False
          decide (ListLit _ _) (ListLit _ _)                        = False
          decide  _             _                                   = True
      ListBuild -> True
      ListFold -> True
      ListLength -> True
      ListHead -> True
      ListLast -> True
      ListIndexed -> True
      ListReverse -> True
      ListFixed -> True
      ListFixedLit a es -> loop a && all loop es
      ListFixedFromList -> True
      ListFixedToList -> True
      ListFixedHead -> True
      ListFixedTail -> True
      Sym _ -> True
      SymLit _ -> True
      SymFromText -> True
      SymToText -> True
      SZ -> True
      SS -> True
      SZLit -> True
      SSLit t -> loop t
      SSFromNonZero -> True
      SSToNonZero -> True
      SSToNatural -> True
      SSAdd -> True
      SSSubtract -> True
      SSEqual -> True
      SSLessThan -> True

      Proof -> True
      ProofLit -> True
      ProofToBool -> True
      ProofFromBool -> True

      PVoid -> True
      PVoidUndefined -> True
      PVoidError -> True
      PVoidKindUndefined -> True

      Optional -> True
      Some a -> loop a
      None -> True
      Record kts -> Dhall.Map.isSorted kts && all (loop . recordFieldValue) kts
      RecordLit kvs -> Dhall.Map.isSorted kvs && all (loop . recordFieldValue) kvs
      Union kts -> Dhall.Map.isSorted kts && all (all loop) kts
      Combine _ x y -> loop x && loop y && decide x y
        where
          decide (RecordLit m) _ | Data.Foldable.null m = False
          decide _ (RecordLit n) | Data.Foldable.null n = False
          decide (RecordLit _) (RecordLit _) = False
          decide  _ _ = True
      CombineTypes x y -> loop x && loop y && decide x y
        where
          decide (Record m) _ | Data.Foldable.null m = False
          decide _ (Record n) | Data.Foldable.null n = False
          decide (Record _) (Record _) = False
          decide  _ _ = True
      Prefer _ x y -> loop x && loop y && decide x y
        where
          decide (RecordLit m) _ | Data.Foldable.null m = False
          decide _ (RecordLit n) | Data.Foldable.null n = False
          decide (RecordLit _) (RecordLit _) = False
          decide l r = not (Eval.judgmentallyEqual l r)
      RecordCompletion _ _ -> False
      Merge x y t -> loop x && loop y && all loop t && case x of
          RecordLit _ -> case y of
              Field (Union _) _ -> False
              App (Field (Union _) _) _ -> False
              Some _ -> False
              App None _ -> False
              _ -> True
          _ -> True
      ToMap x t -> case x of
          RecordLit _ -> False
          _ -> loop x && all loop t
      Field r k -> case r of
          RecordLit _ -> False
          Project _ _ -> False
          Prefer _ (RecordLit m) _ -> Dhall.Map.keys m == [k] && loop r
          Prefer _ _ (RecordLit _) -> False
          Combine _ (RecordLit m) _ -> Dhall.Map.keys m == [k] && loop r
          Combine _ _ (RecordLit m) -> Dhall.Map.keys m == [k] && loop r
          _ -> loop r
      Project r p -> loop r &&
          case p of
              Left s -> case r of
                  RecordLit _ -> False
                  Project _ _ -> False
                  Prefer _ _ (RecordLit _) -> False
                  _ -> not (Dhall.Set.null s) && Dhall.Set.isSorted s
              Right e' -> case e' of
                  Record _ -> False
                  _ -> loop e'
      Assert t -> loop t
      Equivalent l r -> loop l && loop r
      With{} -> False
      Note _ e' -> loop e'
      ImportAlt _ _ -> False
      Embed _ -> True

{-| Detect if the given variable is free within the given expression

>>> "x" `freeIn` "x"
True
>>> "x" `freeIn` "y"
False
>>> "x" `freeIn` Lam "x" (Const Type) "x"
False
-}
freeIn :: Eq a => Var -> Expr s a -> Bool
variable@(V var i) `freeIn` expression =
    subst variable (Var (V var (i + 1))) strippedExpression
      /= strippedExpression
  where
    denote' :: Expr t b -> Expr () b
    denote' = Syntax.denote

    strippedExpression = denote' expression

{- $setup
>>> import Dhall.Syntax (Const(..))
-}
getSSCntExpr :: String -> Expr s a -> Either String NonZero
getSSCntExpr msg = fmap mkNonZeroUnsafe . loop
  where loop (App SS x) = fmap (+1) (loop x)
        loop SZ = Right 1
        loop o = Left $ "Normalize.hs getSSCntExpr [" ++ msg ++ "] expr=" ++ Eval.dumpExpr o

getBothSSCntExpr :: String -> Expr s a -> Expr s a -> (Integer, Integer)
getBothSSCntExpr msg m n =
  case (,) <$> getSSCntExpr "lhs" m <*> getSSCntExpr "rhs" n of
    Left e -> error $ "getBothSSCntExpr " ++ msg ++ " error " ++ e
    Right (NonZeroC x, NonZeroC y) -> (fromIntegral x,fromIntegral y)
