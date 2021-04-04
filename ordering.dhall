let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let Ordering = < LT | EQ | GT >

let ordDef = { LT = False, EQ = False, GT = False }

let isEQ = \(z : Ordering) -> merge (ordDef // { EQ = True }) z : Bool
let isLT = \(z : Ordering) -> merge (ordDef // { LT = True }) z : Bool
let isGT = \(z : Ordering) -> merge (ordDef // { GT = True }) z : Bool
let isLE = \(z : Ordering) -> merge (ordDef // { EQ = True, LT = True }) z : Bool
let isGE = \(z : Ordering) -> merge (ordDef // { EQ = True, GT = True }) z : Bool
let isNE = \(z : Ordering) -> merge (ordDef // { LT = True, GT = True }) z : Bool

let on =
    \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b)
 -> \(g : b -> b -> c)
 -> \(x : a)
 -> \(y : a)
 -> g (f x) (f y)
 : c

let mempty = Ordering.EQ
   : Ordering

let mappend =
    \(a : Ordering)
 -> \(b : Ordering)
 -> merge { LT = a, GT = a, EQ = b } a
   : Ordering

let compareOrdering = mappend : Ordering -> Ordering -> Ordering

let compareNatural =
    \(m : Natural)
 -> \(n : Natural)
 -> if pp.Natural.lessThan m n then Ordering.LT
    else if pp.Natural.equal m n then Ordering.EQ
    else Ordering.GT
    : Ordering

let compareInteger =
    \(m : Integer)
 -> \(n : Integer)
 -> if pp.Integer.lessThan m n then Ordering.LT
    else if pp.Integer.equal m n then Ordering.EQ
    else Ordering.GT
    : Ordering

let compareBool =
    \(m : Bool)
 -> \(n : Bool)
 -> if m == False && n then Ordering.LT
    else if m == n then Ordering.EQ
    else Ordering.GT
    : Ordering

let compareNonZero =
    \(m : NonZero)
 -> \(n : NonZero)
 -> compareNatural (NonZero/toNatural m) (NonZero/toNatural n)
    : Ordering

let compareDateTime =
    \(dt1 : DateTime)
 -> \(dt2 : DateTime)
 -> compareInteger (DateTime/toSeconds dt1) (DateTime/toSeconds dt2)
  : Ordering

let compareRational =
     \(r1 : Rational)
  -> \(r2 : Rational)
  -> let x1 = Rational/fromRational r1
     let x2 = Rational/fromRational r2
     let a = Integer/multiply (x1.num) (NonZero/toInteger (x2.den))
     let b = Integer/multiply (x2.num) (NonZero/toInteger (x1.den))
     in compareInteger a b
       : Ordering

let compareTextImpl =
    \(ci : Bool)
 -> \(m : Text)
 -> \(n : Text)
 -> let x = Text/compare ci m n
    in if pp.Natural.equal x 0 then Ordering.LT
       else if pp.Natural.equal x 1 then Ordering.EQ
       else if pp.Natural.equal x 2 then Ordering.GT
       else PVoid/error ^^"unexpected ordering" Ordering
    : Ordering

let compareText = compareTextImpl False
let compareTextIgnore = compareTextImpl True

let foldMap =
    \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(mempty : b)
 -> \(mappend : b -> b -> b)
 -> \(xs : List a)
 -> List/fold
      a
      xs
      b
      (\(x : a) -> mappend (f x))
      mempty
    : b

--let fold : (a : Type) -> List a -> forall (z : a) -> (a -> a -> a) -> a =
--let fold : forall (a : Type) -> List a -> a -> (a -> a -> a) -> a =
let fold =
    \(a : Type)
 -> foldMap a a (\(x : a) -> x)
    : a -> (a -> a -> a) -> List a -> a

let mconcat =
   \(xs : List Ordering)
   -> fold Ordering mempty mappend xs
   : Ordering

let test1 = assert : fold Ordering mempty mappend [Ordering.EQ, Ordering.LT, Ordering.GT] === Ordering.LT
let test2 = assert : fold Ordering mempty mappend [Ordering.GT,Ordering.EQ,Ordering.LT] === Ordering.GT
let test3 = assert : fold Ordering mempty mappend [Ordering.EQ,Ordering.EQ] === Ordering.EQ
let test4 = assert : fold Ordering mempty mappend ([] : List Ordering) === Ordering.EQ
let test5 = assert : foldMap Natural Ordering (\(x : Natural) -> if Natural/even x then Ordering.LT else Ordering.EQ) mempty mappend [1,3,7] === Ordering.EQ
let test6 = assert : foldMap Natural Ordering (\(x : Natural) -> if Natural/even x then Ordering.LT else Ordering.GT) mempty mappend [2,5,2,3,10,7] === Ordering.LT
let test7 = assert : mconcat [Ordering.EQ,Ordering.EQ,Ordering.LT,Ordering.GT] === Ordering.LT
let test8 = assert : mconcat [Ordering.EQ,Ordering.EQ,Ordering.EQ] === Ordering.EQ
let test9 = assert : mconcat [Ordering.GT,Ordering.EQ,Ordering.EQ,Ordering.LT] === Ordering.GT

let test10 = assert : compareNatural 23 22 === Ordering.GT
let test10 = assert : compareNatural 23 24 === Ordering.LT
let test10 = assert : compareNatural 23 23 === Ordering.EQ

let test10 = assert : compareDateTime ^2020-12-22T12:13:14 ^2020-12-22T12:13:14 === Ordering.EQ
let test10 = assert : compareDateTime ^2020-12-22T12:13:15 ^2020-12-22T12:13:14 === Ordering.GT
let test10 = assert : compareDateTime ^2020-12-22T12:13:13 ^2020-12-22T12:13:14 === Ordering.LT

in
{
, Ordering
, ordDef
, LT = Ordering.LT
, EQ = Ordering.EQ
, GT = Ordering.GT
, isEQ
, isLT
, isGT
, isLE
, isGE
, isNE
, mempty
, mappend
, mconcat
, fold
, foldMap
, on
, compareOrdering
, compareBool
, compareDateTime
, compareInteger
, compareNatural
, compareNonZero
, compareRational
, compareText
, compareTextIgnore
}
