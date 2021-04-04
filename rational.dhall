let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let nz = ./nonzero.dhall
let oo = ./ordering.dhall
let sr = ./semiring.dhall

let num = \(r : Rational) -> (Rational/fromRational r).num : Integer
let den = \(r : Rational) -> (Rational/fromRational r).den : NonZero

let make = \(i : Integer) -> \(n : NonZero) -> i % n : Rational

let zero = +0 % !1 : Rational
let one = +1 % !1 : Rational

let isPositive = \(r : Rational) -> pp.Integer.positive (num r) : Bool
let isNegative = \(r : Rational) -> pp.Integer.negative (num r) : Bool
let isZero = \(r : Rational) -> pp.Integer.equal +0 (num r) : Bool

let negate = \(r : Rational) -> Integer/negate (num r) % den r : Rational
let abs = \(r : Rational) -> if isNegative r then negate r else r : Rational

let add =
    \(r1 : Rational)
 -> \(r2 : Rational)
 -> let x1 = Rational/fromRational r1
    let x2 = Rational/fromRational r2
    let a = Integer/multiply x1.num (NonZero/toInteger x2.den)
    let b = Integer/multiply x2.num (NonZero/toInteger x1.den)
    let d = Integer/add a b
    in d % NonZero/multiply x1.den x2.den
         : Rational

let minus = \(r1 : Rational) -> \(r2 : Rational) -> add r1 (negate r2) : Rational
let subtract = \(r1 : Rational) -> \(r2 : Rational) -> add (negate r1) r2 : Rational

let multiply =
    \(r1 : Rational)
 -> \(r2 : Rational)
 -> let x1 = Rational/fromRational r1
    let x2 = Rational/fromRational r2
    in Integer/multiply x1.num x2.num % NonZero/multiply x1.den x2.den
   : Rational

let divideNonZero =
     \(r : Rational)
  -> \(n : NonZero)
  -> num r % NonZero/multiply (den r) n
  : Rational

let fromInteger =
    \(i : Integer)
  -> i % !1
     : Rational

let fromNatural =
    \(n : Natural)
  -> Natural/toInteger n % !1
   : Rational

let compare = oo.compareRational

let lessThan =
     \(r1 : Rational)
  -> \(r2 : Rational)
  -> oo.isLT (compare r1 r2)
     : Bool

let lessThanEqual =
     \(r1 : Rational)
  -> \(r2 : Rational)
  -> oo.isLE (compare r1 r2)
     : Bool

let equal =
     \(r1 : Rational)
  -> \(r2 : Rational)
  -> oo.isEQ (compare r1 r2)
     : Bool

let greaterThanEqual =
     \(r1 : Rational)
  -> \(r2 : Rational)
  -> oo.isGE (compare r1 r2)
     : Bool

let greaterThan =
     \(r1 : Rational)
  -> \(r2 : Rational)
  -> oo.isGT (compare r1 r2)
     : Bool

let posUnits =
    \(e : Natural)
 -> \(m : Natural)
 -> \(n : Natural)
 -> let v = nz.pow !10 e
    in pp.Natural.toInteger (m * NonZero/toNatural v + n) % v
    : Rational

let addSubUnits =
    \(e : Natural)
 -> \(m : Rational)
 -> \(n : Rational)
 ->  let v = nz.pow !10 e
    in add n (divideNonZero m v)
   : Rational

let numInstance =
   { multiply
   , add
   , zero
   , one
   , fromNatural
   }
   : sr.Type Rational

let showDetail =
    \(n : Natural)
 -> \(m : Rational)
 -> let e = nz.pow !10 n
    let w = if isNegative m then negate m else m
    let a = Rational/fromRational (multiply w (NonZero/toInteger e % !1))
    let ww = Rational/fromRational w
    let b1 = NonZero/div ww.num ww.den
    let b2 = NonZero/mod (NonZero/div a.num a.den) e
    let x = add (b1 % !1) (b2 % e)
    let y = minus w x
    let b3 = Natural/show (pp.Integer.abs b2)
    let b4 = pp.Text.concat (pp.List.replicate (Natural/subtract (Text/length b3) n) Text "0")
    let s = if isNegative m then "-" else "+"
    let z = s ++ Natural/show (pp.Integer.abs b1) ++ "." ++ b4 ++ b3
    in { lhs = pp.Integer.abs b1
       , rhs = pp.Integer.abs b2
       , leftover = y
       , display = z
       , compareZero = compare m zero
       }

let showHaskell =
    \(r : Rational)
  -> let a = Natural/show (pp.Integer.abs (num r))
     in (if oo.isGE (compare r zero) then a
         else "(-" ++ a ++ ")"
        )
  ++ " % "
  ++ Natural/show (NonZero/toNatural (den r))

let enumerateN = sr.enumerateN Rational numInstance.add
let enumerate = sr.enumerate Rational numInstance

let min =
    \(m : Rational)
 -> \(n : Rational)
 -> if greaterThan m n then n else m
  : Rational

let max =
    \(m : Rational)
 -> \(n : Rational)
 -> if greaterThan m n then m else n
  : Rational

let test1 = assert : Rational/fromRational (Rational/fromDouble 3.131333 0.01) === { num = +25, den = !8 }
let test2 = assert : Rational/fromRational (Rational/fromDouble 3.131333 0.0001) === { num = +310, den = !99 }
let test3 = assert : Rational/fromRational (Rational/fromDouble -15.5 0.0) === { num = -31, den = !2 }
let test4 = assert : Rational/fromRational (Rational/fromDouble -15.5 -0.0) === { num = -31, den = !2 }
let test5 = assert : Rational/fromRational (Rational/fromDouble -15.5 +0.0) === { num = -31, den = !2 }
let test6 = assert : Rational/fromRational (Rational/fromDouble +15.5 0.0) === { num = +31, den = !2 }
let test7 = assert : Rational/fromRational (Rational/fromDouble +15.5 0.0) === { num = +31, den = !2 }
let test8 = assert : Rational/fromRational (Rational/fromDouble +15.5 +0.0) === { num = +31, den = !2 }
let test9 = assert : Rational/fromRational (Rational/fromDouble +15.5 -0.0) === { num = +31, den = !2 }
let test10 = assert : Rational/fromRational (+310 % !75) === { num = +62, den = !15 }

let test11 = assert : isZero zero === True
let test12 = assert : negate (+14 % !2) === (-7 % !1)
let test13 = assert : add (+13 % !3)
                         (-7 % !5)
                     === (+44 % !15)
let test14 = assert : equal (add (+13 % !3)
                                (-5 % !3))
                                (+8 % !3) === True
let test15 = assert : minus (+13 % !3)
                              (-7 % !5)
                          === (+86 % !15)

let test16 = assert : subtract (-7 % !5)
                              (+13 % !3)
                          === (+86 % !15)

let test17 = assert : lessThan zero zero === False

let test18 = assert : minus (-7 % !5)
                              (-7 % !5)
                          === (+0 % !1)


let test19 = assert : lessThan zero (+4 % !3) === True
let test20 = assert : lessThan zero (-4 % !3) === False

let test21 = assert : lessThan (+4 % !3) zero === False
let test22 = assert : lessThan (-4 % !3) zero === True

let test23 = assert : lessThan (-4 % !3) (-1 % !2) === True
let test24 = assert : lessThan (-1 % !2) (-4 % !3) === False
let test25 = assert : lessThan (-1 % !2) (-1 % !2) === False

let test26 = assert : lessThan (-4 % !3) (+1 % !2) === True
let test27 = assert : lessThan (-1 % !2) (+4 % !3) === True
let test28 = assert : lessThan (-1 % !2) (+1 % !2) === True

let test29 = assert : lessThan (+4 % !3) (-1 % !2) === False
let test30 = assert : lessThan (+1 % !2) (-4 % !3) === False
let test31 = assert : lessThan (+1 % !2) (-1 % !2) === False

let test32 = assert : lessThan (+4 % !3) (+1 % !2) === False
let test33 = assert : lessThan (+1 % !2) (+4 % !3) === True
let test34 = assert : lessThan (+1 % !2) (+1 % !2) === False

let test35 = assert : multiply (+3 % !2) (+7 % !5) === (+21 % !10)
let test36 = assert : multiply (-3 % !2) (+7 % !5) === (-21 % !10)
let test37 = assert : multiply (-3 % !2) (-7 % !5) === (+21 % !10)

let test38 = assert : multiply (-0 % !2) (-7 % !5) === (+0 % !1)
let test39 = assert : isZero (multiply zero (-7 % !5)) === True
let test40 = assert : isZero (multiply (-7 % !5) zero) === True

let test41 = assert : add (+3 % !2) (+7 % !5) === (+29 % !10)
let test42 = assert : add (-3 % !2) (+7 % !5) === (-1 % !10)
let test43 = assert : add (+3 % !2) (-7 % !5) === (+1 % !10)
let test44 = assert : add (-3 % !2) (-7 % !5) === (-29 % !10)
let test45 = assert : add (-3 % !17) (-9 % !17) === (-12 % !17)

let test46 = assert : add zero (-3 % !2) === (-3 % !2)
let test47 = assert : add zero (+3 % !2) === (+3 % !2)
let test48 = assert : add (+3 % !2) zero === (+3 % !2)
let test49 = assert : add (-3 % !2) zero === (-3 % !2)

let test50 = assert : (-12 % !8) === (-3 % !2)

let test51 = assert : greaterThan (fromInteger +12) (fromInteger +3) === True
let test52 = assert : greaterThan (fromInteger +12) (fromInteger +14) === False
let test53 = assert : greaterThan (fromInteger +12) (fromInteger -3) === True
let test54 = assert : greaterThan (fromInteger +12) (fromInteger -13) === True

let test55 = assert : greaterThan (fromInteger -12) (fromInteger +3) === False
let test56 = assert : greaterThan (fromInteger -12) (fromInteger +14) === False
let test57 = assert : greaterThan (fromInteger -12) (fromInteger -3) === False
let test58 = assert : greaterThan (fromInteger -12) (fromInteger -13) === True

let test59 = assert : divideNonZero (-14 % !1) !12 === (-7 % !6)
let test60 = assert : divideNonZero (-0 % !1) !12 === (+0 % !1)
let test61 = assert : divideNonZero (-0 % !7) !12 === (-0 % !1)
let test62 = assert : divideNonZero (+0 % !14) !12 === (+0 % !1)

let test63 = assert : compare (+4 % !3) (+8 % !6) === oo.EQ
let test64 = assert : compare (-7 % !3) (+4 % !5) === oo.LT
let test65 = assert : compare (-4 % !3) (-4 % !1) === oo.GT

let test66 = assert : Rational/fromDouble -1.4 0.01 === (-7 % !5)
let test67 = assert : Rational/toDouble (+0 % !14) === +0.0
let test68 = assert : Rational/toDouble (+0 % !14) === 0.0
let test69 = assert : Rational/toDouble (-3 % !2) === -1.5
let test70 = assert : Rational/toDouble (Rational/fromDouble -1.4 0.01) === -1.4

let test71 = assert : Rational/toDouble (-15 % !4) === -3.75
let test72 = assert : (-0 % !100) === (+0 % !4)
let test73 = assert : equal (-0 % !100) (+0 % !4) === True

let test74 = assert : Rational/parse "-14 % !4" === Some (-7 % !2)
let test75 = assert : Rational/parse "-14 % 4" === None Rational

let test76 = assert : greaterThan (+14 % !3) (-171 % !2) === True
let test77 = assert : greaterThan (+14 % !3) (+15 % !6) === True
let test78 = assert : greaterThan (+14 % !3) (+13 % !2) === False
let test79 = assert : greaterThan (+14 % !3) (+50 % !49) === True
let test80 = assert : greaterThan (-14 % !3) (-171 % !2) === True
let test81 = assert : greaterThan (-14 % !3) (+15 % !6) === False
let test82 = assert : greaterThan (-14 % !3) (-13 % !2) === True
let test83 = assert : greaterThan (-14 % !3) (-50 % !49) === False
let test84 = assert : greaterThan (-14 % !3) (-28 % !6) === False

let test85 = assert : lessThan (+14 % !3) (-171 % !2) === False
let test86 = assert : lessThan (+14 % !3) (+15 % !6) === False
let test87 = assert : lessThan (+14 % !3) (+13 % !2) === True
let test88 = assert : lessThan (+14 % !3) (+50 % !49) === False
let test89 = assert : lessThan (-14 % !3) (-171 % !2) === False
let test90 = assert : lessThan (-14 % !3) (+15 % !6) === True
let test91 = assert : lessThan (-14 % !3) (-13 % !2) === False
let test92 = assert : lessThan (-14 % !3) (-50 % !49) === True
let test93 = assert : lessThan (-14 % !3) (-28 % !6) === False

let test94 = assert : equal (+14 % !3) (-171 % !2) === False
let test95 = assert : equal (-14 % !3) (-28 % !6) === True
let test96 = assert : equal (-0 % !123) (+0 % !99) === True
let test97 = assert : num (-0 % !123) === -0
let test98 = assert : den (-0 % !123) === !1
let test99 = assert : num (-5 % !15) === -1
let test100 = assert : den (-5 % !15) === !3

let test101 = assert : showHaskell (+12 % !13) === "12 % 13"
let test102 = assert : showHaskell (-12 % !13) === "(-12) % 13"
let test103 = assert : showHaskell (+0 % !166) === "0 % 1"
let test104 = assert : showHaskell (-14 % !21) === "(-2) % 3"

-- display has -0.0 meaning the original is negative but lhs is zero
let test105 = assert : showDetail 0 (-14 % !21) === { display = "-0.0", leftover = +2 % !3, lhs = 0, rhs = 0, compareZero = oo.LT }
let test106 = assert : showDetail 0 (+14 % !21) === { display = "+0.0", leftover = +2 % !3, lhs = 0, rhs = 0, compareZero = oo.GT }


let test107 = assert : showDetail 5 (-100013 % !3) === { display = "-33337.66666", leftover = +1 % !150000, lhs = 33337, rhs = 66666, compareZero = oo.LT }
let test108 = assert : showDetail 2 (add (-12345 % !100) (-1 % !200)) === { display = "-123.45", leftover = +1 % !200, lhs = 123, rhs = 45, compareZero = oo.LT }

let test109 = assert : posUnits 2 13 1 === (+1301 % !100)

let test111 = assert : showDetail 10 (posUnits 10 12 14444) ===
  { compareZero = oo.GT
  , display = "+12.0000014444"
  , leftover = +0 % !1
  , lhs = 12
  , rhs = 14444
  }
let test112 = assert : showDetail 10 (negate (posUnits 10 12 14444)) ===
  { compareZero = oo.LT
  , display = "-12.0000014444"
  , leftover = +0 % !1
  , lhs = 12
  , rhs = 14444
  }
let test113 = assert : showDetail 10 (negate (posUnits 3 0 0)) ===
  { compareZero = oo.EQ
  , display = "+0.0000000000"
  , leftover = +0 % !1
  , lhs = 0
  , rhs = 0
  }

let test114 = assert : enumerateN 5 (-1 % !3) (+1 % !2) === [-1 % !3, +1 % !6, +2 % !3, +7 % !6, +5 % !3]
let test115 = assert : enumerateN 3 (-4 % !3) (-2 % !3) === [-4 % !3, -2 % !1, -8 % !3]

in {
num,
den,

zero,
one,
negate,
abs,
add,
subtract,
minus,
multiply,
divideNonZero,

fromInteger,
fromNatural,

isNegative,
isPositive,
isZero,

compare,
equal,

lessThanEqual,
lessThan,
greaterThanEqual,
greaterThan,

posUnits,
addSubUnits,

showDetail,
showHaskell,
numInstance,
make,
enumerate,
enumerateN,

min,
max
}

