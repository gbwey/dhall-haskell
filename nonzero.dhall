let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall
let nn = ./natural.dhall
let sr = ./semiring.dhall

let compare = oo.compareNonZero

let comparePeano =
    \(m : Type)
 -> \(n : Type)
 -> compare (SS/toNonZero m) (SS/toNonZero n)
 : oo.Ordering

let equal =
   \(m : NonZero)
-> \(n : NonZero)
-> pp.Natural.equal (NonZero/toNatural m) (NonZero/toNatural n)
-- -> oo.isEQ (compare m n)
   : Bool

let lessThanEqual =
   \(m : NonZero)
-> \(n : NonZero)
-> pp.Natural.lessThanEqual (NonZero/toNatural m) (NonZero/toNatural n)
   : Bool

let lessThan =
   \(m : NonZero)
-> \(n : NonZero)
-> pp.Natural.lessThan (NonZero/toNatural m) (NonZero/toNatural n)
   : Bool

let greaterThanEqual =
   \(m : NonZero)
-> \(n : NonZero)
-> pp.Natural.greaterThanEqual (NonZero/toNatural m) (NonZero/toNatural n)
   : Bool

let greaterThan =
   \(m : NonZero)
-> \(n : NonZero)
-> pp.Natural.greaterThan (NonZero/toNatural m) (NonZero/toNatural n)
   : Bool

let fromIntegerProof =
   \(i : Integer)
  -> \(prf : Proof/fromBool ^^"nonzero.dhall: fromIntegerProof found zero" (pp.Integer.equal i +0 == False))
  -> NonZero/clamp (Integer/clamp i)
  : NonZero

let subtractInternal =
    \(m : NonZero)
 -> \(n : NonZero)
 -> if lessThan m n then NonZero/clamp (Natural/subtract (NonZero/toNatural m) (NonZero/toNatural n))
    else PVoid/undefined NonZero
  : NonZero

let subtractProof =
    \(m : NonZero)
 -> \(n : NonZero)
 -> \(prf : Proof/fromBool ^^"nonzero.dhall: subtractProof m>=n" (lessThan m n))
 -> subtractInternal m n
  : NonZero

let clampProof =
    \(n : Natural)
 -> \(prf : Proof/fromBool ^^"nonzero.dhall: clampProof found 0" (Natural/isZero n == False))
 -> NonZero/clamp n

let divMod =
     \(n : Integer)
  -> \(d : NonZero)
  -> { _1 = NonZero/div n d, _2 = NonZero/mod n d }

-- empty list yields one! cos only possibility for nonzero
let sum =
     \(xs : List NonZero)
  -> merge
    { None = !1
    , Some = \(x : NonZero)
       -> List/fold
            NonZero
            (pp.List.drop 1 NonZero xs)
            NonZero
            NonZero/add
            x
    } (List/head NonZero xs)
  : NonZero

-- everything is off by one!
let numInstance =
   { multiply = NonZero/multiply
   , add = NonZero/add
   , zero = !1
   , one = !1
   , fromNatural = \(x : Natural) -> NonZero/clamp (x + 1)
   }
   : sr.Type NonZero

let subtractSSProof =
    \(m : Type)
 -> \(n : Type)
 -> \(prf : SS/lessThan m n)
 -> SS/subtract m n
  : Type

let enumerateN = sr.enumerateN NonZero numInstance.add
let enumerate = sr.enumerate NonZero numInstance

let pow =
    \(m : NonZero)
 -> \(n : Natural)
 -> let mm = NonZero/toNatural m
    in NonZero/clamp (Natural/fold n Natural (\(x : Natural) -> x * mm) 1)
   : NonZero

let lcm =
    \(n : NonZero)
 -> \(d : NonZero)
 -> NonZero/clamp (nn.lcm (NonZero/toNatural n) (NonZero/toNatural d))
  : NonZero

let gcd =
    \(n : NonZero)
 -> \(d : NonZero)
 -> NonZero/clamp (Natural/gcd (NonZero/toNatural n) (NonZero/toNatural d))
  : NonZero

-- cos NonZero/log adds one to the base to prevent logBase 1 1 which is NaN
{-
>logBase 1 1
NaN

>logBase 1 0
-Infinity
-}
let logProof =
    \(m : NonZero)
 -> \(n : NonZero)
 -> \(prf : Proof/fromBool ^^"logProof: expected base m greater than 1" (greaterThan m !1))
 -> NonZero/log (subtractInternal !1 m) n
   : Natural

let min =
    \(m : NonZero)
 -> \(n : NonZero)
 -> if greaterThan m n then n else m
  : NonZero

let max =
    \(m : NonZero)
 -> \(n : NonZero)
 -> if greaterThan m n then m else n
  : NonZero

let fac =
    \(n : NonZero)
 -> let t = { _1 : Natural, _2 : Natural }
    let ret =
      Natural/fold
         (NonZero/toNatural n)
         t
         (\(z : t) -> { _1 = z._1 + 1, _2 = z._1 * z._2 })
         { _1 = 1, _2 = 1 }
    in NonZero/clamp ret._2
         : NonZero

let ssMultiply =
    \(m : Type)
 -> \(n : Type)
 -> SS/fromNonZero (NonZero/multiply (SS/toNonZero m) (SS/toNonZero n))
   : Type

let test1 = assert : NonZero/mod +23 !5 === +3
let test2 = assert : NonZero/div +23 !5 === +4
let test3 = assert : NonZero/mod -23 !5 === +2
let test4 = assert : NonZero/div -23 !5 === -5
let test5 = assert : NonZero/mod -0 !5 === +0
let test6 = assert : NonZero/div -0 !5 === -0
let test7 = assert : NonZero/div -0 !5 === +0
let test8 = assert : NonZero/parse "!14" === Some !14
let test9 = assert : NonZero/parse "!0" === None NonZero
let test10 = assert : NonZero/parse "!1" === Some !1
let test11 = assert : NonZero/parse "99" === None NonZero
let test12 = assert : NonZero/parse "99" === None NonZero
let test13 = assert : NonZero/clamp 14 === !14
let test14 = assert : NonZero/clamp 0 === !1
let test15 = assert : NonZero/clamp 1 === !1
let test16 = assert : NonZero/parse "!12" === Some !12
let test17 = assert : NonZero/parse "!0" === None NonZero

let test18 = assert : NonZero/clamp 99 === !99
let test19 = assert : NonZero/clamp 0 === !1
let test20 = assert : NonZero/clamp 1 === !1

let test21 = assert : NonZero/show !99 === "!99"
let test22 = assert : NonZero/show !1 === "!1"

let test23 = assert : NonZero/toNatural !99 === 99
let test24 = assert : NonZero/toNatural !1 === 1

let test25 = assert : fromIntegerProof +10 Prf === !10
let test26 = assert : fromIntegerProof +1 Prf === !1
--let test27 = assert : fromIntegerProof +0 Prf === !1
let test27 = assert : fromIntegerProof -13 Prf === !1
let test28 = assert : NonZero/toInteger !1 === +1
let test29 = assert : NonZero/toInteger !10 === +10

let test30 = assert : equal !11 !1 === False
let test31 = assert : equal !3 !3 === True
let test32 = assert : NonZero/add !3 !7 === !10
let test33 = assert : NonZero/multiply !3 !7 === !21
let test34 = assert : NonZero/add !1 !1 === !2

let test35 = assert : fromIntegerProof +10 Prf === !10
let test36 = assert : fromIntegerProof +1 Prf === !1
--let test27 = assert : fromIntegerProof +0 Prf === !1 -- proof fails

let test37 = assert : subtractProof !4 !5 Prf === !1
--let test26 = assert : subtractProof !4 !4 Prf === !1
let test38 = assert : subtractInternal !3 !4 === !1
let test39 = assert : subtractInternal !4 !9 === !5
let test40 = assert : subtractProof !1 !3 Prf === !2
let test41 = assert : subtractProof !5 !20 Prf === !15

let test42 = assert : logProof !10 !1000 Prf === 3
let test43 = assert : logProof !10 !1001 Prf === 4
let test44 = assert : logProof !10 !999 Prf === 3
let test45 = assert : logProof !10 !1 Prf === 0

-- adds one to base since logBase 1 _ is undefined
let test46 = assert : NonZero/log !9 !1000 === 3
let test47 = assert : NonZero/log !9 !1001 === 4
let test48 = assert : NonZero/log !9 !999 === 3
let test49 = assert : NonZero/log !9 !1 === 0

let test50 = assert : logProof !2 !1 Prf === 0
let test51 = assert : logProof !2 !2 Prf === 1
let test52 = assert : logProof !2 !3 Prf === 2
let test53 = assert : logProof !2 !4 Prf === 2
let test54 = assert : logProof !2 !5 Prf === 3
let test55 = assert : logProof !2 !6 Prf === 3
let test56 = assert : logProof !2 !7 Prf === 3
let test57 = assert : logProof !2 !8 Prf === 3
let test58 = assert : logProof !2 !9 Prf === 4
let test59 = assert : logProof !15 !12345 Prf === NonZero/log !14 !12345

let test60 = assert : NonZero/log !1 !1 === 0
let test61 = assert : NonZero/log !1 !2 === 1
let test62 = assert : NonZero/log !1 !3 === 2
let test63 = assert : NonZero/log !1 !4 === 2
let test64 = assert : NonZero/log !1 !5 === 3
let test65 = assert : NonZero/log !1 !6 === 3
let test66 = assert : NonZero/log !1 !7 === 3
let test67 = assert : NonZero/log !1 !8 === 3
let test68 = assert : NonZero/log !1 !9 === 4

let test69 = assert : clampProof 4 Prf === !4
--let test46 = assert : clampProof 0 Prf === !1
let test70 = assert : subtractInternal !5 !6 === !1
let test71 = assert : subtractInternal !1 !6 === !5
--let test56 = assert : subtractInternal !6 !6 === !1
--let test56 = assert : PVoid/absurd NonZero (subtractInternal !7 !6) === PVoid

let test72 = assert : comparePeano !!1 !!1 === oo.EQ
let test73 = assert : comparePeano !!1 !!2 === oo.LT
let test74 = assert : comparePeano !!2 !!1 === oo.GT
let test75 = assert : comparePeano !!3 !!1 === oo.GT
let test76 = assert : comparePeano !!3 !!3 === oo.EQ
let test77 = assert : comparePeano !!5 !!4 === oo.GT
let test78 = assert : comparePeano !!4 !!4 === oo.EQ
let test79 = assert : comparePeano !!1 !!4 === oo.LT
let test80 = assert : subtractSSProof !!1 !!4 Prf === !!3
let test81 = assert : subtractSSProof !!3 !!4 Prf === !!1

let test82 = assert : sum ([] : List NonZero) === !1
let test83 = assert : sum [!1] === !1
let test84 = assert : sum [!5] === !5
let test85 = assert : sum [!5,!4,!11] === !20

let test86 = assert : enumerate 0 === ([] : List NonZero)
let test87 = assert : enumerate 7 === [ !1, !2, !3, !4, !5, !6, !7 ]
let test88 = assert : enumerateN 3 !14 !3 === [ !14, !17, !20 ]

let test89 = assert : pow !10 2 === !100
let test90 = assert : lcm !1 !1 === !1
let test91 = assert : lcm !17 !21 === !357
let test92 = assert : lcm !6 !9 === !18

let test93 = assert : fac !1 === !1
let test94 = assert : fac !4 === !24

let test95 = assert : gcd !1 !1 === !1
let test96 = assert : gcd !17 !21 === !1
let test97 = assert : gcd !6 !9 === !3

-- subtractSSProof !!4 !!4 Prf -- cant provide a proof for this of course

in {
, equal
, compare
, comparePeano
, lessThanEqual
, lessThan
, greaterThanEqual
, greaterThan
, divMod
, sum
, subtractProof
, subtractSSProof
, subtractInternal
, fromIntegerProof
, numInstance
, clampProof
, enumerate
, enumerateN
, logProof
, pow
, lcm
, gcd
, min
, max
, fac
, ssMultiply
}