let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall
let sr = ./semiring.dhall

let minus =
   \(m : Natural) -> \(n : Natural) -> Natural/subtract n m

let add =
    \(n : Natural)
 -> \(d : Natural)
 -> n + d
  : Natural

let multiply =
    \(n : Natural)
 -> \(d : Natural)
 -> n * d
  : Natural

let div =
    \(n : Natural)
 -> \(d : NonZero)
 -> pp.Integer.abs (NonZero/div (Natural/toInteger n) d)
 : Natural

let mod =
    \(n : Natural)
 -> \(d : NonZero)
 -> pp.Integer.abs (NonZero/mod (Natural/toInteger n) d)
 : Natural

let divMod =
    \(n : Natural)
 -> \(d : NonZero)
 -> { _1 = div n d, _2 = mod n d }

let lcm =
    \(n : Natural)
 -> \(d : Natural)
 -> div (n * d) (NonZero/clamp (Natural/gcd n d))
  : Natural

let compare = oo.compareNatural

let equal =
    \(d : Natural)
 -> \(e : Natural)
 -> oo.isEQ (compare d e)
  : Bool

let between =
    \(i : Natural)
 -> \(j : Natural)
 -> \(n : Natural)
 -> pp.Natural.greaterThanEqual n i && pp.Natural.lessThanEqual n j
 : Bool

let numInstance =
  { multiply
  , add
  , zero = 0
  , one = 1
  , fromNatural = \(x : Natural) -> x
  }
  : sr.Type Natural

let even =
    \(x : Natural)
 -> Natural/isZero (Integer/clamp (NonZero/mod (Natural/toInteger x) !2))
  : Bool

let odd =
   \(x : Natural)
 -> even x == False
   : Bool

let enumerateN = sr.enumerateN Natural numInstance.add

let enumerate = sr.enumerate Natural numInstance

let chooseFast =
    \(n : Natural)
 -> \(k : Natural)
 -> let k0 = if pp.Natural.greaterThan k (Natural/subtract k n)
             then Natural/subtract k n
             else k
    let t = { _1 : Natural, _2 : Natural }
    let ret =
      Natural/fold
        k0
        t
        (\(z : t) ->
           let r1 = z._2 * (Natural/subtract z._1 n)
           let r2 = div r1 (NonZero/clamp (z._1 + 1))
           in { _1 = z._1 + 1, _2 = r2 }
        )
        { _1 = 0, _2 = 1 }
     in ret._2
     : Natural

let chooseFastProof =
    \(n : Natural)
 -> \(k : Natural)
 -> \(prf : Proof/fromBool ^^"natural.dhall: chooseFastProof: k must be less than n"
      (pp.Natural.lessThan k n)
     )
 -> chooseFast n k
     : Natural

-- didnt end up needing gcd (was used for manually creating rational)
let test1 = assert : Natural/gcd 23 5 === 1
let test1 = assert : Natural/gcd 25 5 === 5
let test2 = assert : Natural/gcd 42 98 === 14
let test3 = assert : Natural/gcd 98 42 === 14
let test4 = assert : Natural/parse "14" === Some 14
let test5 = assert : Natural/parse "0" === Some 0
let test6 = assert : Natural/parse "1" === Some 1
let test7 = assert : Natural/parse "+99" === None Natural
let test8 = assert : Natural/parse "-1" === None Natural
let test9 = assert : Natural/parse "+0" === None Natural

let test10 = assert : 0xff === 255
let test11 = assert : 0b111 === 7
let test12 = assert : 0o71 === 57
let test13 = assert : Natural/parse "0b22" === None Natural
let test14 = assert : Natural/parse "0b11" === Some 3

let test16 = assert : even 0 === True
let test17 = assert : even 1 === False
let test18 = assert : even 213 === False
let test19 = assert : odd 213 === True
let test20 = assert : lcm 0 0 === 0
let test21 = assert : lcm 1 0 === 0
let test22 = assert : lcm 0 1 === 0
let test23 = assert : lcm 1 1 === 1
let test24 = assert : lcm 15 18 === 90
let test25 = assert : lcm 7 5 === 35

in {
, numInstance
, div
, mod
, divMod
, compare
, equal
, add
, multiply
, minus
, between
, even
, odd
, enumerate
, enumerateN
, lcm
, chooseFast
, chooseFastProof
}