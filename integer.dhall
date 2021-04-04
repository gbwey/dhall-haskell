let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall
let sr = ./semiring.dhall

let subtract =
   \(m : Integer) -> \(n : Integer) -> Integer/add (Integer/negate m) n

let minus =
   \(m : Integer) -> \(n : Integer) -> Integer/add m (Integer/negate n)

let compare = oo.compareInteger

let equal =
    \(d : Integer)
 -> \(e : Integer)
 -> oo.isEQ (compare d e)
  : Bool

let numInstance =
  { multiply = Integer/multiply
  , add = Integer/add
  , zero = +0
  , one = +1
  , fromNatural = Natural/toInteger
  }
  : sr.Type Integer

let enumerateN = sr.enumerateN Integer numInstance.add : Natural -> Integer -> Integer -> List Integer

let enumerate = sr.enumerate Integer numInstance : Natural -> List Integer

let min =
    \(m : Integer)
 -> \(n : Integer)
 -> if pp.Integer.greaterThan m n then m else n
  : Integer

let max =
    \(m : Integer)
 -> \(n : Integer)
 -> if pp.Integer.greaterThan m n then n else m
  : Integer


let test1 = assert : Integer/parse "-14" === Some -14
let test2 = assert : Integer/parse "+14" === Some +14
let test3 = assert : Integer/parse "-0" === Some +0
let test4 = assert : Integer/parse "-0" === Some -0
let test5 = assert : Integer/parse "+0" === Some +0
let test6 = assert : Integer/parse "+0" === Some -0
let test7 = assert : Integer/parse "99" === None Integer
let test8 = assert : Integer/parse "1" === None Integer
let test9 = assert : Integer/parse "0" === None Integer
let test10 = assert : Integer/parse "" === None Integer
let test11 = assert : Integer/parse " " === None Integer
let test12 = assert : Integer/parse "x" === None Integer

let test13 = assert : Integer/add +4 -7 === -3
let test14 = assert : Integer/multiply +4 -7 === -28
let test15 = assert : Integer/add +0 +7 === +7
let test16 = assert : Integer/add +0 -0 === +0
let test17 = assert : Integer/multiply +0 +7 === +0

let test18 = assert : minus +10 +7 === +3
let test19 = assert : minus -10 +7 === -17
let test20 = assert : subtract +7 +10 === +3
let test21 = assert : subtract +7 -10 === -17

let test22 = assert : enumerateN 5 -4 -3 === [-4,-7,-10,-13,-16]
let test23 = assert : enumerateN 5 -1 +0 === [-1,-1,-1,-1,-1]
let test24 = assert : enumerateN 0 -1 +0 === ([] : List Integer)

in {
subtract,
minus,
compare,
equal,
numInstance,
enumerateN,
enumerate,
min,
max
}