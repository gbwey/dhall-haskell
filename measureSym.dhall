-- SymLit doesnt allow us to comine measures together but gives us type safety
-- Sym gives us no type safety so just use Text with a prf
-- the problem is we cant define a type signature that goes from Text -> SymLit t
-- nor can we define SymLit t -> Text
-- SymLit t is defined by 't'

-- could make SymLit (Val a) instead of SymLit Text
-- but how to distinguish Val a from other Val a
-- could add them both and have one kick in when the other is not available

-- no advantage from using plain Text: in fact more awkward
-- typelevel symbols work [best of both worlds]
-- if we use ^ then we can use the type system to guarantee correctness
--   ie cos will match the types: but we cant change the symbol at all

-- if we use ^^ then it is a Type so works everywhere but will need Prf if we want to ensure units match
-- with ^^ we can also change the symbols in any fashion
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall
let t = ./text.dhall
let r = ./rational.dhall

let MM = { val : Rational, unit : Type }
let meterT = ^^"meter"
let secondT = ^^"second"
let meter = ^"meter"
let second = ^"second"
let meters = \(r : Rational) -> { val = r, unit = meter }
let seconds = \(r : Rational) -> { val = r, unit = second }
let metersT = \(r : Rational) -> { val = r, unit = meterT }
let secondsT = \(r : Rational) -> { val = r, unit = secondT }

let meterSecond = ^"meter*second"
let meterSecondT = ^^"meter*second"

let m1 = meters (+15 % !4)
let m2 = meters (-3 % !7)
let s1 = seconds (-7 % !13)
let s2 = seconds (+1 % !2)

let mm1 = metersT (+15 % !4)
let mm2 = metersT (-3 % !7)
let ss1 = secondsT (-7 % !13)
let ss2 = secondsT (+1 % !2)

-- these are consistent but there are no checks that the types are the same
-- have to use a proof to make this work properly
-- expects same unit
let multiplyA =
    \(m : { val : Rational, unit : Type })
 -> \(n : { val : Rational, unit : Type })
 -> \(prf : Proof/fromBool ^^"multiplyA: currency must match" (t.equal (Sym/toText m.unit) (Sym/toText n.unit)))
 -> { val = r.multiply m.val n.val, unit = m.unit }
  : { val : Rational, unit : Type }

-- different units but changes the result unit -- gurk!
let multiplyB =
    \(m : { val : Rational, unit : Type })
 -> \(n : { val : Rational, unit : Type })
 -> let t = "(" ++ Sym/toText m.unit ++ ")*(" ++ Sym/toText n.unit ++ ")"
    in { val = r.multiply m.val n.val, unit = Sym/fromText t}
    : { val : Rational, unit : Type }
--    { val = r.multiply m.val n.val, unit = Sym/lower m.unit n.unit }

-- same as multiply except with divide symbol
let divideB =
    \(m : { val : Rational, unit : Type })
 -> \(n : { val : Rational, unit : Type })
 -> let t = "(" ++ Sym/toText m.unit ++ ")/(" ++ Sym/toText n.unit ++ ")"
    in { val = r.multiply m.val n.val, unit = Sym/fromText t}
    : { val : Rational, unit : Type }

-- typesafe multiply
let multiplySymLit =
    \(a : Type)
 -> \(m : { val : Rational, unit : a })
 -> \(n : { val : Rational, unit : a })
 -> { val = r.multiply m.val n.val, unit = m.unit }
  : { val : Rational, unit : a }

{-
-- unit is up a level to Type!!! gack! and we cant get back down
let multiply2OLD =
    \(a : Type)
 -> \(b : Type)
 -> \(m : { val : Rational, unit : a })
 -> \(n : { val : Rational, unit : b })
 -> { val = r.multiply m.val n.val, unit = Sym/lower a b }
    : { val : Rational, unit : Type }
-}
{-
     let t = Sym/toText a ++ "*" ++ Sym/toText b
     let s = Sym/fromText t
     in { val = r.multiply m.val n.val, unit = s } -- same as Sym/lower a b
-}

let f = \(a : Type) -> \(x : a) -> {=}
let test1 = assert : f ^^"asfd" ^"asfd" === {=}

let test2 = assert : Sym/toText ^^"abc" === "abc"
let test3 = assert : Sym/fromText "abc" === ^^"abc"
let test4 = assert : multiplySymLit meterT m1 m2 === { unit = meter, val = -45 % !28 }
{-
let test5 = assert : multiply2OLD meterT secondT m1 s1
===
{ unit = meterSecondT, val = -105 % !52 }
-}
let test6 = assert : multiplyB { val = +1 % !1, unit = ^^"abc" } { val = +1 % !1, unit = ^^"def" }
===
{ unit = ^^"(abc)*(def)", val = +1 % !1 }

let test7 = assert : multiplyA { val = +1 % !1, unit = ^^"abc" } { val = +1 % !1, unit = ^^"abc" } Prf
===
{ unit = ^^"abc", val = +1 % !1 }

in {
, meters
, seconds
, meter
, second
, meterT
, secondT
, meterSecond
, meterSecondT
, multiplySymLit
--, multiply2OLD
, multiplyA
, multiplyB
, divideB
, m1
, s1
, m2
, s2
, mm1
, ss1
, mm2
, ss2
}
{-
a.multiplySymLit a.meterT a.m1 a.m2
{ unit = SymLit ^"meter", val = -45 % !28 }

a.multiply2OLD a.meterT a.secondT a.m1 a.s1
{ unit = Sym ^^"meter*second", val = -105 % !52 }
-}


