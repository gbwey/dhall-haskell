-- Sym "ss" is the same type as Sym "tt"
-- so might as well just use a Text value
--let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let t = ./text.dhall
let r = ./rational.dhall

let MM = { val : Rational, unit : Text }
let Measure = \(r : Rational) -> \(s : Text) -> { val = r, unit = s }
let meters = \(r : Rational) -> Measure r "meter"
let seconds = \(r : Rational) -> Measure r "second"
let Mult =
     \(m : MM)
  -> \(n : MM)
  -> { val = r.multiply m.val n.val, unit = m.unit ++ "*" ++ n.unit }

let multiplyProof =
  \(m : MM)
  -> \(n : MM)
  -> \(prf : Proof/fromBool ^^"measureText.dhall: units are not the same" (t.equal m.unit n.unit))
  -> { val = r.multiply m.val n.val, unit = m.unit }

let m1 = meters (+15 % !4)
let s1 = seconds (-7 % !13)

let test1 = assert : multiplyProof (seconds (+15 % !4)) (seconds (-12 % !5)) Prf === { unit = "second", val = -9 % !1 }
let test2 = assert : Mult  (meters (+15 % !4)) (seconds (-12 % !5)) === { unit = "meter*second", val = -9 % !1 }
in {
Measure,
MM,
Mult,
meters,
seconds,
multiplyProof,
m1,
s1
}

{-
Measure/divide : VConst Type ~> VConst Type ~> VConst Type
Measure/multiply : VConst Type ~> VConst Type ~> VConst Type

Measure/divide { val : NonZero, unit : Text } (Measure/multiply "second" "second")

Unit : VNonZero ~> VText
need a type that is indexed by the value of the Text
need symbols at the type level but then we have no way to describe them in type check

could fake it with peano numbers

MSZ :: VText ~> VConst Type
MSS :: VConst Type ~> VConst Type

-- how do we safely divide inside eval [cant be a zero rational!] would have to do it via measure.dhall using Prf or just dont allow so it halts

Measure :: VRational ~> VConst Type ~> VConst Type

Measure/multiply :: VMeasure ~> VMeasure ~> VMeasure
Measure/divide :: VMeasure ~> VMeasure ~> VMeasure


-- how do we divide / multiply types
-- need more constructors to analyze stuff
-- easier to start with SS (ie wrap SZ so we start at 2)
-- SS SMult SDiv -- how do we simplify stuff eg m^2/m
-- let meter = SS (SZ "meter")  -- ie add a string as part of the type for tracing
-- let second = SS (SS (SZ "second"))
-- let second^2 = SMult second second
-- let hour = val * 3600 -- units are the same
-- have to stop users from wrapping with SS else will break everything

-- best way would be typelevel symbolic strings
-- but this will work

-- easier to deal with SS only and not SZ
MeasureLit VRational SS

Measure/new VRational VText VSS
MeasureLit VRational VText Measure

need (MSZ VText) (MSS (MSS/MSZ)) (MMult MSS MSS) (MDiv MSS MSS)




measure/mult { val : Rational, unit : SS } ss == MMult SS SS  -- and then only same units can be multiplied
measure/div ss == MDiv SS SS


Measure/divide : { val : VNonZero, unit : VSS } ~> { val : VNonZero, unit : VSS } ~> VConst Type
Measure/multiply : VConst Type ~> VConst Type ~> VConst Type
-}