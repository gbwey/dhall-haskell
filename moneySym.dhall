-- dont use this!!! left as an explanation
-- no safety cos using Type ie ^^USD not ^"USD" so ^^USD is a value of Type and ^USD is a real type
-- totally unsafe: would need additional Proofs to be sfe
-- just use Text
-- no benefit at all
-- need Proofs everywhere
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let r = ./rational.dhall

let Value = { _1 : Rational, _2 : Type }

-- add a proof
let equal =
    \(v : Value)
 -> \(w : Value)
 -> r.equal v._1 w._1
 : Bool

let mkPos =
    \(c : Type)
 -> \(m : Natural)
 -> \(n : Natural)
 -> { _1 = r.posUnits 2 m n, _2 = c }
    : Value

let negate =
   \(v : Value)
 -> v // { _1 = r.negate v._1 }
    : Value

let mkNeg =
    \(c : Type)
 -> \(m : Natural)
 -> \(n : Natural)
 -> negate (mkPos c m n)
   : Value

let addCents =
    \(m : Rational)
 -> \(v : Value)
 -> v // { _1 = r.addSubUnits 2 m v._1 }
  : Value

let multiply =
    \(m : Rational)
 -> \(v : Value)
 -> v // { _1 = r.multiply m v._1 }
   : Value

let add =
    \(v : Value)
 -> \(w : Value)
 -> { _1 = r.add v._1 w._1, _2 = v._2 }
    : Value

let showN =
    \(n : Natural)
 -> \(v : Value)
 -> let a = r.showDetail n v._1
    let ey = if r.isZero a.leftover then "" else "*"
    in a.display ++ " " ++ Sym/toText v._2 ++ ey
    : Text

let show =
   showN 2
    : Value -> Text

let test1 = assert : mkPos ^^"GBP" 12 53 === { _1 = +1253 % !100, _2 = ^^"GBP" }
let test2 = assert : show (mkPos ^^"EUR" 11 20) === "+11.20 EUR"

let test3 = assert : mkNeg ^^"GBP" 12 253 === { _1 = -1453 % !100, _2 = ^^"GBP" }
let test4 = assert : show (mkNeg ^^"EUR" 11 120) === "-12.20 EUR"
let test5 = assert : show (mkNeg ^^"EUR" 11 7) === "-11.07 EUR"

let test6 = assert : addCents (+1 % !50) (mkPos ^^"EUR" 12 45) === { _1 = +62251 % !5000, _2 = ^^"EUR" }

let test7 = assert : show (addCents (+1 % !50) (mkPos ^^"EUR" 12 45)) === "+12.45 EUR*"

let test8 = assert : multiply (+5 % !1) (mkPos ^^"USD" 12 10) === { _1 = +121 % !2, _2 = ^^"USD" }
let test9 = assert : show (multiply (+5 % !1) (mkPos ^^"USD" 12 10)) === "+60.50 USD"

let test10 = assert : add (mkPos ^^"USD" 12 10) (mkNeg ^^"USD" 3 11) === { _1 = +899 % !100, _2 = ^^"USD" }
--let test11 = assert : add (mkPos ^^"USD" 12 10) (mkNeg ^^"USD" 3 11 ^^"AUD") Prf ...
let test12 = assert : show (add (mkNeg ^^"NZD" 12 10) (mkNeg ^^"NZD" 3 11)) === "-15.21 NZD"

-- let test13 = assert : show (add (mkNeg 12 10 ^^"NZD") (mkNeg 3 11 ^^"AUD") Prf) === "nodata"

let test14 = assert : show (addCents (+27 % !1) (mkPos ^^"GBP" 20 75)) === "+21.02 GBP"

-- original value is negative even though shows zero: cos there are extras!
let test15 = assert : show (addCents (-1 % !10) (mkPos ^^"GBP" 0 0)) === "-0.00 GBP*"
let test16 = assert : show (addCents (+1 % !10) (mkPos ^^"GBP" 0 0)) === "+0.00 GBP*"

let test17 = assert : show (mkPos ^^"GBP" 0 0) === "+0.00 GBP"
let test18 = assert : show (add (mkPos ^^"GBP" 12 50) (mkPos ^^"GBP" 7 49)) === "+19.99 GBP"
-- let test19 = assert : show (add (mkPos 12 50 ^^"AUD") (mkPos ^^"GBP" 7 49)) === "nodata"
let test20 = assert : show (add (mkNeg ^^"GBP" 12 50) (mkPos ^^"GBP" 7 49)) === "-5.01 GBP"

let test21 = assert : add (mkPos ^^"GBP" 25 30) (mkPos ^^"GBP" 25 30) === { _1 = +253 % !5, _2 = ^^"GBP" }


let test21 = assert : show (addCents (+1 % !200) (negate (mkPos ^^"GBP" 1 32)))
===
"-1.31 GBP*"

let test21 = assert : showN 5 (addCents (+1 % !200) (negate (mkPos ^^"GBP" 1 32)))
===
"-1.31995 GBP"

let test21 = assert : showN 10 (addCents (+1 % !200) (negate (mkPos ^^"GBP" 1 32)))
===
"-1.3199500000 GBP"

in {
, USD = ^^"USD"
, NZD = ^^"NZD"
, AUD = ^^"AUD"
, EUR = ^^"EUR"
, GBP = ^^"GBP"
, Value
, mkPos
, mkNeg
, negate
-- , showCurrency
-- , equal
-- , equalCurrency
, addCents
, multiply
, add
, showN
, show
}