-- uses union for currency
-- see moneyText for Text only version
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let t = ./text.dhall
let r = ./rational.dhall

let Currency = < GBP | USD | EUR | NZD | AUD >
let Value = { _1 : Rational, _2 : Currency }

let showCurrency =
   \(c : Currency)
 -> merge {
   , GBP = "GBP"
   , USD = "USD"
   , EUR = "EUR"
   , NZD = "NZD"
   , AUD = "AUD"
   } c
   : Text

let equalCurrency =
    \(c : Currency)
 -> \(d : Currency)
 -> t.equal (showCurrency c) (showCurrency d)
   : Bool

let equal =
   \(v : Value)
 -> \(w : Value)
 -> r.equal v._1 w._1
 && equalCurrency v._2 v._2
 : Bool

let mkPos =
    \(m : Natural)
 -> \(n : Natural)
 -> \(c : Currency)
 -> { _1 = r.posUnits 2 m n, _2 = c }
    : Value

let negate =
    \(v : Value) -> v // { _1 = r.negate v._1 }
    : Value

let mkNeg =
    \(m : Natural)
 -> \(n : Natural)
 -> \(c : Currency)
 -> negate (mkPos m n c)
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

{-
let addOLD =
    \(v : Value)
 -> \(w : Value)
 -> \(prf : Proof/fromBool (equalCurrency v._2 w._2))
 -> if equalCurrency v._2 w._2
    then { _1 = r.add v._1 w._1, _2 = v._2 }
    else { _1 = +9999 % !1, _2 = v._2 }  -- impossible condition: we need a Void here
    : Value
-}

let add =
    \(v : Value)
 -> \(w : Value)
 -> \(prf : Proof/fromBool ^^"add: currency must match" (equalCurrency v._2 w._2))
 -> { _1 = r.add v._1 w._1, _2 = v._2 }
    : Value

let showN =
    \(n : Natural)
 -> \(v : Value)
 -> let a = r.showDetail n v._1
    let c = showCurrency v._2
    let ey = if r.isZero a.leftover then "" else "*"
    in a.display ++ " " ++ c ++ ey
    : Text

let show = showN 2 : Value -> Text

let test1 = assert : mkPos 12 53 Currency.GBP === { _1 = +1253 % !100, _2 = Currency.GBP }
let test2 = assert : show (mkPos 11 20 Currency.EUR) === "+11.20 EUR"

let test3 = assert : mkNeg 12 253 Currency.GBP === { _1 = -1453 % !100, _2 = Currency.GBP }
let test4 = assert : show (mkNeg 11 120 Currency.EUR) === "-12.20 EUR"
let test5 = assert : show (mkNeg 11 7 Currency.EUR) === "-11.07 EUR"

let test6 = assert : addCents (+1 % !50) (mkPos 12 45 Currency.EUR) === { _1 = +62251 % !5000, _2 = < AUD | EUR | GBP | NZD | USD >.EUR }

let test7 = assert : show (addCents (+1 % !50) (mkPos 12 45 Currency.EUR)) === "+12.45 EUR*"

let test8 = assert : multiply (+5 % !1) (mkPos 12 10 Currency.USD) === { _1 = +121 % !2, _2 = Currency.USD }
let test9 = assert : show (multiply (+5 % !1) (mkPos 12 10 Currency.USD)) === "+60.50 USD"

let test10 = assert : add (mkPos 12 10 Currency.USD) (mkNeg 3 11 Currency.USD) Prf === { _1 = +899 % !100, _2 = Currency.USD }
--let test11 = assert : add (mkPos 12 10 Currency.USD) (mkNeg 3 11 Currency.AUD) Prf ...
let test12 = assert : show (add (mkNeg 12 10 Currency.NZD) (mkNeg 3 11 Currency.NZD) Prf) === "-15.21 NZD"
-- let test13 = assert : show (add (mkNeg 12 10 Currency.NZD) (mkNeg 3 11 Currency.AUD) Prf) === "nodata"

let test14 = assert : show (addCents (+27 % !1) (mkPos 20 75 Currency.GBP)) === "+21.02 GBP"

-- original value is negative even though shows zero: cos there are extras!
let test15 = assert : show (addCents (-1 % !10) (mkPos 0 0 Currency.GBP)) === "-0.00 GBP*"
let test16 = assert : show (addCents (+1 % !10) (mkPos 0 0 Currency.GBP)) === "+0.00 GBP*"

let test17 = assert : show (mkPos 0 0 Currency.GBP) === "+0.00 GBP"
let test18 = assert : show (add (mkPos 12 50 Currency.GBP) (mkPos 7 49 Currency.GBP) Prf) === "+19.99 GBP"
-- let test19 = assert : show (add (mkPos 12 50 Currency.AUD) (mkPos 7 49 Currency.GBP) Prf) === "nodata"
let test20 = assert : show (add (mkNeg 12 50 Currency.GBP) (mkPos 7 49 Currency.GBP) Prf) === "-5.01 GBP"

let test21 = assert : add (mkPos 25 30 Currency.GBP) (mkPos 25 30 Currency.GBP) Prf === { _1 = +253 % !5, _2 = < AUD | EUR | GBP | NZD | USD >.GBP }


let test21 = assert : show (addCents (+1 % !200) (negate (mkPos 1 32 Currency.GBP)))
===
"-1.31 GBP*"

let test21 = assert : showN 5 (addCents (+1 % !200) (negate (mkPos 1 32 Currency.GBP)))
===
"-1.31995 GBP"

let test21 = assert : showN 10 (addCents (+1 % !200) (negate (mkPos 1 32 Currency.GBP)))
===
"-1.3199500000 GBP"

in {
, Currency
, USD = Currency.USD
, NZD = Currency.NZD
, AUD = Currency.AUD
, EUR = Currency.EUR
, GBP = Currency.GBP
, Value
, mkPos
, mkNeg
, negate
, showCurrency
, equal
, equalCurrency
, addCents
, multiply
, add
, showN
, show
}