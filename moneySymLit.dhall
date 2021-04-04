-- typesafe but harder to use
-- if we use SymLit we still have to pass in the type of the SymLit ie Sym t
-- SS is better defined cos we dont use SSLit !!

-- works but is serious crap: have to specify the type and the value!!! for mkpos mkneg
  --- mitigated by having preset usd/nzd which create stuff in that currency
-- also we have to always pass (c : Type) everywhere
-- more palatable with preset make for each currency and use subtract/minus instead of makeNeg or negate
{-
this is how you might use it realistically

:let a = ./moneySymLit.dhall
> a.minus a.USD (a.usd 10 15) (a.usd 20 1)
{ _1 = -493 % !50, _2 = ^"USD" }

> a.show a.USD (a.minus a.USD (a.usd 10 15) (a.usd 20 1))
"-9.86 USD"

> a.show a.USD (a.addCents a.USD (+51 % !100) (a.minus a.USD (a.usd 10 15) (a.usd 20 1)))
"-9.85 USD*"

> a.showN a.USD 5 (a.addCents a.USD (+51 % !100) (a.minus a.USD (a.usd 10 15) (a.usd 20 1)))
"-9.85490 USD"

> a.showN a.USD 5 (a.addCents a.USD (+51 % !1) (a.minus a.USD (a.usd 10 15) (a.usd 20 1)))
"-9.35000 USD"
-}
-- dont use negate just use minus
--let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let r = ./rational.dhall

let Value = \(c : Type) -> { _1 : Rational, _2 : c }

let make =
    \(c : Type)
 -> \(x : c)
 -> \(m : Natural)
 -> \(n : Natural)
 -> { _1 = r.posUnits 2 m n, _2 = x }
    : Value c

let USD = ^^"USD"
let NZD = ^^"NZD"
let AUD = ^^"AUD"
let EUR = ^^"EUR"
let GBP = ^^"GBP"

let usd = make ^^"USD" ^"USD"
let gbp = make ^^"GBP" ^"GBP"
let nzd = make ^^"NZD" ^"NZD"
let aud = make ^^"AUD" ^"AUD"
let eur = make ^^"EUR" ^"EUR"

let equal =
    \(c : Type)
 -> \(v : Value c)
 -> \(w : Value c)
 -> r.equal v._1 w._1
 : Bool

let negate =
    \(c : Type)
 -> \(v : Value c)
 -> v // { _1 = r.negate v._1 }
   : Value c

let makeNeg =
    \(c : Type)
 -> \(x : c)
 -> \(m : Natural)
 -> \(n : Natural)
 -> negate c (make c x m n)
  : Value c

let addCents =
    \(c : Type)
 -> \(m : Rational)
 -> \(v : Value c)
 -> v // { _1 = r.addSubUnits 2 m v._1 }
  : Value c

let multiply =
    \(c : Type)
 -> \(m : Rational)
 -> \(v : Value c)
 -> v // { _1 = r.multiply m v._1 }
 : Value c

let add =
    \(c : Type)
 -> \(v : Value c)
 -> \(w : Value c)
 -> { _1 = r.add v._1 w._1, _2 = v._2 }
 : Value c

let minus =
    \(c : Type)
 -> \(v : Value c)
 -> \(w : Value c)
 -> { _1 = r.minus v._1 w._1, _2 = v._2 }
 : Value c

let showN =
    \(c : Type)
 -> \(n : Natural)
 -> \(v : Value c)
 -> let a = r.showDetail n v._1
    let ey = if r.isZero a.leftover then "" else "*"
    in a.display ++ " " ++ Sym/toText c ++ ey
    : Text

let show =
    \(c : Type)
  -> showN c 2
    : Value c -> Text

let test1 = assert : make ^^"GBP" ^"GBP" 12 53 === { _1 = +1253 % !100, _2 = ^"GBP" }
let test2 = assert : show ^^"EUR" (make ^^"EUR" ^"EUR" 11 20) === "+11.20 EUR"

let test3 = assert : makeNeg ^^"GBP" ^"GBP" 12 253 === { _1 = -1453 % !100, _2 = ^"GBP" }
let test4 = assert : show ^^"EUR" (makeNeg ^^"EUR" ^"EUR" 11 120) === "-12.20 EUR"
let test5 = assert : show ^^"EUR" (makeNeg ^^"EUR" ^"EUR" 11 7) === "-11.07 EUR"

let test6 = assert : addCents ^^"EUR" (+1 % !50) (make ^^"EUR"  ^"EUR"  12 45) === { _1 = +62251 % !5000, _2 = ^"EUR" }

let test7 = assert : show ^^"EUR" (addCents ^^"EUR" (+1 % !50) (make ^^"EUR"  ^"EUR"  12 45)) === "+12.45 EUR*"

let test8 = assert : multiply ^^"USD" (+5 % !1) (make ^^"USD"  ^"USD"  12 10) === { _1 = +121 % !2, _2 = ^"USD" }
let test9 = assert : show ^^"USD" (multiply ^^"USD" (+5 % !1) (make ^^"USD"  ^"USD"  12 10)) === "+60.50 USD"

let test10 = assert : add ^^"USD" (make ^^"USD" ^"USD" 12 10) (makeNeg ^^"USD" ^"USD" 3 11) === { _1 = +899 % !100, _2 = ^"USD" }
let test11 = assert : show ^^"NZD" (add ^^"NZD" (makeNeg ^^"NZD" ^"NZD" 12 10) (makeNeg ^^"NZD" ^"NZD" 3 11)) === "-15.21 NZD"

-- let test13 = assert : show (add ^(makeNeg ^^"NZD" ^"NZD" 12 10) (makeNeg ^^"AUD" 3 11 ^"AUD") Prf) === "nodata"

let test12 = assert : show ^^"GBP" (addCents ^^"GBP" (+27 % !1) (make ^^"GBP"  ^"GBP"  20 75)) === "+21.02 GBP"

-- original value is negative even though shows zero: cos there are extras!
let test13 = assert : show ^^"GBP" (addCents ^^"GBP" (-1 % !10) (make ^^"GBP"  ^"GBP"  0 0)) === "-0.00 GBP*"
let test14 = assert : show ^^"GBP" (addCents ^^"GBP" (+1 % !10) (make ^^"GBP"  ^"GBP"  0 0)) === "+0.00 GBP*"

let test15 = assert : show ^^"GBP" (make ^^"GBP" ^"GBP" 0 0) === "+0.00 GBP"
let test16 = assert : show ^^"GBP" (add ^^"GBP" (make ^^"GBP"  ^"GBP"  12 50) (make ^^"GBP"  ^"GBP"  7 49)) === "+19.99 GBP"
-- let test19 = assert : show (add ^(make 12 50 ^"AUD") (make ^^"GBP"  ^"GBP"  7 49)) === "nodata"
let test17 = assert : show ^^"GBP" (add ^^"GBP" (makeNeg ^^"GBP" ^"GBP" 12 50) (make ^^"GBP" ^"GBP"  7 49)) === "-5.01 GBP"

let test18 = assert : add ^^"GBP" (make ^^"GBP"  ^"GBP"  25 30) (make ^^"GBP" ^"GBP"  25 30) === { _1 = +253 % !5, _2 = ^"GBP" }


let test19 = assert : show ^^"GBP" (addCents ^^"GBP" (+1 % !200) (negate ^^"GBP" (make ^^"GBP"  ^"GBP"  1 32)))
===
"-1.31 GBP*"

let test20 = assert : showN ^^"GBP" 5 (addCents ^^"GBP" (+1 % !200) (negate ^^"GBP" (make ^^"GBP"  ^"GBP"  1 32)))
===
"-1.31995 GBP"

let test21 = assert : showN ^^"GBP" 10 (addCents ^^"GBP" (+1 % !200) (negate ^^"GBP" (make ^^"GBP"  ^"GBP"  1 32)))
===
"-1.3199500000 GBP"

let test22 = assert : add ^^"NZD" (nzd 1 20) (nzd 13 14)
===
{ _1 = +717 % !50, _2 = ^"NZD" }

let test23 = assert : show ^^"NZD" (add ^^"NZD" (nzd 1 20) (nzd 13 14))
===
"+14.34 NZD"


let test24 = assert : add NZD (nzd 10 15) (nzd 20 1)
===
{ _1 = +754 % !25, _2 = ^"NZD" }

let test25 = assert : minus USD (usd 10 15) (usd 20 1)
===
{ _1 = -493 % !50, _2 = ^"USD" }

let test26 = assert : show USD (minus USD (usd 10 15) (usd 20 1))
===
"-9.86 USD"

let test27 = assert : show USD (addCents USD (+51 % !100) (minus USD (usd 10 15) (usd 20 1)))
===
"-9.85 USD*"

let test28 = assert : showN USD 5 (addCents USD (+51 % !100) (minus USD (usd 10 15) (usd 20 1)))
===
"-9.85490 USD"

let test29 = assert : showN USD 5 (addCents USD (+51 % !1) (minus USD (usd 10 15) (usd 20 1)))
===
"-9.35000 USD"

let test30 = assert : showN ^^"USD" 5 (addCents ^^"USD" (+1 % !2) (usd 14 99))
===
"+14.99500 USD"

in {
USD,
NZD,
AUD,
EUR,
GBP,
Value,
make,
makeNeg,
negate,
equal,
addCents,
multiply,
add,
minus,
showN,
show,

usd,
gbp,
nzd,
aud,
eur
}

