{-
the only reason i can get away with PVoid/undefined is I dont normalize any further so it is basically STUCK so matches anything
PVoid/error msg a
as soon as I simplify it then stuff breaks: simplifying to PVoid msg will fail using merge cos handlers are different:ie is type PVoid not type 'a'

Proofs on things like head/last/uncons/unsnoc are odd: means we expect a non empty list
  so make it a nonempty type: eg { _1 : a, _2 : List a }

Proofs on This/That/These are also odd as we probably shouldnt have used These in the first place

Proofs on ListFixed/Matrix make more sense where we ensure the indices are in bounds

-}
-- now works cos loosened up Kind restriction in TypeCheck
-- sigmaTest2 uses PVoid/kindUndefined so need to loosen up and allow kinds for this to work
{-
if True then Bool else PVoid/kindUndefined Type

Error: 'if' branch is not a term
1| if True then Bool else PVoid/kindUndefined Type
-}

-- at the end of the day we want to compare a Type as an arg to a fixed Type
-- until we can do that we are screwed: Proof/typeEqual didnt work nor did 'same' as a keyword
-- merge doesnt work that way
-- we need some more sophisticated machinery to make this happen
-- \(a : Type) -> a == Natural : Bool

-- we could create a ListKind which works on Kinds so we can hold Types but doesnt solve the above problem

-- now we can store [Bool] but cant assert
-- we can assert Bool === Bool
-- still cant assert [Bool] === [Bool]
-- List takes a Type to Type so we need a higher order ListKind
-- the issue is App is Type to Type not Kind to Kind
{-
assert : [Bool] === [Bool]

Error: Wrong type of function argument

- Type
+ Kind
-}
-- dictionary of Type and Natural: cant store Type in a List!
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let ll = ./list.dhall
let tt = ./text.dhall
let re = ./regex.dhall

let test1 = assert : Proof/toBool (SS/equal !!1 !!1) === True
let test2 = assert : Proof/toBool (SS/equal !!3 !!3) === True
let test3 = assert : Proof/toBool (SS/equal !!2 !!1) === False
let test4 = assert : Proof/toBool (SS/equal !!1 !!2) === False

let test5 = assert : Proof/toBool (SS/lessThan !!1 !!2) === True
let test6 = assert : Proof/toBool (SS/lessThan !!1 !!2) === True
let test7 = assert : Proof/toBool (SS/lessThan !!1 !!1) === False
let test8 = assert : Proof/toBool (SS/lessThan !!2 !!1) === False
let test9 = assert : Proof/toBool (SS/lessThan !!10 !!11) === True
let test10 = assert : Proof/toBool (SS/lessThan !!12 !!12) === False
let test11 = assert : Proof/toBool (SS/lessThan !!12 !!19) === True

let test12 = assert : Proof/toBool (Proof/fromBool ^^"test8" (pp.List.all Natural (pp.Natural.greaterThan 3) [1,1])) === True
let test13 = assert : Proof/toBool (Proof/fromBool ^^"test9" (pp.List.all Natural (pp.Natural.greaterThan 3) [1,1])) === True
let test14 = assert : Proof/toBool (Proof/fromBool ^^"test10" (pp.List.all Natural (pp.Natural.greaterThan 3) [1,3])) === False

let test15 = assert : Proof/toBool (Proof/fromBool ^^"test11" (tt.allInList ["x"] ["a","b","c"])) === False
let test16 = assert : Proof/toBool (Proof/fromBool ^^"test12" (tt.allInList ["a","b","b","a"] ["a","b","c"])) === True
let test17 = assert : Proof/toBool (Proof/fromBool ^^"test13" (tt.allInList ["a","b","b","w","a"] ["a","b","c"])) === False

let matchRegexList =
    \(r : Regex)
 -> \(xs : List Text)
 -> \(prf : Proof/fromBool ^^"proof.dhall: matchRegList doesn't match all in the list" (pp.List.all Text (Regex/match r) xs))
 -> {=}
  : {}

let test18 = assert : matchRegexList ~"^\d{3}-\d{3}-\d{4}$" ["123-222-1234" , "123-111-9999", "111-123-9912"] Prf === {=}
--let test21 = assert : matchRegexList ~"^\d{3}-\d{3}-\d{4}$" ["123-222-1234" , "123-111-9999", "111-123-99123"] Prf === {=}
{-
-- take a list of m values and match against r
-- they all have to match
-- pass the results to the callback f (_2 is fixed list of n)
let matchRegexList =
    \(m : Type)
 -> \(n : Type)
 -> \(b : Type)
 -> \(r : Regex)
 -> \(xs : ListFixed m Text)
 -> \(f : Text -> ListFixed n Text -> b)
 -> \(prf : Proof/fromBool (pp.List.all Text (Regex/match r) xs))
 -> List/fold
     xs
  : ListFixed m b
-}

let matchRegexListCallback =
    \(b : Type)
 -> \(r : Regex)
 -> \(xs : List Text)
 -> \(f : List (List Text) -> b)
 -> \(prf : Proof/fromBool ^^"proof.dhall matchRegexListCallback" (pp.List.all Text (Regex/match r) xs))
 -> pp.List.map Text b (\(x : Text) -> f (re.scanSnds r x)) xs
  : List b

let test19 = assert : matchRegexListCallback (List (List Text)) ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" ["123.1.12.11","1.2.1.2"] (\(x : List (List Text)) -> x) Prf
===
[ [ [ "123", "1", "12", "11" ] ], [ [ "1", "2", "1", "2" ] ] ]

{-
x.p.matchRegexListCallback (List (List Text)) ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" ["123.1.12.11","1.3","1.2.1.2"] Prf (\(x : List (List Text)) -> x)

Error: Wrong type of function argument

- PVoid ...
+ Proof ...
1| x.p.matchRegexListCallback (List (List Text)) ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" ["123.1.12.11","1.3","1.2.1.2"] Prf
-}

let sumBinaryList =
    \(xs : List Natural)
 -> \(prf : Proof/fromBool ^^"proof.dhall sumBinaryList" (ll.allInListNat xs [0,1]))
 -> let t = { _1 : Natural, _2 : Natural }
    let ret = List/fold
      Natural
      xs
      t
      (\(x : Natural) -> \(z : t) -> { _1 = z._1 * 2, _2 = z._2 + x * z._1 })
      { _1 = 1, _2 = 0 }
    in ret._2

let test20 = assert : sumBinaryList [1,0,1] Prf === 5
let test21 = assert : sumBinaryList [1,0,1,1,1,1,1,0] Prf === 0b10111110
let test22 = assert : sumBinaryList ([] : List Natural) Prf === 0
let test23 = assert : sumBinaryList [1,1,1,0] Prf === 14
--let test22 = assert : sumBinaryList [1,0,1,2] Prf === 2

let ip4List =
    \(i1 : Natural)
 -> \(i2 : Natural)
 -> \(i3 : Natural)
 -> \(i4 : Natural)
 -> \(prf : ll.ip4Proof i1 i2 i3 i4)
 -> {=}

let test24 = assert : ip4List 12 13 4 255 Prf === {=}
let test25 = assert : ip4List 0 0 0 0 Prf === {=}
--let test20 = assert : ip4List 256 13 4 255 Prf === {=}

let testProofB =
    \(i : Natural)
 -> \(prf : Proof/fromBool ^^"proof.dhall testProofB" (pp.Natural.equal i 4))
 -> {=}

let testProofA =
    \(i : Natural)
 -> \(prf : Proof/fromBool ^^"proof.dhall testProofA" (pp.Natural.equal i 4))
 -- -> \(prf : Proof/fromBool (pp.Natural.equal 4 i)) will fail! has to be exact
 -- -> (i + 0) works though
 -> testProofB i prf

let test26 = assert : testProofA 4 Prf === {=}

let test27 = assert : merge { None = PVoid/undefined Natural, Some = \(x : Natural) -> x } (Some 4) === 4
let test28 = assert : merge { None = PVoid/undefined Natural, Some = \(x : Natural) -> x } (List/head Natural [99,2,3]) === 99

-- needed to loosen up TypeCheck.hs to allow Kinds through
let sigmaTest2 =
    \(n : Natural)
 -> \(prf : Proof/fromBool ^^"proof.dhall: sigmaTest2 n must be less than 4" (pp.Natural.lessThan n 4))
 -> if pp.Natural.equal n 0 then Natural
    else if pp.Natural.equal n 1 then NonZero
    else if pp.Natural.equal n 2 then Integer
    else if pp.Natural.equal n 3 then Rational
    else PVoid/kindUndefined Type
--    else {}

let test32 = assert : sigmaTest2 0 Prf === Natural
let test33 = assert : sigmaTest2 1 Prf === NonZero
let test34 = assert : sigmaTest2 2 Prf === Integer
let test35 = assert : sigmaTest2 3 Prf === Rational
--let test30 = assert : sigmaTest2 4 Prf === Natural

let test36 =
   let f = \(n : Natural) -> if Natural/isZero n then Bool else NonZero
   let test1 = assert : f 1 === NonZero
   let test2 = assert : f 0 === Bool
   in {=}

in {
ip4List,
sumBinaryList,
testProofA,
testProofB,
matchRegexList,
matchRegexListCallback,
sigmaTest2
}

{-
> :let g = let f = \(n : Natural) -> if Natural/isZero n then Bool else NonZero in f
Error: 'if' branch is not a term [[it is now loosened up so will not give that error]]
-}