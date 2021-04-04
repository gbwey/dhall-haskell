let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall
let ss = ./sort.dhall

let NonEmpty = \(a : Type) -> { _1 : a, _2 : List a }

let make =
    \(a : Type)
 -> \(x : a)
 -> \(xs : List a)
 -> { _1 = x, _2 = xs }

let toList =
    \(a : Type)
 -> \(xs : NonEmpty a)
 -> [xs._1] # xs._2
 : List a

let fromListProof =
    \(a : Type)
 -> \(xs : List a)
 -> \(prf : Proof/fromBool ^^"nonempty.dhall: fromListProof list is empty" (Natural/isZero (List/length a xs) == False))
 -> let t = NonEmpty a
    in merge
       { None = PVoid/error ^^"nonempty.dhall: fromListProof how did we get here?" t
       , Some = \(x : a) -> { _1 = x, _2 = pp.List.drop 1 a xs }
       }
       (List/head a xs)
 : t

let reverse =
    \(a : Type)
 -> \(xs : NonEmpty a)
 -> merge { None = { _1 = xs._1, _2 = [] : List a }
             , Some = \(x : a) -> { _1 = x, _2 = List/reverse a (pp.List.take (Natural/subtract 1 (List/length a xs._2)) a xs._2) # [xs._1] }
             } (List/last a xs._2)
   : NonEmpty a

let head =
    \(a : Type)
 -> \(xs : NonEmpty a)
 -> xs._1
  : a

let last =
    \(a : Type)
 -> \(xs : NonEmpty a)
 -> merge { None = xs._1, Some = \(x : a) -> x } (List/last a xs._2)
  : a

let tail =
    \(a : Type)
 -> \(xs : NonEmpty a)
 -> xs._2
  : List a

let mappend =
    \(a : Type)
 -> \(xs : NonEmpty a)
 -> \(ys : NonEmpty a)
 -> { _1 = xs._1, _2 = xs._2 # [ys._1] # ys._2 }
   : NonEmpty a

let foldMap1 =
    \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(xs : NonEmpty a)
 -> \(mappend : b -> b -> b)
 -> ss.foldl
      a
      xs._2
      b
      (\(x : b) -> \(y : a) -> mappend x (f y))
      (f xs._1)
    : b

let fold1 =
    \(a : Type)
 -> foldMap1 a a (\(x : a) -> x)
    : NonEmpty a -> (a -> a -> a) -> a

let test1 = assert : fold1 oo.Ordering (make oo.Ordering oo.EQ [oo.LT, oo.GT]) oo.mappend === oo.LT
let test2 = assert : fold1 oo.Ordering (make oo.Ordering oo.GT [oo.EQ,oo.LT]) oo.mappend === oo.GT
let test3 = assert : fold1 oo.Ordering (make oo.Ordering oo.EQ [oo.EQ]) oo.mappend === oo.EQ
let test4 = assert : fold1 oo.Ordering (make oo.Ordering oo.GT ([] : List oo.Ordering)) oo.mappend === oo.GT
let test5 = assert : foldMap1 Natural oo.Ordering (\(x : Natural) -> if Natural/even x then oo.LT else oo.EQ) (make Natural 1 [3,7]) oo.mappend === oo.EQ
let test6 = assert : foldMap1 Natural oo.Ordering (\(x : Natural) -> if Natural/even x then oo.LT else oo.GT) (make Natural 2 [5,2,3,10,7]) oo.mappend === oo.LT

let test7 = assert : fold1 Text { _1 = "a", _2 = ["b","c"] } (\(x : Text) -> \(y : Text) -> x ++ y)
===
"abc"

let test8 = assert : foldMap1 Natural Text Natural/show { _1 = 10, _2 = [11,12] } (\(x : Text) -> \(y : Text) -> x ++ y)
===
"101112"

let test9 = assert : head Natural { _1 = 10, _2 = [11,12] } === 10
let test10 = assert : head Natural { _1 = 10, _2 = [11] } === 10
let test11 = assert : head Natural { _1 = 10, _2 = [] : List Natural } === 10

let test12 = assert : last Natural { _1 = 10, _2 = [11,12] } === 12
let test13 = assert : last Natural { _1 = 10, _2 = [11] } === 11
let test14 = assert : last Natural { _1 = 10, _2 = [] : List Natural } === 10
let test15 = assert : reverse Natural { _1 = 10, _2 = [] : List Natural } === { _1 = 10, _2 = [] : List Natural }
let test16 = assert : reverse Natural { _1 = 10, _2 = [11] } === { _1 = 11, _2 = [10] }
let test17 = assert : reverse Natural { _1 = 10, _2 = [11,12] } === { _1 = 12, _2 = [11,10] }

let test18 = assert : fromListProof Natural [1,2,3,4] Prf === { _1 = 1, _2 = [ 2, 3, 4 ] }
let test19 = assert : fromListProof Natural [99] Prf === { _1 = 99, _2 = [] : List Natural }
-- let test20 = assert : fromListProof Natural ([] : List Natural) Prf

in
{
NonEmpty,
make,
foldMap1,
fold1,
mappend,
mconcat = foldMap1,
head,
last,
tail,
reverse,
toList,
fromListProof
}
