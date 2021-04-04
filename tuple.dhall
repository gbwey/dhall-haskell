let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall

let Pair : forall (a : Type) -> forall (b : Type) -> Type =
      \(a : Type)
   -> \(b : Type)
   -> { _1 : a, _2 : b }

let mkPair =
      \(a : Type)
   -> \(b : Type)
   -> \(x : a)
   -> \(y : b)
   -> { _1 = x, _2 = y }
   : Pair a b

let Triple =
     \(a : Type)
  -> \(b : Type)
  -> \(c : Type)
  -> { _1 : a, _2 : b, _3 : c }

let mkTriple =
      \(a : Type)
   -> \(b : Type)
   -> \(c : Type)
   -> \(x : a)
   -> \(y : b)
   -> \(z : c)
   -> { _1 = x, _2 = y, _3 = z }
   : Triple a b c

let compare =
    \(a : Type)
 -> \(b : Type)
 -> \(cmpa : a -> a -> oo.Ordering)
 -> \(cmpb : b -> b -> oo.Ordering)
 -> \(tp1 : Pair a b)
 -> \(tp2 : Pair a b)
 -> merge {
    , LT = oo.LT
    , EQ = cmpb tp1._2 tp2._2
    , GT = oo.GT
    } (cmpa tp1._1 tp2._1)
    : oo.Ordering

let fst =
      \(a : Type)
   -> \(b : Type)
   -> \(p : Pair a b)
   -> p._1
   : a

let snd =
      \(a : Type)
   -> \(b : Type)
   -> \(p : Pair a b)
   -> p._2
   : b

let swap =
     \(a : Type)
  -> \(b : Type)
  -> \(z : Pair a b)
  -> { _1 = z._2, _2 = z._1 }
  : Pair b a

let fsts =
     \(a : Type)
  -> \(b : Type)
  -> let s = Pair a b
     in pp.List.map s a (fst a b)
  : List s -> List a

let snds =
     \(a : Type)
  -> \(b : Type)
  -> let s = Pair a b
     in pp.List.map s b (snd a b)
  : List s -> List b

let first =
     \(a : Type)
  -> \(b : Type)
  -> \(a0 : Type)
  -> \(f : a -> a0)
  -> \(p : Pair a b)
  -> mkPair a0 b (f p._1) p._2
  : Pair a0 b

let second =
     \(a : Type)
  -> \(b : Type)
  -> \(b0 : Type)
  -> \(f : b -> b0)
  -> \(p : Pair a b)
  -> mkPair a b0 p._1 (f p._2)
  : Pair a b0

let mapFsts =
     \(a : Type)
  -> \(b : Type)
  -> \(a0 : Type)
  -> \(f : a -> a0)
  -> let s = Pair a b
     let t = Pair a0 b
     in pp.List.map s t (\(p : s) -> p // { _1 = f p._1 })
  : List s -> List t

let mapSnds =
     \(a : Type)
  -> \(b : Type)
  -> \(b0 : Type)
  -> \(f : b -> b0)
  -> let s = Pair a b
     let t = Pair a b0
     in pp.List.map s t (\(p : s) -> p // { _2 = f p._2 })
  : List s -> List t

let mapBoths =
     \(a : Type)
  -> \(b : Type)
  -> \(a0 : Type)
  -> \(b0 : Type)
  -> \(f : a -> a0)
  -> \(g : b -> b0)
  -> let s = Pair a b
     let t = Pair a0 b0
     in pp.List.map s t (\(p : s) -> { _1 = f p._1, _2 = g p._2 })
  : List s -> List t

let toTuple =
     \(a : Type)
  -> \(def1 : a)
  -> \(def2 : a)
  -> \(xs : List a)
  -> let f = \(y : a) -> merge { None = mkPair a a y def2, Some = \(z : a) -> mkPair a a y z } (List/head a (pp.List.drop 1 a xs))
     in merge { None = mkPair a a def1 def2, Some = f } (List/head a xs)
     : Pair a a

let amp =
   \(a : Type)
   -> \(b : Type)
   -> \(c : Type)
   -> \(f : a -> b)
   -> \(g : a -> c)
   -> \(x : a)
   -> mkPair b c (f x) (g x)
   : Pair b c
let mempty =
   \(a : Type)
-> \(b : Type)
-> \(m : a)
-> \(n : b)
-> mkPair a b m n
  : Pair a b

let mappend =
   \(a : Type)
-> \(b : Type)
-> \(m : a -> a -> a)
-> \(n : b -> b -> b)
-> \(x : Pair a b)
-> \(y : Pair a b)
-> mkPair a b (m x._1 y._1) (n x._2 y._2)
  : Pair a b

let mconcat =
    \(a : Type)
 -> \(b : Type)
 -> \(m : a -> a -> a)
 -> \(n : b -> b -> b)
 -> \(z : Pair a b)
 -> \(xs : List (Pair a b))
 -> List/fold (Pair a b) xs (Pair a b) (\(x : Pair a b) -> \(y : Pair a b) -> { _1 = m x._1 y._1, _2 = n x._2 y._2 }) z
  : Pair a b

let headProof =
     \(a : Type)
  -> \(xs : List a)
  -> \(prf : Proof/fromBool ^^"headProof: empty list" (pp.List.null a xs == False))
  -> merge { None = PVoid/undefined a, Some = \(x : a) -> x } (List/head a xs)
     : a

let lastProof =
     \(a : Type)
  -> \(xs : List a)
  -> \(prf : Proof/fromBool ^^"lastProof: empty list" (pp.List.null a xs == False))
  -> merge { None = PVoid/undefined a, Some = \(x : a) -> x } (List/last a xs)
     : a

let unconsProof =
     \(a : Type)
  -> \(xs : List a)
  -> \(prf : Proof/fromBool ^^"unconsProof: empty list" (pp.List.null a xs == False))
  -> let t = Pair a (List a)
     let f = \(x : a) -> { _1 = x, _2 = pp.List.drop 1 a xs }
     in f (headProof a xs prf)
     : t

let unsnocProof =
     \(a : Type)
  -> \(xs : List a)
  -> \(prf : Proof/fromBool ^^"unsnocProof: empty list" (pp.List.null a xs == False))
  -> let t = Pair (List a) a
     let f = \(x : a) -> { _1 = pp.List.take (Natural/subtract 1 (List/length a xs)) a xs, _2 = x }
     in f (lastProof a xs prf)
     : t

let uncons =
     \(a : Type)
  -> \(xs : List a)
  -> let t = Pair a (List a)
     in pp.Optional.map a t (\(x : a) -> { _1 = x, _2 = pp.List.drop 1 a xs }) (List/head a xs)
     : Optional t

let unsnoc =
     \(a : Type)
  -> \(xs : List a)
  -> let t = Pair (List a) a
     in pp.Optional.map a t (\(x : a) -> { _1 = pp.List.take (Natural/subtract 1 (List/length a xs)) a xs, _2 = x }) (List/last a xs)
     : Optional t

let test1 = assert : fst Natural Bool { _1 = 25, _2 = False } === 25
let test2 = assert : snd Natural Bool { _1 = 25, _2 = False } === False
let test3 = assert : swap Natural Bool { _1 = 25, _2 = False } === { _1 = False, _2 = 25 }
let test4 = assert : fsts Natural Bool
      [ { _1 = 25, _2 = True }
      , { _1 = 27, _2 = False }
      , { _1 = 12, _2 = False }
      , { _1 = 2, _2 = True }
      ] === [25,27,12,2]
let test5 = assert : snds Natural Bool
      [ { _1 = 25, _2 = True }
      , { _1 = 27, _2 = False }
      , { _1 = 12, _2 = False }
      , { _1 = 2, _2 = True }
      ] === [True,False,False,True]
let test6 = assert : toTuple Natural 99 999 [10,13,12] === { _1 = 10, _2 = 13 }
let test7 = assert : toTuple Natural 99 999 [10] === { _1 = 10, _2 = 999 }
let test8 = assert : toTuple Natural 99 999 ([] : List Natural) === { _1 = 99, _2 = 999 }
let test9 = assert : mapFsts Natural Bool Text Natural/show
      [ { _1 = 25, _2 = True }
      , { _1 = 27, _2 = False }
      , { _1 = 12, _2 = False }
      , { _1 = 2, _2 = True }
      ] ===
        [ { _1 = "25", _2 = True }
        , { _1 = "27", _2 = False }
        , { _1 = "12", _2 = False }
        , { _1 = "2", _2 = True }
      ]
let test10 = assert : mkTriple Double Double Double -1.3e-10  +14.0000001 -13.0000000000 === { _1 = -1.3e-10, _2 = +14.0000001, _3 = -13.0000000000 }

let test11 = assert : unconsProof Natural [1,2,3] Prf === { _1 = 1, _2 = [ 2, 3 ] }
let test12 = assert : unsnocProof Natural [1,2,3] Prf === { _1 = [1,2], _2 = 3 }
let test13 = assert : headProof Natural [99,2,3] Prf === 99

--let test13 = assert : unconsProof Natural ([] : List Natural) Prf === None (Pair Natural (List Natural))
--let test14 = assert : unsnocProof Natural ([] : List Natural) Prf === None (Pair (List Natural) Natural)

let test14 = assert : headProof (Pair Natural Natural) [ { _1 = 10, _2 = 20}, { _1 = 99, _2 = 0 } ] Prf
===
{ _1 = 10, _2 = 20 }

let test15 = assert : unconsProof (Pair Natural Natural) [ { _1 = 10, _2 = 20}, { _1 = 99, _2 = 0 } ] Prf
===
{ _1 = { _1 = 10, _2 = 20 }, _2 = [ { _1 = 99, _2 = 0 } ] }

let test16 = assert : unsnocProof (Pair Natural Natural) [ { _1 = 10, _2 = 20}, { _1 = 99, _2 = 0 } ] Prf
===
{ _1 = [ { _1 = 10, _2 = 20 } ], _2 = { _1 = 99, _2 = 0 } }

let test17 = assert : unconsProof Natural [ 10,11,12] Prf
===
{ _1 = 10, _2 = [ 11, 12 ] }

let test18 = assert : unsnocProof Natural [ 10,11,12] Prf
===
{ _1 = [ 10, 11 ], _2 = 12 }

let test19 = assert : unsnoc Natural [ 10,11,12]
===
Some { _1 = [ 10, 11 ], _2 = 12 }

let test20 = assert : uncons (Pair Natural Natural) [ { _1 = 10, _2 = 20}, { _1 = 99, _2 = 0 } ]
===
Some { _1 = { _1 = 10, _2 = 20 }, _2 = [ { _1 = 99, _2 = 0 } ] }

let test21 = assert : uncons Natural ([] : List Natural)
===
None { _1 : Natural, _2 : List Natural }

let test22 = assert : unsnoc Natural ([] : List Natural)
===
None { _1 : List Natural, _2 : Natural }

in {
, Pair
, mkPair
, Triple
, mkTriple
, fst
, snd
, swap
, first
, second
, mapFsts
, mapSnds
, mapBoths
, toTuple
, fsts
, snds
, amp

, mempty
, mappend
, mconcat

, uncons
, unsnoc

, unconsProof
, unsnocProof

, headProof
, lastProof

, compare
}

{-
List/fold Natural [1,2,3] (List Natural -> List Natural) (\(a : Natural) -> \(k : List Natural -> List Natural) -> \(x : List Natural) -> [a] #  k x) (\(xs : List Natural) -> xs # [999]) [10,11]
[ 1, 2, 3, 10, 11, 999 ]

List/fold Natural [1,2,3] (List Natural -> List Natural) (\(a : Natural) -> \(k : List Natural -> List Natural) -> \(x : List Natural) -> [a] #  k x) (x.pp.Function.identity (List Natural)) [999]
[ 1, 2, 3, 999 ]

> x.tp.head Natural ([] : List Natural) Prf

Error: Wrong type of function argument

- PVoid ...
+ Proof ...

1| x.tp.head Natural ([] : List Natural) Prf

(stdin):1:1

> x.tp.last Natural ([] : List Natural)

\(prf : PVoid) -> PVoid/undefined Natural

> :t x.tp.last Natural ([] : List Natural)

forall(prf : PVoid) -> Natural

> x.tp.last Natural ([] : List Natural)

\(prf : PVoid) -> PVoid/undefined Natural

> x.tp.last Natural ([] : List Natural) Prf

Error: Wrong type of function argument

- PVoid ...
+ Proof ...

1| x.tp.last Natural ([] : List Natural) Prf

(stdin):1:1
-}