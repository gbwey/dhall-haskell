{-
SS/toNonZero Bool  -- this doesnt evaluate

SS/toNonZero !!3 === !!3

same with ListFixed n -- we can choose any 'n' not that we could instantiate anything
other than SS types but still ....
-}
-- todo: replace ListFixed/head with PVoid/undefined or PVoid/error [used in ListFixed/fromList also]
-- got rid of all NonZero cos is a lie: use SS !!1 or !!1 !!2 !!3: NonZero loses information: need inductive types to manipulate eg in cons where we add an extra element
-- awkward: need to concat fixedlists together without providing a default value cos we have to drag out the head to get a value: yurk
-- cant use NonZero cos we lose induction so cannot change the NonZero value!
-- convert these to use NonZero instead of SS !!1 etc
-- cant do it cos NonZero is a value not a type unlike SS!! so it wouldnt be able to distinguish NonZeros from each other
-- create local versions that do the conversion for you

-- how to avoid ListFixed/head a [we dont need the 'a'] but need it to typecheck in typecheck.hs
{- need to conjure up an 'a' somehow? since List/reverse needs it we are really hosed
-- the only diff is that ListFixed is never empty!!!
-- need to encode the length at the type level

        ListFixedHead -> do
            return (VHPi "a" (VConst Type) (\a -> VListFixed a ~> a))

-}
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall
let ll = ./list.dhall
let nz = ./nonzero.dhall
let r = ./rational.dhall
let nn = ./natural.dhall
let ii = ./integer.dhall
let ss = ./sort.dhall
let sr = ./semiring.dhall

let defError =
  \(a : Type)
  -> PVoid/error ^^"oops should never be run:program error" a

-- way too slow! use fromListGE
let fromListExact =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : List a)
 -> let len = List/length a xs
    in if pp.Natural.equal (SS/toNatural n) len
    then ListFixed/fromList n a (defError a) xs
    else PVoid/error (Sym/fromText ("listfixed.dhall: fromListExact: list length=" ++ Natural/show len ++ " is not the same as n=" ++ Natural/show (SS/toNatural n))) (ListFixed n a)
 : ListFixed n a

let fromListGE =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : List a)
 -> ListFixed/fromList n a (defError a) xs
 : ListFixed n a

-- extends or truncates a fixed list using head as default
let lift =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed m a)
 -> ListFixed/fromList n a (ListFixed/head m a xs) (ListFixed/toList m a xs)
   : ListFixed n a

let fromListProof =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : List a)
 -> \(prf : Proof/fromBool ^^"fromListProof: list is smaller than n"
         (pp.Natural.greaterThanEqual (List/length a xs) (SS/toNatural n))
     )
 -> ListFixed/fromList n a (defError a) xs
  : ListFixed n a

let map =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(xs : ListFixed n a)
 -> let ret = List/build
      b
      (   \(list : Type)
       -> \(cons : b -> list -> list)
       -> \(nil : list)
       -> List/fold
               a
               (ListFixed/toList n a xs)
               list
               (\(x : a) -> \(z : list) -> cons (f x) z)
               nil
      )
    in fromListGE n b ret
    : ListFixed n b

let mapAmp =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(xs : ListFixed n a)
-> let t = { _1 : a, _2 : b }
   in map n a t (\(x : a) -> { _1 = x, _2 = f x }) xs
 : ListFixed n t

let vecNaturalN =
    \(n : Type)
 -> \(start : Natural)
 -> \(step : Natural)
 -> fromListGE n Natural (nn.enumerateN (SS/toNatural n) start step)
  : ListFixed n Natural

let vecNatural =
    \(n : Type)
 -> vecNaturalN n 0 1
  : ListFixed n Natural

-- starts at 1 not 0
let vecNonZeroN =
    \(n : Type)
 -> \(start : NonZero)
 -> \(step : NonZero)
 -> fromListGE n NonZero (nz.enumerateN (SS/toNatural n) start step)
  : ListFixed n NonZero

let vecNonZero =
    \(n : Type)
 -> vecNonZeroN n !1 !1
  : ListFixed n NonZero

let vecIntegerN =
    \(n : Type)
 -> \(start : Integer)
 -> \(step : Integer)
 -> fromListGE n Integer (ii.enumerateN (SS/toNatural n) start step)
  : ListFixed n Integer

let vecInteger =
    \(n : Type)
 -> vecIntegerN n +0 +1
  : ListFixed n Integer

let vecRationalN =
    \(n : Type)
 -> \(start : Rational)
 -> \(step : Rational)
 -> fromListGE n Rational (r.enumerateN (SS/toNatural n) start step)
  : ListFixed n Rational

let vecRational =
    \(n : Type)
 -> vecRationalN n r.zero r.one
  : ListFixed n Rational

let replicate =
    \(n : Type)
 -> \(a : Type)
 -> \(x : a)
 -> ListFixed/fromList n a x ([] : List a)
 : ListFixed n a

let cons =
    \(n : Type)
 -> \(a : Type)
 -> \(x : a)
 -> \(xs : ListFixed n a)
 -> let n0 = SS/add !!1 n
    in fromListGE n0 a ([x] # ListFixed/toList n a xs)
   : ListFixed n0 a

let snoc =
    \(n : Type)
 -> \(a : Type)
 -> \(x : a)
 -> \(xs : ListFixed n a)
-> let n0 = SS/add !!1 n
   in fromListGE n0 a (ListFixed/toList n a xs # [x])
   : ListFixed n0 a

let reverse =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed n a)
 -> let bs = List/reverse a (ListFixed/toList n a xs)
    in fromListGE n a bs
    : ListFixed n a

let uncons =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed n a)
 -> { _1 = ListFixed/head n a xs, _2 = ListFixed/tail n a xs }
   : { _1 : a, _2 : List a }

let unsnoc =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed n a)
 -> let bs = ListFixed/toList n a xs
    let rs = ll.splitAt a (Natural/subtract 1 (List/length a bs)) bs
    in { _1 = rs._1
       , _2 = merge { None = PVoid/undefined a, Some = \(x : a) -> x } (List/head a rs._2)
       }
   : { _1 : List a, _2 : a }

let compare =
    \(n : Type)
 -> \(a : Type)
 -> \(f : a -> a -> oo.Ordering)
 -> \(xs : ListFixed n a)
 -> \(ys : ListFixed n a)
 -> ll.compare a f (ListFixed/toList n a xs) (ListFixed/toList n a ys)
   : oo.Ordering

-- dont have to be the same length so not mappend as it is a different type
let append =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed m a)
 -> \(ys : ListFixed n a)
 -> let tot = SS/add m n
    in fromListGE tot a (ListFixed/toList m a xs # ListFixed/toList n a ys)
   : ListFixed tot a

-- has to be the same length
let zipWith =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b -> c)
 -> \(xs : ListFixed n a)
 -> \(ys : ListFixed n b)
 -> let ret = ll.zipWithTrunc a b c f (ListFixed/toList n a xs) (ListFixed/toList n b ys)
    in fromListGE n c ret
       : ListFixed n c

let zip =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(xs : ListFixed n a)
 -> \(ys : ListFixed n b)
 -> let t = { _1 : a, _2 : b }
    in zipWith n a b t (\(x : a) -> \(y : b) -> { _1 = x, _2 = y }) xs ys
    : ListFixed n t

let getValProof =
    \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(xs : ListFixed n a)
 -> \(prf : Proof/fromBool ^^"listfixed.dhall: getValProof index >= size" (pp.Natural.lessThan i (SS/toNatural n)))
 -> let ma = List/head a (pp.List.drop i a (ListFixed/toList n a xs))
    in merge { None = ListFixed/head n a xs, Some = \(x : a) -> x } ma
    : a

let setValProof =
    \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(x : a)
 -> \(xs : ListFixed n a)
 -> \(prf : Proof/fromBool ^^"listfixed.dhall: setValProof index >= size" (pp.Natural.lessThan i (SS/toNatural n)))
 -> let ys = ListFixed/toList n a xs
    let a1 = pp.List.take i a ys
    let a5 = pp.List.drop (i + 1) a ys
    in fromListGE n a (a1 # [x] # a5)
    : ListFixed n a

let deleteValProof =
    \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(xs : ListFixed n a)
 -> \(prf1 : Proof/fromBool ^^"listfixed.dhall: deleteValProof index >= size" (pp.Natural.lessThan i (SS/toNatural n)))
 -> \(prf2 : SS/lessThan !!1 n)
 -> let n0 = SS/subtract !!1 n
    let ys = ListFixed/toList n a xs
    let a1 = pp.List.take i a ys
    let a5 = pp.List.drop (i + 1) a ys
    in fromListGE n0 a (a1 # a5)
    : ListFixed n0 a

let substringProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed m a)
 -> \(start : Natural)
 -> \(prf1 : Proof/fromBool ^^"list.dhall: substringProof: start index must be less than the size of the list" (pp.Natural.lessThan start (SS/toNatural m)))
 -> \(prf2 : Proof/fromBool ^^"list.dhall: substringProof: length must be less than or equal to the size of the list" (pp.Natural.lessThanEqual (start + SS/toNatural n) (SS/toNatural m)))
 -> let ys = pp.List.take (SS/toNatural n) a (pp.List.drop start a (ListFixed/toList m a xs))
    in fromListGE n a ys
   : ListFixed n a

let swapProof =
    \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(j : Natural)
 -> \(xs : ListFixed n a)
 -> \(prf1 : Proof/fromBool ^^"listfixed.dhall: swapProof indices > size"
       (   pp.Natural.lessThan i (SS/toNatural n)
        && pp.Natural.lessThan j (SS/toNatural n)
       )
    )
 -> \(prf2 : Proof/fromBool ^^"listfixed.dhall swapProof indices are the same"
       (pp.Natural.equal i j == False)
     )
     -- todo: simplify
 -> let mn = pp.Natural.min i j
    let mx = pp.Natural.max i j
    let ys = ListFixed/toList n a xs
    let w1 = ll.splitAt a mn ys -- pre
    let a1 = w1._1 -- pre
    let a2 = pp.List.take 1 a w1._2 -- the first one
    let a3 = pp.List.take (Natural/subtract (1 + mn) mx) a (pp.List.drop (mn + 1) a ys) -- between
    let a4 = pp.List.take 1 a (pp.List.drop mx a ys) -- the second one
    let a5 = pp.List.drop (mx + 1) a ys -- post
    in fromListGE n a (a1 # a4 # a3 # a2 # a5)
    : ListFixed n a

let unfoldr =
    \(n : Type)
 -> \(a : Type)
 -> \(s : Type)
 -> \(seed : a)
 -> \(state : s)
 -> \(f : s -> a -> { state : s, next : a })
 -> let t = { state : s, next : a, ret : List a }
    let r =
      Natural/fold
      (Natural/subtract 1 (SS/toNatural n))
      t
      ( \(z : t)
      -> let w = f z.state z.next
         in { state = w.state, next = w.next, ret = z.ret # [w.next] }
      )
      { state = state, next = seed, ret = [seed] : List a }
    in fromListGE n a r.ret
    : ListFixed n a

let iterate =
    \(n : Type)
 -> \(a : Type)
 -> \(seed : a)
 -> \(f : a -> a)
 -> unfoldr n a {} seed {=} (\(_ : {}) -> \(x : a) -> { state = {=}, next = f x })
    : ListFixed n a

let foldr1 =
    \(n : Type)
 -> \(a : Type)
 -> \(f : a -> a -> a)
 -> \(xs : ListFixed n a)
 -> List/fold
      a
      (ListFixed/tail n a xs)
      a
      f
      (ListFixed/head n a xs)
      : a

let foldMap1 =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(mappend : b -> b -> b)
 -> \(xs : ListFixed n a)
 -> ss.foldl
      a
      (ListFixed/tail n a xs)
      b
      (\(x : b) -> \(y : a) -> mappend x (f y))
      (f (ListFixed/head n a xs))
    : b

let fold =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed n a)
 -> \(list : Type)
 -> \(cons : a -> list -> list)
 -> \(nil : list)
 -> List/fold
      a
      (ListFixed/toList n a xs)
      list
      (\(x : a) -> \(z : list) -> cons x z)
      nil
      : list

let mapIndex =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : Natural -> a -> b)
 -> \(xs : ListFixed n a)
 -> let len = Natural/subtract 1 (SS/toNatural n)
    let ret = List/build
      b
      (   \(list : Type)
       -> \(cons : b -> list -> list)
       -> \(nil : list)
       -> let t1 = { _1 : Natural, _2 : list }
          let ww = List/fold
               a
               (ListFixed/toList n a xs)
               t1
               (\(x : a) -> \(z : t1) -> { _1 = z._1 + 1, _2 = cons (f (Natural/subtract z._1 len) x) z._2 })
               { _1 = 0, _2 = nil }
          in ww._2
      )
    in fromListGE n b ret
    : ListFixed n b

let unzip =
    \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(xs : ListFixed n { _1 : a, _2 : b })
 -> let z = pp.List.unzip a b (ListFixed/toList n { _1 : a, _2 : b } xs)
    in { _1 = fromListGE n a z._1
       , _2 = fromListGE n b z._2
       }
    : { _1 : ListFixed n a, _2 : ListFixed n b }

let dotProduct =
    \(n : Type)
 -> \(a : Type)
 -> \(f : sr.Type a)
 -> \(xs : ListFixed n a)
 -> \(ys : ListFixed n a)
 -> let zs = zipWith n a a a f.multiply xs ys
    in List/fold
         a
         (ListFixed/tail n a zs)
         a
         f.add
         (ListFixed/head n a zs)
   : a

let dotProductNatural = \(n : Type) -> dotProduct n Natural nn.numInstance
let dotProductInteger = \(n : Type) -> dotProduct n Integer ii.numInstance
let dotProductRational = \(n : Type) -> dotProduct n Rational r.numInstance
let dotProductNonZero = \(n : Type) -> dotProduct n NonZero nz.numInstance

let addScalarNatural =
    \(n : Type)
 -> \(x : Natural)
 -> map n Natural Natural (\(i : Natural) -> i + x)
   : ListFixed n Natural -> ListFixed n Natural

let multiplyScalarNatural =
    \(n : Type)
 -> \(x : Natural)
 -> map n Natural Natural (\(i : Natural) -> i * x)
   : ListFixed n Natural -> ListFixed n Natural

-- can use Proof/fromBool or SS/lessThan for the proof
let splitAtProof =
    \(n : Type)
 -> \(i : Type)
 -> \(a : Type)
 -> \(xs : ListFixed n a)
 -> \(prf : SS/lessThan i n)
 -> let rhs = SS/subtract i n
    let ys = ListFixed/toList n a xs
    in { _1 = ListFixed/fromList i a (defError a) ys
       , _2 = ListFixed/fromList rhs a (defError a) (pp.List.drop (NonZero/toNatural (SS/toNonZero i)) a ys)
       }
    : { _1 : ListFixed i a, _2 : ListFixed rhs a }

let negate =
    \(n : Type)
 -> map n Integer Integer Integer/negate
  : ListFixed n Integer -> ListFixed n Integer

let all =
    \(n : Type)
 -> \(a : Type)
 -> \(p : a -> Bool)
 -> \(xs : ListFixed n a)
 -> List/fold
      a
      (ListFixed/tail n a xs)
      Bool
      (\(x : a) -> \(z : Bool) -> p x && z)
      (p (ListFixed/head n a xs))
      : Bool

let ip4Proof =
    \(xs : ListFixed !!4 Natural)
 -> Proof/fromBool ^^"listfixed.dhall: ip4Proof one or more of the octets >= 256"
     (pp.List.all Natural (pp.Natural.greaterThan 256) (ListFixed/toList !!4 Natural xs))

let chunksOf =
    \(n : Type)
 -> \(step : NonZero)
 -> \(a : Type)
 -> \(xs : List a)
 -> pp.List.map
      (List a)
      (ListFixed n a)
      (fromListGE n a)
      (ll.chunksOf (SS/toNonZero n) step a xs)
      : List (ListFixed n a)
{-
let sortBy =
    \(n : Type)
 -> \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List (ListFixed n a))
 -> pp.map (ListFixed n a) (List a) (ListFixed/toList n) xs
 let x =
          Natural/fold
            (List/length a xs)
            (Accumulator a)
            (step a cmp)
            { sorted = [] : List a, rest = xs }
     in  x.sorted
     : List a
-}
let sortBy =
    \(n : Type)
 -> \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : ListFixed n a)
 -> ListFixed/fromList n a (defError a) (ss.sortBy a cmp (ListFixed/toList n a xs))
     : ListFixed n a

let test1 = assert : ListFixed/fromList !!4 Natural 99 [17,2,19,4] === ~[17,2,19,4]
let test2 = assert : ListFixed/toList !!4 Natural ~[17,2,19,4] === [17,2,19,4]
let test3 = assert : ListFixed/toList !!4 Natural (ListFixed/fromList !!4 Natural 99 [17,2,19,4]) === [17,2,19,4]
let test4 = assert : ListFixed/tail !!3 Natural ~[1,2,3] === [ 2, 3 ]
let test5 = assert : ListFixed/head !!3 Natural ~[1,2,3] === 1
let test6 = assert : compare !!3 oo.Ordering oo.compareOrdering ~[oo.EQ, oo.LT, oo.GT] ~[oo.EQ, oo.LT, oo.GT] === oo.LT
let test7 = assert : SS/fromNonZero !3 === !!3 -- this is a type so cant compare (we can now!)
let test8 = assert : SS/fromNonZero !1 === !!1
let test9 = assert : SS/toNonZero !!2 === !2
let test10 = assert : SS/toNonZero !!1 === !1
let test11 = assert : SS/toNonZero !!3 === !3
let test12 = assert : ListFixed/fromList (SS/fromNonZero !4) Natural 99 [17,2,19,4] === ~[17,2,19,4]
let test13 = assert : compare !!3 oo.Ordering oo.compareOrdering ~[oo.EQ, oo.LT, oo.GT] ~[oo.EQ, oo.LT, oo.GT] === oo.LT
--let test6 = assert : compare !!3 oo.Ordering oo.compareOrdering ~[oo.LT, oo.GT] ~[oo.LT, oo.GT] === oo.LT
let test14 = assert : ListFixed/head !!4 Natural ~[99,3,7,991] === 99
let test15 = assert : ListFixed/tail !!4 Natural ~[99,3,7,991] === [3,7,991]
let test16 = assert : ListFixed/toList !!4 Natural ~[99,3,7,991] === [99,3,7,991]
let test17 = assert : ListFixed/fromList !!4 Natural 0 [99,3,7,991] === ~[99,3,7,991]
let test18 = assert : ListFixed/fromList !!4 Natural 0 [99] === ~[99,0,0,0]
let test19 = assert : ListFixed/fromList !!4 Natural 0 [99,3,7,991,12,13] === ~[99,3,7,991]
let test20 = assert : ListFixed/fromList !!4 Natural 0 ([] : List Natural) === ~[0,0,0,0]
let test21 = assert : append !!3 !!7 Natural ~[4,5,6] ~[1,2,3,10,11,12,13] === ~[ 4, 5, 6, 1, 2, 3, 10, 11, 12, 13 ]

-- no longer requires parens around ListFixed cos using ~ instead of @ which is already used eg x @2 refers to two versions back of x
let test22 =
   let f = \(xs : ListFixed (SS/fromNonZero !4) Integer) -> \(ys : ListFixed (SS/fromNonZero !2) Natural) -> { _1 = xs, _2 = ys }
   in assert : f ~[+10,-9,+8,+8] ~[12,13] === { _1 = ~[+10,-9,+8,+8], _2 = ~[12,13] }

let test23 = assert : cons !!4 Natural 99 ~[10,12,13,15] === ~[99,10,12,13,15]
let test24 = assert : snoc !!4 Natural 99 ~[10,12,13,15] === ~[10,12,13,15,99]
let test25 = assert : cons !!4 Text "dude" ~["x","y","z","w"] === ~[ "dude", "x", "y", "z", "w" ]

let test26 = assert : zip !!3 Natural Integer ~[4,5,6] ~[-13,-99,+17] === ~[ { _1 = 4, _2 = -13 }, { _1 = 5, _2 = -99 }, { _1 = 6, _2 = +17 } ]

let test27 =
   let z = !!1
   let s = SS/add !!1
   in assert : ListFixed/fromList (s (s (s z))) Bool False [True,False] === ~[True,False,False,False]

let test28 = assert : SS/toNonZero (SS/add !!1 !!1) === !2
let test29 = assert : SS/toNonZero (SS/add !!2 !!1) === !3
let test30 = assert : SS/toNonZero (SS/add !!1 !!2) === !3
let test31 = assert : SS/toNonZero (SS/add !!5 !!3) === !8
let test32 = assert : SS/toNonZero (SS/add !!10 !!3) === !13

let test33 = assert : SS/toNonZero (SS/fromNonZero !1) === !1
let test34 = assert : SS/toNonZero (SS/fromNonZero !2) === !2
let test35 = assert : SS/toNonZero (SS/fromNonZero !3) === !3

let test36 = assert : ListFixed/head !!3 { _1 : Natural, _2 : Natural } (zip !!3 Natural Natural ~[9,10,11] ~[99,100,101])
 ===
{ _1 = 9, _2 = 99 }

let test37 = assert : zip !!3 Natural Natural ~[9,10,11] ~[99,100,101]
===
~[ { _1 = 9, _2 = 99 }, { _1 = 10, _2 = 100 }, { _1 = 11, _2 = 101 } ]

let test38 = assert : append !!3 !!4 Natural ~[9,10,11] ~[,1,99,100,101]
===
~[ 9, 10, 11, 1, 99, 100, 101 ]

let test39 = assert : ListFixed/fromList !!3 Natural 99 [1,2,3,4,5,6] === ~[ 1, 2, 3 ]

let test40 = assert : ListFixed/fromList !!3 Natural 99 [1,2,3,4] === ~[ 1, 2, 3]
let test41 = assert : ListFixed/fromList !!3 Natural 99 [1,2,3] === ~[ 1, 2, 3 ]

let test42 = assert : ListFixed/fromList !!3 Natural 99 [1,2,3,4,5] === ~[ 1, 2, 3 ]
let test43 = assert : negate !!5 ~[-12,+13,+100,-0,+0]=== ~[+12,-13,-100,-0,+0]


let test44 =
   let n1 = SS/fromNonZero !1
   let n2 = SS/fromNonZero !2
   let n3 = SS/add n1 n2
   let a1 = ListFixed/toList n1 Natural ~[132]
   let b1 = ListFixed/toList !!1 Natural ~[132]
   let a2 = ListFixed/toList n2 Natural ~[132,555]
   let b2 = ListFixed/toList !!2 Natural ~[132,555]
   let a3 = ListFixed/toList n3 Natural ~[111,132,555]
   let b3 = ListFixed/toList !!3 Natural ~[111,132,555]
   let zz1 = assert : a1 === b1
   let zz2 = assert : a2 === b2
   let zz3 = assert : a3 === b3
   let x1 = [a1,b1]
   let x2 = [a2,b2]
   let x3 = [a3,b3]
   in { a1
      , b1
      , a2
      , b2
      , a3
      , b3
      , x1
      , x2
      , x3
      }

-- using expression projection
let test45 =
   let f = \(xs : ListFixed (SS/fromNonZero !4) Integer) -> \(ys : ListFixed (SS/fromNonZero !2) Natural) -> { _1 = xs, _2 = ys }
   let test41a = assert :
     (f ~[-1,-2,-3,-4] ~[99,100]).({_2 : ListFixed !!2 Natural})
     ===
     { _2 = ~[ 99, 100 ] }
   in f

let test46 = assert : replicate !!2 Natural 1 === ~[ 1, 1 ]
let test47 = assert : replicate (SS/fromNonZero !10) Natural 7 === ~[ 7, 7, 7, 7, 7, 7, 7, 7, 7, 7 ]
let test48 = assert : replicate !!1 Integer +99 === ~[ +99 ]

let test49 = assert : getValProof !!5 Natural 0 ~[19,11,12,13,14] Prf === 19
let test50 = assert : getValProof !!5 Natural 1 ~[19,11,12,13,14] Prf === 11
let test51 = assert : getValProof !!5 Natural 2 ~[19,11,12,13,14] Prf === 12
let test52 = assert : getValProof !!5 Natural 3 ~[19,11,12,13,14] Prf === 13
let test53 = assert : getValProof !!5 Natural 4 ~[19,11,12,13,14] Prf === 14
let test54 = assert : getValProof !!1 Natural 0 ~[19] Prf === 19

let test55 = assert : uncons !!4 Natural ~[1,2,3,4] === { _1 = 1, _2 = [ 2, 3, 4 ] }
let test56 = assert : unsnoc !!4 Natural ~[1,2,3,4] === { _1 = [ 1, 2, 3 ], _2 = 4 }
let test57 = assert : uncons !!1 Natural ~[99] === { _1 = 99, _2 = [] : List Natural }
let test58 = assert : unsnoc !!1 Natural ~[99] === { _1 = [] : List Natural, _2 = 99 }

let test59 = assert : swapProof !!4 Natural 2 1 ~[100,200,300,400] Prf Prf === ~[ 100, 300, 200, 400 ]
let test60 = assert : swapProof !!4 Natural 0 1 ~[100,200,300,400] Prf Prf === ~[ 200, 100, 300, 400 ]
let test61 = assert : swapProof !!4 Natural 0 3 ~[100,200,300,400] Prf Prf === ~[ 400, 200, 300, 100 ]

let test62 = assert : reverse !!5 Natural ~[10,11,12,13,14] === ~[14,13,12,11,10]
let test63 = assert : reverse !!1 Natural ~[10] === ~[10]

let test64 = assert : mapIndex !!5 Natural { _1 : Natural, _2 : Natural } (\(i : Natural) -> \(x : Natural) -> { _1 = i, _2 = x }) ~[10,11,12,13,14]
===
~[ { _1 = 0, _2 = 10 }
  , { _1 = 1, _2 = 11 }
  , { _1 = 2, _2 = 12 }
  , { _1 = 3, _2 = 13 }
  , { _1 = 4, _2 = 14 }
  ]

let test65 = assert : splitAtProof !!8 !!7 Natural ~[1,2,3,4,5,6,7,8] Prf
===
{ _1 = ~[ 1, 2, 3, 4, 5, 6, 7 ], _2 = ~[ 8 ] }

let test66 = assert : splitAtProof !!8 !!1 Natural ~[1,2,3,4,5,6,7,8] Prf
===
{ _1 = ~[ 1 ], _2 = ~[ 2, 3, 4, 5, 6, 7, 8 ] }

let test67 = assert : splitAtProof !!8 !!3 Natural ~[1,2,3,4,5,6,7,8] Prf
===
{ _1 = ~[ 1, 2, 3 ], _2 = ~[ 4, 5, 6, 7, 8 ] }

let test68 = assert : vecNatural !!8 === ~[ 0, 1, 2, 3, 4, 5, 6, 7 ]

let test69 = assert : Proof/toBool (ip4Proof ~[1,2,3,256]) === False
let test70 = assert : Proof/toBool (ip4Proof ~[1,260,3,256]) === False
let test71 = assert : Proof/toBool (ip4Proof ~[1,2555,3,0]) === False
let test72 = assert : Proof/toBool (ip4Proof ~[255,255,255,255]) === True
let test73 = assert : Proof/toBool (ip4Proof ~[0,0,0,0]) === True

let test74 = assert : setValProof !!5 Natural 0 99 ~[19,11,12,13,14] Prf === ~[99,11,12,13,14]
let test75 = assert : setValProof !!5 Natural 4 99 ~[19,11,12,13,14] Prf === ~[19,11,12,13,99]
let test76 = assert : setValProof !!5 Natural 3 99 ~[19,11,12,99,14] Prf === ~[19,11,12,99,14]

let test77 = assert : deleteValProof !!5 Natural 3 ~[19,11,12,99,14] Prf Prf === ~[19,11,12,14]
--let test50 = assert : deleteValProof !!1 Natural 0 ~[19] Prf Prf === ~[19,11,12,14]

let test78 = assert : deleteValProof !!3 Natural 0 ~[1,19,10] Prf Prf === ~[ 19, 10 ]
let test79 = assert : deleteValProof !!2 Natural 0 ~[19,10] Prf Prf === ~[ 10 ]
let test80 = assert : deleteValProof !!2 Natural 1 ~[19,10] Prf Prf === ~[ 19 ]

-- let test50 = assert : SS/subtract !!1 !!1 === SS/subtract !!1 !!1
let test81 = assert : SS/toNonZero (SS/subtract !!1 !!2) === !1

let test82 = assert : SS/toNonZero (SS/subtract !!1 !!3) === !2

let test83 = assert : SS/toNonZero (SS/subtract !!2 !!3) === !1

-- let test50 = assert : SS/subtract !!3 !!3 === SS/subtract !!3 !!3
let test84 = assert : fold !!10 Natural (vecNatural !!10) Text (\(x : Natural) -> \(z : Text) -> Natural/show (x + 1) ++ z) "" === "12345678910"
let test85 = assert : map !!10 Natural Text (\(x : Natural) -> Natural/show (x + 1)) (vecNatural !!10) === ~["1","2","3","4","5","6","7","8","9","10"]

let test86 = assert : foldr1 !!9 Integer Integer/add ~[+10,-3,-4,+15,+7,+0,-0,+5,+5] === +35
let test87 = assert : foldMap1 !!9 Integer Text pp.Integer.show (\(x : Text) -> \(z : Text) -> x ++ z) ~[+10,-3,-4,+15,+7,+0,-0,+5,+5] === "+10-3-4+15+7+0+0+5+5"

let test88 = assert : all !!5 Natural (\(x : Natural) -> pp.Natural.greaterThanEqual x 7 && pp.Natural.lessThanEqual x 20) ~[8, 15, 12, 20, 7] === True
let test89 = assert : all !!5 Natural (\(x : Natural) -> pp.Natural.greaterThanEqual x 7 && pp.Natural.lessThanEqual x 20) ~[8, 15, 12, 20, 1] === False
let test90 = assert : all !!5 Natural (\(x : Natural) -> pp.Natural.greaterThanEqual x 7 && pp.Natural.lessThanEqual x 20) ~[21, 21, 21, 21, 21] === False

let test91 = assert : SS/toNonZero !!5 === !5
let test92 = assert : SS/toNonZero !!1 === !1
let test93 = assert : Proof/toBool (SS/equal !!5 !!5) === True
let test94 = assert : Proof/toBool (SS/equal !!1 !!1) === True
let test95 = assert : Proof/toBool (SS/equal !!4 !!5) === False
let test96 = assert : Proof/toBool (SS/equal !!6 !!5) === False

let test97 = assert : dotProductNatural !!5 ~[10,12,1,2,5] ~[3,1,4,7,100] === 560
let test98 = assert : dotProductNonZero !!5 ~[!10,!12,!1,!2,!5] ~[!3,!1,!4,!7,!100] === !560
let test99 = assert : dotProductNatural !!3 ~[10,1,0] ~[0,2,100] === 2

let test100 = assert : splitAtProof !!10 !!7 NonZero (vecNonZero !!10) Prf
===
{ _1 = ~[ !1, !2, !3, !4, !5, !6, !7 ], _2 = ~[ !8, !9, !10 ] }

let test101 = assert : splitAtProof !!10 !!4 Rational (vecRational !!10) Prf
===
{ _1 = ~[ +0 % !1, +1 % !1, +2 % !1, +3 % !1 ]
, _2 = ~[ +4 % !1, +5 % !1, +6 % !1, +7 % !1, +8 % !1, +9 % !1 ]
}
let test102 = assert : unfoldr !!5 Natural {} 10 {=} (\(_ : {}) -> \(v : Natural) -> { next = v + 1, state = {=} })
===
~[ 10,11,12,13,14 ]

let test103 = assert : iterate !!5 Natural 10 (\(v : Natural) -> v + 1)
===
~[ 10,11,12,13,14 ]

let test104 = assert : iterate !!5 NonZero !23 (NonZero/add !5) === ~[ !23, !28, !33, !38, !43 ]

let test105 = assert : fromListProof !!4 Natural [1,2,3,4] Prf
===
~[ 1, 2, 3, 4 ]

let test106 = assert : fromListProof !!4 NonZero [ !23, !28, !33, !38, !43 ] Prf
===
~[ !23, !28, !33, !38]

let test107 = assert : vecRationalN !!5 (-3 % !7) (+1 % !4)
===
~[ -3 % !7, -5 % !28, +1 % !14, +9 % !28, +4 % !7 ]

let test108 = assert : chunksOf !!2 !1 Natural [1,2,3,4,5,6,7,8,9]
===
[ ~[ 1, 2 ]
, ~[ 2, 3 ]
, ~[ 3, 4 ]
, ~[ 4, 5 ]
, ~[ 5, 6 ]
, ~[ 6, 7 ]
, ~[ 7, 8 ]
, ~[ 8, 9 ]
]

let test109 = assert : chunksOf !!4 !2 Natural [1,2,3,4,5,6,7,8,9]
===
[ ~[ 1, 2, 3, 4 ], ~[ 3, 4, 5, 6 ], ~[ 5, 6, 7, 8 ] ]

let test110 = assert : lift !!4 !!2 Natural ~[1,2,3,4] === ~[1,2]
let test111 = assert : lift !!4 !!5 Natural ~[1,2,3,4] === ~[1,2,3,4,1]
let test112 = assert : lift !!1 !!5 NonZero ~[!99] === ~[!99, !99, !99, !99, !99]

let test113 = assert : unfoldr !!5 Natural {} 10 {=} (\(_ : {}) -> \(v : Natural) -> { next = v + 1, state = {=} })
===
~[ 10,11,12,13,14 ]

let test114 = assert : substringProof !!5 !!3 Natural ~[1,2,3,4,5] 2 Prf Prf
===
~[ 3, 4, 5 ]
let test115 = assert : substringProof !!5 !!1 Natural ~[1,2,3,4,5] 4 Prf Prf
===
~[ 5 ]
let test116 = assert : substringProof !!1 !!1 Natural ~[99] 0 Prf Prf
===
~[ 99 ]
let test117 = assert : fromListGE !!5 Natural [5,3,4,5,2]
===
~[5,3,4,5,2]

in {
, replicate
, negate
, compare
, append
, zipWith
, zip
, unzip
, cons
, snoc
, reverse
, uncons
, unsnoc
, getValProof
, setValProof
, map
, mapAmp
, mapIndex
, fold
, swapProof
, splitAtProof

, vecNatural
, vecNonZero
, vecInteger
, vecRational

, vecNaturalN
, vecNonZeroN
, vecIntegerN
, vecRationalN

, dotProduct
, dotProductNatural
, dotProductInteger
, dotProductRational
, dotProductNonZero

, multiplyScalarNatural
, addScalarNatural

, ip4Proof
, deleteValProof

, foldMap1
, foldr1
, unfoldr
, iterate
, all
, defError

, chunksOf
, substringProof
, lift
, fromListExact
, fromListGE
, fromListProof
, sortBy
}

{-
> b.swapProof !4 Natural 2 1 ~[100,200,300,400] Prf Prf
~[ 100, 300, 200, 400 ]

> b.swapProof !4 Natural 2 2 ~[100,200,300,400] Prf Prf
Error: Wrong type of function argument
- PVoid ...
+ Proof ...

1| b.swapProof !4 Natural 2 2 Prf Prf

(stdin):1:1
> b.swapProof !2 Natural 2 2 ~[100,200,300,400] Prf
Error: Wrong type of function argument
- PVoid ...
+ Proof ...

1| b.swapProof !2 Natural 2 2 Prf Prf

(stdin):1:1
> b.swapProof !2 Natural 1 2 Prf ~[100,200,300,400]
Error: Wrong type of function argument

- PVoid ...
+ Proof ...

1| b.swapProof !2 Natural 1 2 Prf Prf

(stdin):1:1
>

x.lf.all !!3 Text (\(x : Text) -> Regex/match ~"^\d{3}-\d{3}-\d{4}$" x) ~["123-222-1234" , "123-111-9999", "111-123-9912"]
True

>Dhall.input (Dhall.pair (nonEmpty (Dhall.Core.NonZeroC 6) natural) (nonEmpty (Dhall.Core.NonZeroC 4) natural)) "let x = ./all.dhall in x.lf.splitAtProof !!10 !!6 Natural Prf ~[99,3,78,33,4,0,22,44,1,1]" :: IO (NonEmpty Natural, NonEmpty Natural)
(99 :| [3,78,33,4,0],22 :| [44,1,1])
it :: (NonEmpty Natural, NonEmpty Natural)
(14.69 secs, 12,302,801,768 bytes)

>Dhall.input (Dhall.pair (nonEmpty (Dhall.Core.NonZeroC 6) natural) (nonEmpty (Dhall.Core.NonZeroC 4) natural)) "let x = ./all.dhall in x.lf.splitAtProof !!10 !!6 Natural Prf ~[99,3,78,33,4,0,22,44,1,1]" :: IO (NonEmpty Natural, NonEmpty Natural)
(99 :| [3,78,33,4,0],22 :| [44,1,1])
it :: (NonEmpty Natural, NonEmpty Natural)
(22.22 secs, 11,584,172,152 bytes)
>Dhall.input (Dhall.pair (nonEmpty (Dhall.Core.NonZeroC 6) natural) (nonEmpty (Dhall.Core.NonZeroC 4) natural)) "let x = ./all.dhall in x.lf.splitAtProof !!10 !!6 Natural Prf ~[99,3,78,33,4,0,22,44,1,1]" :: IO (NonEmpty Natural, NonEmpty Natural)
(99 :| [3,78,33,4,0],22 :| [44,1,1])
it :: (NonEmpty Natural, NonEmpty Natural)
(16.48 secs, 9,396,866,304 bytes)

>Dhall.input (Dhall.pair (nonEmpty (Dhall.Core.NonZeroC 6) natural) (nonEmpty (Dhall.Core.NonZeroC 4) natural)) "let x = ./listfixed.dhall in x.splitAtProof !!10 !!6 Natural Prf ~[99,3,78,33,4,0,22,44,1,1]" :: IO (NonEmpty Natural, NonEmpty Natural)
(99 :| [3,78,33,4,0],22 :| [44,1,1])
it :: (NonEmpty Natural, NonEmpty Natural)
(4.49 secs, 3,246,632,856 bytes)

> x.lf.getValProof !!5 Natural 5 Prf ~[19,11,12,13,14]
Error: Wrong type of function argument

- PVoid
+ Proof
- Sym ^^"listfixed.dhall: getValProof index >= size"
+ Type

1| x.lf.getValProof !!5 Natural 5 Prf

(stdin):1:1
-}