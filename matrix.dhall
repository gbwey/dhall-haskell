-- caused a loop? or just insanely long: this is missing the second matrix but holy crap: why so much stuff
-- exponential
-- x.m.multiply !!5 !!5 !!5 Natural (x.lf.dotProductNatural !!5) (x.m.squareNatural !!5)
-- x.m.multiply !!2 !!2 !!2 Natural (x.lf.dotProductNatural !!2) (x.m.squareNatural !!2)  -- takes a while but does finish

let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let lf = ./listfixed.dhall
let ll = ./list.dhall
let ss = ./sort.dhall
let r = ./rational.dhall
let ii = ./integer.dhall
let nn = ./natural.dhall
let nz = ./nonzero.dhall
let oo = ./ordering.dhall

let Mat =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> ListFixed m (ListFixed n a)

let map =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(xs : Mat m n a)
 -> lf.map m (ListFixed n a) (ListFixed n b)
    (lf.map n a b f) xs
    : Mat m n b

-- adds row and column
let mapIndex =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : Natural -> Natural -> a -> b)
 -> \(xs : Mat m n a)
 -> lf.mapIndex m (ListFixed n a) (ListFixed n b)
    (   \(i : Natural)
     -> \(ys : ListFixed n a)
     -> lf.mapIndex
          n
          a
          b
          (f i) -- (\(j : Natural) -> f i j)
          ys
    ) xs
    : Mat m n b

let mapIndexSimple =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(xs : Mat m n a)
 -> let t = { _1 : Natural, _2 : Natural, _3 : b }
    in lf.mapIndex m (ListFixed n a) (ListFixed n t)
    (   \(i : Natural)
     -> \(ys : ListFixed n a)
     -> lf.mapIndex
          n
          a
          t
          (\(j : Natural) -> \(x : a) -> { _1 = i, _2 = j, _3 = f x })
          ys
    ) xs
    : Mat m n t

let fromList =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(x : a)
 -> \(xs : List a)
 -> let s = ListFixed n a
    let t = { _1 : List a, _2 : List s }
    let ret =
      Natural/fold
        (SS/toNatural m)
        t
        (   \(z : t)
          -> let v = SS/toNatural n
             let lr = ll.splitAt a v z._1
             in { _1 = lr._2
                , _2 = z._2 # [ListFixed/fromList n a x lr._1]
                }
        )
        { _1 = xs, _2 = [] : List s }
    in lf.fromListGE m s ret._2
     : Mat m n a

let fromListExact =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : List a)
 -> let len = List/length a xs
    in if pp.Natural.equal (SS/toNatural (nz.ssMultiply m n)) len
    then fromList m n a (lf.defError a) xs
    else PVoid/error (Sym/fromText ("matrix.dhall: fromListExact: list length=" ++ Natural/show len ++ " is not the same as n=" ++ Natural/show (SS/toNatural n))) (Mat m n a)
 : Mat m n a

let fromListGE =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : List a)
 -> fromList m n a (lf.defError a) xs
 : Mat m n a

let fromListExactProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : List a)
 -> \(prf : Proof/fromBool ^^"matrix.dhall: fromListExact: wrong length"
       (pp.Natural.equal (SS/toNatural (nz.ssMultiply m n)) (List/length a xs))
     )
 -> fromList m n a (lf.defError a) xs
 : Mat m n a

let matNatural =
    \(m : Type)
 -> \(n : Type)
 -> fromList m n Natural (lf.defError Natural) (pp.Natural.enumerate (SS/toNatural (nz.ssMultiply m n)))
   : Mat m n Natural

let matInteger =
    \(m : Type)
 -> \(n : Type)
 -> fromList m n Integer (lf.defError Integer) (ii.enumerate (SS/toNatural (nz.ssMultiply m n)))
   : Mat m n Integer

let matNonZero =
    \(m : Type)
 -> \(n : Type)
 -> fromList m n NonZero (lf.defError NonZero) (nz.enumerate (SS/toNatural (nz.ssMultiply m n)))
   : Mat m n NonZero

let matRational =
    \(m : Type)
 -> \(n : Type)
 -> fromList m n Rational (lf.defError Rational) (r.enumerate (SS/toNatural (nz.ssMultiply m n)))
   : Mat m n Rational

let concat =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : Mat m n a)
 -> let mn = nz.ssMultiply m n
    let ret =
      ss.foldl
        (ListFixed n a)
        (ListFixed/tail m (ListFixed n a) xs)
        (List a)
        (\(z : List a) -> \(w : ListFixed n a) -> z # ListFixed/toList n a w)
        (ListFixed/toList n a (ListFixed/head m (ListFixed n a) xs))
    in lf.fromListGE mn a ret
   : ListFixed mn a

let transpose =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : Mat m n a)
 -> let t = { _1 : List (List a), _2 : List (ListFixed m a) }
    let ys =
      pp.List.map
        (ListFixed n a)
        (List a)
        (ListFixed/toList n a)
        (ListFixed/toList m (ListFixed n a) xs)
        : List (List a)
    let zs = Natural/fold
               (SS/toNatural n)
               t
               (   \(z : t)
                -> let s = { hd : List a, tl : List (List a) }
                   let inner =
                     List/fold
                       (List a)
                       z._1
                       s
                       (   \(ws : List a)
                        -> \(wss : s)
                        -> let v = ll.splitAt a 1 ws
                           in { hd = v._1 # wss.hd
                              , tl = [v._2] # wss.tl
                              }
                       )
                       { hd = [] : List a, tl = [] : List (List a) }
                   in { _1 = inner.tl, _2 = z._2 # [lf.fromListGE m a inner.hd] }
                 )
               { _1 = ys, _2 = [] : List (ListFixed m a) }

    in lf.fromListGE n (ListFixed m a) zs._2
  : Mat n m a

let multiply =
    \(m : Type)
 -> \(n : Type)
 -> \(p : Type)
 -> \(a : Type)
 -> \(f : ListFixed n a -> ListFixed n a -> a)
 -> \(xs : Mat m n a)
 -> \(ys : Mat n p a)
 -> let bs = ListFixed/toList p (ListFixed n a) (transpose n p a ys)
    let zs =
      List/fold
        (ListFixed n a)
        (ListFixed/toList m (ListFixed n a) xs : List (ListFixed n a))
        (List a)
        (   \(x0 : ListFixed n a)
         -> \(z0 : List a)
         -> let vs = List/fold
              (ListFixed n a)
              bs
              (List a)
              (   \(x1 : ListFixed n a)
               -> \(z1 : List a)
               -> [f x0 x1] # z1
              )
              ([] : List a)
            in vs # z0
        )
        ([] : List a)
    in fromList m p a (PVoid/undefined a) zs
   : Mat m p a

-- pass in all the instances + Prf that it exists and then use that info
-- to pull out the specific instance of semiring and use that!
-- need a Map of a : Type and the semiring instance
let multiplyNatural =
    \(m : Type)
 -> \(n : Type)
 -> \(p : Type)
 -> multiply m n p Natural (lf.dotProductNatural n)
  : Mat m n Natural -> Mat n p Natural -> Mat m p Natural

let multiplyInteger =
    \(m : Type)
 -> \(n : Type)
 -> \(p : Type)
 -> multiply m n p Integer (lf.dotProductInteger n)
  : Mat m n Integer -> Mat n p Integer -> Mat m p Integer

let multiplyRational =
    \(m : Type)
 -> \(n : Type)
 -> \(p : Type)
 -> multiply m n p Rational (lf.dotProductRational n)
  : Mat m n Rational -> Mat n p Rational -> Mat m p Rational

-- ok cos lists are never empty
let multiplyNonZero =
    \(m : Type)
 -> \(n : Type)
 -> \(p : Type)
 -> multiply m n p NonZero (lf.dotProductNonZero n)
  : Mat m n NonZero -> Mat n p NonZero -> Mat m p NonZero

let matFunction =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b -> c)
 -> \(xs : Mat m n a)
 -> \(ys : Mat m n b)
 -> let g = lf.zipWith n a b c f
    let zs = lf.zipWith m (ListFixed n a) (ListFixed n b) (ListFixed n c) g xs ys
    in zs
   : Mat m n c

let addNatural =
    \(m : Type)
 -> \(n : Type)
 -> \(xs : Mat m n Natural)
 -> \(ys : Mat m n Natural)
 -> matFunction m n Natural Natural Natural (\(x : Natural) -> \(y : Natural) -> x + y) xs ys
   : Mat m n Natural

let square =
    \(n : Type)
 -> \(a : Type)
 -> \(zero : a)
 -> \(one : a)
 -> let m = SS/toNatural n
    let xs = [one] # pp.List.replicate m a zero
    let ys = pp.List.concat a (pp.List.replicate m (List a) xs)
    in fromList n n a zero ys
    : Mat n n a

-- use semiring for zero and one
let squareNatural = \(n : Type) -> square n Natural 0 1
let squareInteger = \(n : Type) -> square n Integer +0 +1
let squareRational = \(n : Type) -> square n Rational r.zero r.one
-- nonzero makes no sense as zero doesnt exist
--let squareNonZero = \(n : Type) -> square n NonZero !1 !2

let swapColumnsProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(j : Natural)
 -> \(xs : Mat m n a)
 -> \(prf1 : Proof/fromBool
       ^^"matrix.dhall: swapColumnsProof: indices are greater than the size"
       (   pp.Natural.lessThan i (SS/toNatural n)
        && pp.Natural.lessThan j (SS/toNatural n)
        )
    )
 -> \(prf2 : Proof/fromBool
       ^^"matrix.dhall: swapColumnsProof: indices are the same"
       (pp.Natural.equal i j == False)
    )
 -> let a1 = transpose m n a xs
    let a2 = lf.swapProof n (ListFixed m a) i j a1 prf1 prf2
    in transpose n m a a2
    : Mat m n a

let replaceColumnProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(j : Natural)
 -> \(vec : ListFixed m a)
 -> \(xs : Mat m n a)
 -> \(prf : Proof/fromBool
       ^^"matrix.dhall: replaceColumnProof: column index j is greater than the size"
       (pp.Natural.lessThan j (SS/toNatural n)))
 -> let a1 = transpose m n a xs
    let a2 = lf.setValProof n (ListFixed m a) j vec a1 prf
    in transpose n m a a2
    : Mat m n a

let deleteColumnProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(j : Natural)
 -> \(xs : Mat m n a)
 -> \(prf1 : Proof/fromBool
       ^^"matrix.dhall: deleteColumnProof: column index j is greater than the size"
       (pp.Natural.lessThan j (SS/toNatural n)))
 -> \(prf2 : SS/lessThan !!1 n)
 -> let n0 = SS/subtract !!1 n
    let a1 = transpose m n a xs
    let a2 = lf.deleteValProof n (ListFixed m a) j a1 prf1 prf2
    in transpose n0 m a a2
    : Mat m n0 a

let getValProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(j : Natural)
 -> \(xs : Mat m n a)
 -> \(prf1 : Proof/fromBool
       ^^"matrix.dhall: getValProof: row index i is greater than the size m"
      (pp.Natural.lessThan i (SS/toNatural m)))
 -> \(prf2 : Proof/fromBool
      ^^"matrix.dhall: getValProof: column index j is greater than the size n"
      (pp.Natural.lessThan j (SS/toNatural n)))
 -> let outer = lf.getValProof m (ListFixed n a) i xs prf1
    in lf.getValProof n a j outer prf2
    : a

let setValProof =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(i : Natural)
 -> \(j : Natural)
 -> \(x : a)
 -> \(xs : Mat m n a)
 -> \(prf1 : Proof/fromBool
       ^^"matrix.dhall: setValProof: row index i greater than the size m"
       (pp.Natural.lessThan i (SS/toNatural m)))
 -> \(prf2 : Proof/fromBool
      ^^"matrix.dhall: setValProof: column index j is greater than the size n"
       (pp.Natural.lessThan j (SS/toNatural n)))
 -> let outer = lf.getValProof m (ListFixed n a) i xs prf1
    let x1 = lf.setValProof n a j x outer prf2
    in lf.setValProof m (ListFixed n a) i x1 xs prf1
    : Mat m n a

let consColumn =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(col : ListFixed m a)
 -> \(xs : Mat m n a)
 -> -- let n1 = NonZero/add !1 n -- cant do this and then SS/fromNonZero !! cos confuses the type checker
    let a1 = transpose m n a xs : Mat n m a
    let a2 = lf.cons n (ListFixed m a) col a1 : Mat (SS/add !!1 n) m a
    in transpose (SS/add !!1 n) m a a2
    : Mat m (SS/add !!1 n) a

let negate =
    \(m : Type)
 -> \(n : Type)
 -> map m n Integer Integer Integer/negate
  : Mat m n Integer -> Mat m n Integer

let fromListNested =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(defA : a)
 -> \(xs : List (List a))
 -> let defListNA = lf.replicate n a defA : ListFixed n a
    in ListFixed/fromList
         m
         (ListFixed n a)
         defListNA
         (pp.List.map (List a) (ListFixed n a) (ListFixed/fromList n a defA) xs)
   : Mat m n a

-- have to have at least as many lists and elements in each list
let fromListNestedUnsafe =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : List (List a))
 -> ListFixed/fromList
         m
         (ListFixed n a)
         (lf.defError (ListFixed n a))
         (pp.List.map (List a) (ListFixed n a) (ListFixed/fromList n a (lf.defError a)) xs)
   : Mat m n a

let toList =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(xs : Mat m n a)
 -> let ys = ListFixed/toList m (ListFixed n a) xs
    in pp.List.map (ListFixed n a) (List a) (ListFixed/toList n a) ys
 : List (List a)

let cartesianWith =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b -> c)
 -> \(xs : ListFixed m a)
 -> \(ys : ListFixed n b)
 -> let ret = ll.cartesianWith a b c f (ListFixed/toList m a xs) (ListFixed/toList n b ys)
    in fromListNestedUnsafe m n c ret
       : Mat m n c

let cartesian =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(b : Type)
 -> let t = { _1 : a, _2 : b}
    in cartesianWith m n a b t (\(x : a) -> \(y : b) -> { _1 = x, _2 = y })
       : ListFixed m a -> ListFixed n b -> Mat m n t

let genNaturalWith =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(f : Natural -> Natural -> a)
 -> cartesianWith m n Natural Natural a f (lf.vecNatural m) (lf.vecNatural n)
       : Mat m n a

let genNatural =
    \(m : Type)
 -> \(n : Type)
 -> let t = { _1 : Natural, _2 : Natural }
--    in cartesianWith m n Natural Natural t (\(x : Natural) -> \(y : Natural) -> { _1 = x, _2 = y }) (lf.vecNatural m) (lf.vecNatural n)
   in genNaturalWith m n t (\(x : Natural) -> \(y : Natural) -> { _1 = x, _2 = y })
       : Mat m n t

let fromVec =
    \(n : Type)
 -> \(a : Type)
 -> \(xs : ListFixed n a)
 -> let t = ListFixed n a
    in lf.fromListGE !!1 t [xs]
    : Mat !!1 n a

-- k has to be less than n otherwise it just returns the original list [no value add]
-- k is 1..len-1 cos we dont allow empty fixed length lists: k=0 is empty list and k=len is the original list: both add no value
let chooseProof =
     \(n : Type)
  -> \(k : Type)
  -> \(a : Type)
  -> \(xs : ListFixed n a)
  -> \(prf : SS/lessThan k n)
  -> let ret =
       pp.List.map
         (List a)
         (ListFixed k a)
         (\(zs : List a) -> lf.fromListGE k a zs)
         (List/choose a (SS/toNatural k) (ListFixed/toList n a xs))
--     let n0 = SS/fromNonZero (NonZero/clamp (nn.chooseFast (SS/toNatural n) (SS/toNatural k)))
     let n0 = SS/fromNonZero (NonZero/clamp (List/length (ListFixed k a) ret))
     in lf.fromListGE n0 (ListFixed k a) ret
  : Mat n0 k a

let permutations =
     \(n : Type)
  -> \(a : Type)
  -> \(xs : ListFixed n a)
  -> let ret =
       pp.List.map
         (List a)
         (ListFixed n a)
         (lf.fromListGE n a)
         (List/permutations a (ListFixed/toList n a xs))
     let n0 = SS/fromNonZero (nz.fac (SS/toNonZero n))
     in lf.fromListGE n0 (ListFixed n a) ret
  : Mat n0 n a

let sortBy =
    \(m : Type)
 -> \(n : Type)
 -> \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : Mat m n a)
 -> fromListNestedUnsafe m n a (ll.sortBy a cmp (toList m n a xs))
     : Mat m n a

let i25 = fromList !!2 !!5 Integer +99 [-3,-15,-7,+12,+1,+2,+3,+4,+5,+0]
let i51 = fromList !!5 !!1 Integer +99 [+1,+3,-1,+12,+3]
let i13 = fromList !!1 !!3 Integer +99 [+10,-11,-12]
let i32 = fromList !!3 !!2 Integer +99 [-3,-2,-1,+0,+1,+2]

let n34 = fromList !!3 !!4 Natural 99 [1,2,3,4,5,6,7,8,9,10,11,12,13,14]
let n42 = fromList !!4 !!2 Natural 99 [10,12,13,15,17,19,21,22]
let n32 = multiplyNatural !!3 !!4 !!2 n34 n42
let n23 = fromList !!2 !!3 Natural 99 [7,8,9,10,11,12]

let n32a = ~[ ~[1,2], ~[3,4], ~[5,6] ]
let n32b = ~[ ~[7,8], ~[9,10], ~[11,12] ]

let test1 = assert : fromList !!3 !!4 Natural 99 [1] ===
~[ ~[ 1, 99, 99, 99 ], ~[ 99, 99, 99, 99 ], ~[ 99, 99, 99, 99 ] ]

let test2 = assert : fromList !!3 !!4 Natural 99 [1,2,3,4,5,6,7,8,9] ===
~[ ~[ 1, 2, 3, 4 ], ~[ 5, 6, 7, 8 ], ~[ 9, 99, 99, 99 ] ]

let test3 = assert : fromList !!3 !!4 Natural 99 [1,2,3,4,5,6,7,8,9,10,11,12,13] ===
~[ ~[ 1, 2, 3, 4 ], ~[ 5, 6, 7, 8 ], ~[ 9, 10, 11, 12 ] ]

let test4 = assert : fromList !!3 !!4 Natural 99 [1,2,3,4,5,6,7,8,9,10,11,12,13,14] ===
~[ ~[ 1, 2, 3, 4 ], ~[ 5, 6, 7, 8 ], ~[ 9, 10, 11, 12 ] ]

let test5 = assert : transpose !!3 !!4 Natural (fromList !!3 !!4 Natural 99 [1,2,3,4,5,6,7,8,9,10,11,12,13,14]) ===
~[ ~[ 1, 5, 9 ], ~[ 2, 6, 10 ], ~[ 3, 7, 11 ], ~[ 4, 8, 12 ] ]

let test6 = assert : multiplyNatural !!3 !!4 !!2 n34 n42 === ~[ ~[ 171, 187 ], ~[ 415, 459 ], ~[ 659, 731 ] ]

let test7 = assert : multiplyInteger !!2 !!5 !!1 i25 i51 === ~[ ~[ +106 ], ~[ +67 ] ]

let test8 = assert : squareNatural !!4
 ===
~[ ~[ 1, 0, 0, 0 ], ~[ 0, 1, 0, 0 ], ~[ 0, 0, 1, 0 ], ~[ 0, 0, 0, 1 ] ]

let test9 = assert : squareNatural !!1
 ===
~[ ~[ 1 ] ]

let test10 = assert : square !!4 Text "zero" "one"
 ===
~[ ~[ "one", "zero", "zero", "zero" ], ~[ "zero", "one", "zero", "zero" ], ~[ "zero", "zero", "one", "zero" ], ~[ "zero", "zero", "zero", "one" ] ]

let test11 = assert : addNatural !!3 !!2 n32a n32b
=== ~[ ~[ 8, 10 ], ~[ 12, 14 ], ~[ 16, 18 ] ]

let test12 = assert : swapColumnsProof !!3 !!4 Natural 3 1 n34 Prf Prf
===
~[ ~[ 1, 4, 3, 2 ], ~[ 5, 8, 7, 6 ], ~[ 9, 12, 11, 10 ] ]

let test13 = assert : swapColumnsProof !!3 !!4 Natural 1 3 n34 Prf Prf
===
~[ ~[ 1, 4, 3, 2 ], ~[ 5, 8, 7, 6 ], ~[ 9, 12, 11, 10 ] ]

let test14 = assert : lf.swapProof !!4 (ListFixed !!2 Natural) 1 3 n42 Prf Prf
===
~[ ~[ 10, 12 ], ~[ 21, 22 ], ~[ 17, 19 ], ~[ 13, 15 ] ]

let test15 = assert : getValProof !!4 !!2 Natural 2 1 n42 Prf Prf === 19
let test16 = assert : getValProof !!4 !!2 Natural 2 0 n42 Prf Prf === 17
let test17 = assert : getValProof !!4 !!2 Natural 0 0 n42 Prf Prf === 10
let test18 = assert : getValProof !!4 !!2 Natural 3 0 n42 Prf Prf === 21

let test19 = assert : matNatural !!4 !!5
===
~[ ~[ 0, 1, 2, 3, 4 ]
  , ~[ 5, 6, 7, 8, 9 ]
  , ~[ 10, 11, 12, 13, 14 ]
  , ~[ 15, 16, 17, 18, 19 ]
  ]

let test20 = assert : map !!4 !!3 Natural Natural (\(x : Natural) -> x + 1) (matNatural !!4 !!3)
===
~[ ~[ 1, 2, 3 ], ~[ 4, 5, 6 ], ~[ 7, 8, 9 ], ~[ 10, 11, 12 ] ]

let test21 = assert : mapIndex !!4 !!3 Natural { _1 : Natural, _2 : Natural, _3 : Natural }  (\(i : Natural) -> \(j : Natural) -> \(x : Natural) -> { _1 = i, _2 = j, _3 = x }) (matNatural !!4 !!3)
===
~[ ~[ { _1 = 0, _2 = 0, _3 = 0 }
      , { _1 = 0, _2 = 1, _3 = 1 }
      , { _1 = 0, _2 = 2, _3 = 2 }
      ]
  , ~[ { _1 = 1, _2 = 0, _3 = 3 }
      , { _1 = 1, _2 = 1, _3 = 4 }
      , { _1 = 1, _2 = 2, _3 = 5 }
      ]
  , ~[ { _1 = 2, _2 = 0, _3 = 6 }
      , { _1 = 2, _2 = 1, _3 = 7 }
      , { _1 = 2, _2 = 2, _3 = 8 }
      ]
  , ~[ { _1 = 3, _2 = 0, _3 = 9 }
      , { _1 = 3, _2 = 1, _3 = 10 }
      , { _1 = 3, _2 = 2, _3 = 11 }
      ]
  ]

let test22 = assert : getValProof !!4 !!5 Natural 1 0 (matNatural !!4 !!5) Prf Prf === 5

let test23 = assert : mapIndexSimple !!4 !!3 Natural Integer Natural/toInteger (matNatural !!4 !!3)
===
~[ ~[ { _1 = 0, _2 = 0, _3 = +0 }
      , { _1 = 0, _2 = 1, _3 = +1 }
      , { _1 = 0, _2 = 2, _3 = +2 }
      ]
  , ~[ { _1 = 1, _2 = 0, _3 = +3 }
      , { _1 = 1, _2 = 1, _3 = +4 }
      , { _1 = 1, _2 = 2, _3 = +5 }
      ]
  , ~[ { _1 = 2, _2 = 0, _3 = +6 }
      , { _1 = 2, _2 = 1, _3 = +7 }
      , { _1 = 2, _2 = 2, _3 = +8 }
      ]
  , ~[ { _1 = 3, _2 = 0, _3 = +9 }
      , { _1 = 3, _2 = 1, _3 = +10 }
      , { _1 = 3, _2 = 2, _3 = +11 }
      ]
  ]

let test24 = assert : setValProof !!4 !!2 Natural 2 1 99 n42 Prf Prf
===
~[ ~[ 10, 12 ], ~[ 13, 15 ], ~[ 17, 99 ], ~[ 21, 22 ] ]

--let test14 = assert : setValProof !!4 !!2 Natural 2 1 99 n42 Prf Prf  -- fails

let test25 = assert : deleteColumnProof !!4 !!2 Natural 1 n42 Prf Prf
===
~[ ~[ 10 ], ~[ 13 ], ~[ 17 ], ~[ 21 ] ]

let test26 = assert : deleteColumnProof !!4 !!2 Natural 0 n42 Prf Prf
===
~[ ~[ 12 ], ~[ 15 ], ~[ 19 ], ~[ 22 ] ]

let test27 = assert : deleteColumnProof !!3 !!4 Natural 1 n34 Prf Prf
===
~[ ~[ 1, 3, 4 ], ~[ 5, 7, 8 ], ~[ 9, 11, 12 ] ]

let test28 = assert : deleteColumnProof !!3 !!4 Natural 3 n34 Prf Prf
===
~[ ~[ 1, 2, 3 ], ~[ 5, 6, 7 ], ~[ 9, 10, 11 ] ]

let test29 = assert : multiply !!5 !!5 !!5 Natural (lf.dotProductNatural !!5) (squareNatural !!5) (squareNatural !!5)
===
~[ ~[ 1, 0, 0, 0, 0 ]
  , ~[ 0, 1, 0, 0, 0 ]
  , ~[ 0, 0, 1, 0, 0 ]
  , ~[ 0, 0, 0, 1, 0 ]
  , ~[ 0, 0, 0, 0, 1 ]
  ]

let test30 = assert : multiplyNatural !!5 !!5 !!5 (square !!5 Natural 0 4) (square !!5 Natural 0 7)
===
~[ ~[ 28, 0, 0, 0, 0 ]
  , ~[ 0, 28, 0, 0, 0 ]
  , ~[ 0, 0, 28, 0, 0 ]
  , ~[ 0, 0, 0, 28, 0 ]
  , ~[ 0, 0, 0, 0, 28 ]
  ]

let test31 = assert : matInteger !!4 !!5
===
~[ ~[ +0, +1, +2, +3, +4 ]
  , ~[ +5, +6, +7, +8, +9 ]
  , ~[ +10, +11, +12, +13, +14 ]
  , ~[ +15, +16, +17, +18, +19 ]
  ]

let test32 = assert : matInteger !!3 !!5
===
~[ ~[ +0, +1, +2, +3, +4 ]
  , ~[ +5, +6, +7, +8, +9 ]
  , ~[ +10, +11, +12, +13, +14 ]
  ]

let test33 = assert : matRational !!5 !!1
===
~[ ~[ +0 % !1 ], ~[ +1 % !1 ], ~[ +2 % !1 ], ~[ +3 % !1 ], ~[ +4 % !1 ] ]

let test34 = assert : matRational !!5 !!3
===
~[ ~[ +0 % !1, +1 % !1, +2 % !1 ]
  , ~[ +3 % !1, +4 % !1, +5 % !1 ]
  , ~[ +6 % !1, +7 % !1, +8 % !1 ]
  , ~[ +9 % !1, +10 % !1, +11 % !1 ]
  , ~[ +12 % !1, +13 % !1, +14 % !1 ]
  ]

let test35 = assert : multiplyRational !!5 !!4 !!6 (matRational !!5 !!4) (matRational !!4 !!6)
===
~[ ~[ +84 % !1, +90 % !1, +96 % !1, +102 % !1, +108 % !1, +114 % !1 ]
  , ~[ +228 % !1, +250 % !1, +272 % !1, +294 % !1, +316 % !1, +338 % !1 ]
  , ~[ +372 % !1, +410 % !1, +448 % !1, +486 % !1, +524 % !1, +562 % !1 ]
  , ~[ +516 % !1, +570 % !1, +624 % !1, +678 % !1, +732 % !1, +786 % !1 ]
  , ~[ +660 % !1, +730 % !1, +800 % !1, +870 % !1, +940 % !1, +1010 % !1 ]
  ]

let test36 = assert : cartesian !!4 !!3 Integer Natural ~[-0,-1,-2,-3] ~[10,20,30]
===
~[ ~[ { _1 = +0, _2 = 10 }, { _1 = +0, _2 = 20 }, { _1 = +0, _2 = 30 } ]
  , ~[ { _1 = -1, _2 = 10 }, { _1 = -1, _2 = 20 }, { _1 = -1, _2 = 30 } ]
  , ~[ { _1 = -2, _2 = 10 }, { _1 = -2, _2 = 20 }, { _1 = -2, _2 = 30 } ]
  , ~[ { _1 = -3, _2 = 10 }, { _1 = -3, _2 = 20 }, { _1 = -3, _2 = 30 } ]
  ]

let test37 = assert : cartesianWith !!4 !!3 Integer NonZero Rational (\(a : Integer) -> \(b : NonZero) -> a % b) ~[-0,-1,-2,-3] ~[!10,!20,!30]
===
~[ ~[ +0 % !1, +0 % !1, +0 % !1 ]
  , ~[ -1 % !10, -1 % !20, -1 % !30 ]
  , ~[ -1 % !5, -1 % !10, -1 % !15 ]
  , ~[ -3 % !10, -3 % !20, -1 % !10 ]
  ]

let test38 = assert : fromListNested !!3 !!4 Natural 999 ([] : List (List Natural))
===
~[ ~[ 999, 999, 999, 999 ]
  , ~[ 999, 999, 999, 999 ]
  , ~[ 999, 999, 999, 999 ]
  ]

let test39 = assert : fromListNested !!3 !!4 Natural 999 [[1,2,3,4],[5,6,7,8]]
===
~[ ~[ 1, 2, 3, 4 ]
  , ~[ 5, 6, 7, 8 ]
  , ~[ 999, 999, 999, 999 ]
  ]

let test40 = assert : transpose !!3 !!4 NonZero ~[ ~[ !3, !5, !9, !1 ], ~[ !5, !6, !7, !8 ], ~[ !9, !10, !11, !12 ] ]
===
~[ ~[ !3, !5, !9 ], ~[ !5, !6, !10 ], ~[ !9, !7, !11 ], ~[ !1, !8, !12 ] ]

let test41 = assert : cartesianWith !!7 !!4 Integer NonZero Rational r.make (lf.vecInteger !!7) (lf.vecNonZero !!4)
===
~[ ~[ +0 % !1, +0 % !1, +0 % !1, +0 % !1 ]
  , ~[ +1 % !1, +1 % !2, +1 % !3, +1 % !4 ]
  , ~[ +2 % !1, +1 % !1, +2 % !3, +1 % !2 ]
  , ~[ +3 % !1, +3 % !2, +1 % !1, +3 % !4 ]
  , ~[ +4 % !1, +2 % !1, +4 % !3, +1 % !1 ]
  , ~[ +5 % !1, +5 % !2, +5 % !3, +5 % !4 ]
  , ~[ +6 % !1, +3 % !1, +2 % !1, +3 % !2 ]
  ]

let test42 = assert : transpose !!1 !!1 Natural ~[~[123]]
===
~[ ~[ 123 ] ]
let test43 = assert : genNatural !!3 !!5
===
~[ ~[ { _1 = 0, _2 = 0 }
      , { _1 = 0, _2 = 1 }
      , { _1 = 0, _2 = 2 }
      , { _1 = 0, _2 = 3 }
      , { _1 = 0, _2 = 4 }
      ]
  , ~[ { _1 = 1, _2 = 0 }
      , { _1 = 1, _2 = 1 }
      , { _1 = 1, _2 = 2 }
      , { _1 = 1, _2 = 3 }
      , { _1 = 1, _2 = 4 }
      ]
  , ~[ { _1 = 2, _2 = 0 }
      , { _1 = 2, _2 = 1 }
      , { _1 = 2, _2 = 2 }
      , { _1 = 2, _2 = 3 }
      , { _1 = 2, _2 = 4 }
      ]
  ]

let test44 = assert : cartesian !!5 !!3 Integer NonZero (lf.vecInteger !!5) (lf.vecNonZero !!3)
===
~[ ~[ { _1 = +0, _2 = !1 }, { _1 = +0, _2 = !2 }, { _1 = +0, _2 = !3 } ]
  , ~[ { _1 = +1, _2 = !1 }, { _1 = +1, _2 = !2 }, { _1 = +1, _2 = !3 } ]
  , ~[ { _1 = +2, _2 = !1 }, { _1 = +2, _2 = !2 }, { _1 = +2, _2 = !3 } ]
  , ~[ { _1 = +3, _2 = !1 }, { _1 = +3, _2 = !2 }, { _1 = +3, _2 = !3 } ]
  , ~[ { _1 = +4, _2 = !1 }, { _1 = +4, _2 = !2 }, { _1 = +4, _2 = !3 } ]
  ]

let test45 = assert : permutations !!3 NonZero ~[!3, !5, !7]
===
~[ ~[ !3, !5, !7 ]
  , ~[ !3, !7, !5 ]
  , ~[ !5, !3, !7 ]
  , ~[ !5, !7, !3 ]
  , ~[ !7, !3, !5 ]
  , ~[ !7, !5, !3 ]
  ]

let test46 = assert : chooseProof !!5 !!2 NonZero ~[!3, !5, !7, !2, !8] Prf
===
~[ ~[ !3, !5 ]
   , ~[ !3, !7 ]
   , ~[ !3, !2 ]
   , ~[ !3, !8 ]
   , ~[ !5, !7 ]
   , ~[ !5, !2 ]
   , ~[ !5, !8 ]
   , ~[ !7, !2 ]
   , ~[ !7, !8 ]
   , ~[ !2, !8 ]
   ]

let test47 = assert : chooseProof !!4 !!2 NonZero ~[!3, !5, !7, !3] Prf
===
~[ ~[ !3, !5 ]
  , ~[ !3, !7 ]
  , ~[ !3, !3 ]
  , ~[ !5, !7 ]
  , ~[ !5, !3 ]
  , ~[ !7, !3 ]
  ]

let test48 = assert : chooseProof !!4 !!2 Integer ~[+1,+3,+5,-7] Prf
===
~[ ~[ +1, +3 ]
, ~[ +1, +5 ]
, ~[ +1, -7 ]
, ~[ +3, +5 ]
, ~[ +3, -7 ]
, ~[ +5, -7 ]
]

let test49 = assert : permutations !!3 Integer ~[+1,+3,+5]
===
~[ ~[ +1, +3, +5 ]
, ~[ +1, +5, +3 ]
, ~[ +3, +1, +5 ]
, ~[ +3, +5, +1 ]
, ~[ +5, +1, +3 ]
, ~[ +5, +3, +1 ]
]

let test50 = assert : permutations !!4 Text ~["x","a","x","b"]
===
~[ ~[ "x", "a", "x", "b" ]
   , ~[ "x", "a", "b", "x" ]
   , ~[ "x", "x", "a", "b" ]
   , ~[ "x", "x", "b", "a" ]
   , ~[ "x", "b", "a", "x" ]
   , ~[ "x", "b", "x", "a" ]
   , ~[ "a", "x", "x", "b" ]
   , ~[ "a", "x", "b", "x" ]
   , ~[ "a", "x", "x", "b" ]
   , ~[ "a", "x", "b", "x" ]
   , ~[ "a", "b", "x", "x" ]
   , ~[ "a", "b", "x", "x" ]
   , ~[ "x", "x", "a", "b" ]
   , ~[ "x", "x", "b", "a" ]
   , ~[ "x", "a", "x", "b" ]
   , ~[ "x", "a", "b", "x" ]
   , ~[ "x", "b", "x", "a" ]
   , ~[ "x", "b", "a", "x" ]
   , ~[ "b", "x", "a", "x" ]
   , ~[ "b", "x", "x", "a" ]
   , ~[ "b", "a", "x", "x" ]
   , ~[ "b", "a", "x", "x" ]
   , ~[ "b", "x", "x", "a" ]
   , ~[ "b", "x", "a", "x" ]
   ]

let test51 = assert : concat !!6 !!2 Integer (
~[ ~[ +1, +3 ]
, ~[ +1, +5 ]
, ~[ +1, -7 ]
, ~[ +3, +5 ]
, ~[ +3, -7 ]
, ~[ +5, -7 ]
]) === ~[ +1, +3, +1, +5, +1, -7, +3, +5, +3, -7, +5, -7 ]

let test52 = assert : fromVec !!12 Integer ~[ +1, +3, +1, +5, +1, -7, +3, +5, +3, -7, +5, -7 ]
=== ~[~[ +1, +3, +1, +5, +1, -7, +3, +5, +3, -7, +5, -7]]

let test53 = assert : fromListExact !!3 !!4 Natural [1,2,3,4,5,6,7,8,9,10,11,12]
===
~[ ~[ 1, 2, 3, 4 ], ~[ 5, 6, 7, 8 ], ~[ 9, 10, 11, 12 ] ]

let test54 = assert : fromListExactProof !!3 !!4 Natural [1,2,3,4,5,6,7,8,9,10,11,12] Prf
===
~[ ~[ 1, 2, 3, 4 ], ~[ 5, 6, 7, 8 ], ~[ 9, 10, 11, 12 ] ]

let test55 =
  let xs = permutations !!4 Natural (lf.vecNatural !!4)
  in assert : sortBy !!24 !!4 Natural nn.compare xs === xs

in {
, Mat
, fromList
, fromListGE
, fromListExact
, fromListExactProof
, genNaturalWith
, genNatural
, cartesianWith
, cartesian
, fromListNested
, fromListNestedUnsafe
, toList
, fromVec
, matNatural
, matInteger
, matNonZero
, matRational
, transpose
, concat
, negate
, multiply
, multiplyNatural
, multiplyInteger
, multiplyRational
, multiplyNonZero
, square
, squareNatural
, squareInteger
, squareRational
, matFunction
, addNatural
, swapColumnsProof
, consColumn
, replaceColumnProof
, deleteColumnProof
, map
, mapIndex
, mapIndexSimple
, getValProof
, setValProof
, n34
, n42
, n32
, n32a
, n32b
, n23
, i25
, i51
, i13
, i32
, permutations
, chooseProof
, sortBy
}

{-
a.matNatural !!4 !!5

~[ ~[ 0, 1, 2, 3, 4 ]
  , ~[ 5, 6, 7, 8, 9 ]
  , ~[ 10, 11, 12, 13, 14 ]
  , ~[ 15, 16, 17, 18, 19 ]
  ]

x.fromList.mapIndex !!4 !!3 Natural { _1 : Natural, _2 : Natural, _3 : Natural }  (\(i : Natural) -> \(j : Natural) -> \(y : Natural) -> { _1 = i, _2 = j, _3 = x }) (x.fromList.matNatural !!4 !!3)

~[ ~[ { _1 = 0, _2 = 0, _3 = 0 }
      , { _1 = 0, _2 = 1, _3 = 1 }
      , { _1 = 0, _2 = 2, _3 = 2 }
      ]
  , ~[ { _1 = 1, _2 = 0, _3 = 3 }
      , { _1 = 1, _2 = 1, _3 = 4 }
      , { _1 = 1, _2 = 2, _3 = 5 }
      ]
  , ~[ { _1 = 2, _2 = 0, _3 = 6 }
      , { _1 = 2, _2 = 1, _3 = 7 }
      , { _1 = 2, _2 = 2, _3 = 8 }
      ]
  , ~[ { _1 = 3, _2 = 0, _3 = 9 }
      , { _1 = 3, _2 = 1, _3 = 10 }
      , { _1 = 3, _2 = 2, _3 = 11 }
      ]
  ]

x.fromList.mapIndex !!4 !!3 Natural (List Natural)  (\(i : Natural) -> \(j : Natural) -> \(y : Natural) -> [i,j,x]) (x.fromList.matNatural !!4 !!3)

~[ ~[ [ 0, 0, 0 ], [ 0, 1, 1 ], [ 0, 2, 2 ] ]
  , ~[ [ 1, 0, 3 ], [ 1, 1, 4 ], [ 1, 2, 5 ] ]
  , ~[ [ 2, 0, 6 ], [ 2, 1, 7 ], [ 2, 2, 8 ] ]
  , ~[ [ 3, 0, 9 ], [ 3, 1, 10 ], [ 3, 2, 11 ] ]
  ]

x.fromList.mapIndex !!4 !!3 Natural (ListFixed !!3 Natural)  (\(i : Natural) -> \(j : Natural) -> \(y : Natural) -> ListFixed/fromList !!3 Natural 999 [i,j,y]) (x.fromList.matNatural !!4 !!3)

~[ ~[ ~[ 0, 0, 0 ], ~[ 0, 1, 1 ], ~[ 0, 2, 2 ] ]
  , ~[ ~[ 1, 0, 3 ], ~[ 1, 1, 4 ], ~[ 1, 2, 5 ] ]
  , ~[ ~[ 2, 0, 6 ], ~[ 2, 1, 7 ], ~[ 2, 2, 8 ] ]
  , ~[ ~[ 3, 0, 9 ], ~[ 3, 1, 10 ], ~[ 3, 2, 11 ] ]
  ]

> x.m.setValProof !!4 !!5 NonZero 3 4 !999 (x.m.matNonZero !!4 !!5) Prf Prf

~[ ~[ !1, !2, !3, !4, !5 ]
  , ~[ !6, !7, !8, !9, !10 ]
  , ~[ !11, !12, !13, !14, !15 ]
  , ~[ !16, !17, !18, !19, !999 ]
  ]

> x.m.setValProof !!4 !!5 NonZero 3 5 !999 (x.m.matNonZero !!4 !!5) Prf Prf

Error: Wrong type of function argument

- PVoid
+ Proof
- ^^"matrix.dhall: setValProof: column index j is greater than the size n"
+ Type

1| x.m.setValProof !!4 !!5 NonZero 3 5 !999 (x.m.matNonZero !!4 !!5) Prf Prf

(stdin):1:1

> x.m.swapColumnsProof !!4 !!5 NonZero 3 4 (x.m.matNonZero !!4 !!5) Prf Prf

~[ ~[ !1, !2, !3, !5, !4 ]
  , ~[ !6, !7, !8, !10, !9 ]
  , ~[ !11, !12, !13, !15, !14 ]
  , ~[ !16, !17, !18, !20, !19 ]
  ]

> x.m.swapColumnsProof !!4 !!5 NonZero 3 3 (x.m.matNonZero !!4 !!5) Prf Prf

Error: Wrong type of function argument

- PVoid
+ Proof
- ^^"matrix.dhall: swapColumnsProof: indices are the same"
+ Type

1| x.m.swapColumnsProof !!4 !!5 NonZero 3 3 (x.m.matNonZero !!4 !!5) Prf Prf

(stdin):1:1
> x.m.swapColumnsProof !!4 !!5 NonZero 3 5 (x.m.matNonZero !!4 !!5) Prf Prf

Error: Wrong type of function argument

- PVoid
+ Proof
- ^^"matrix.dhall: swapColumnsProof: indices are not less than the size"
+ Type

1| x.m.swapColumnsProof !!4 !!5 NonZero 3 5 (x.m.matNonZero !!4 !!5) Prf

(stdin):1:1

-}
