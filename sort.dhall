let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall

let foldl =
   \(a : Type)
-> \(xs : List a)
-> \(b : Type)
-> \(f : b -> a -> b)
-> List/fold
    a
    xs
    (b -> b)
    (\(x : a) -> \(k : b -> b) -> \(v : b) -> k (f v x))
    (\(x : b) -> x)
    : b -> b

let Accumulator = \(a : Type) -> { sorted : List a, rest : List a }

let listMin
    =    \(a : Type)
      -> \(cmp  : a -> a -> oo.Ordering)
      -> \(xs : List a)
      -> pp.Optional.map
          a
          a
          (   \(n : a)
            -> List/fold
                 a
                 xs
                 a
                 (\(x : a) -> \(y : a) -> if oo.isLT (cmp x y) then x else y)
                 n
          )
          (List/head a xs)
          : Optional a

let partitionMinima =
         \(a : Type)
      -> \(xs : List a)
      -> \(cmp  : a -> a -> oo.Ordering)
      -> merge
          { Some =
              \(m : a) -> pp.List.partition a (\(x : a) -> oo.isGE (cmp m x)) xs
          , None = { true = [] : List a, false = [] : List a }
          }
          (listMin a cmp xs)
          : { true : List a, false : List a}

let step =
         \(a : Type)
      -> \(cmp  : a -> a -> oo.Ordering)
      -> \(x : Accumulator a)
      -> let p = partitionMinima a x.rest cmp
         in { sorted = x.sorted # p.true, rest = p.false }
         : Accumulator a

-- stable sort
let sortBy =
         \(a : Type)
      -> \(cmp  : a -> a -> oo.Ordering)
      -> \(xs : List a)
      -> let x =
              Natural/fold
                (List/length a xs)
                (Accumulator a)
                (step a cmp)
                { sorted = [] : List a, rest = xs }
         in  x.sorted
         : List a

let groupBy =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> let t = { _1 : Optional a, _2 : List a, _3 : List (List a) }
    let ws =
      List/fold
      a
      xs
      t
      (    \(x : a)
        -> \(z : t)
        -> merge { None = { _1 = Some x, _2 = [x], _3 = z._3 }
                          , Some =
                              \(w : a)
                          -> if oo.isEQ (cmp w x)
                             then { _1 = Some x, _2 = [x] # z._2, _3 = z._3 }
                             else { _1 = Some x, _2 = [x], _3 = [z._2] # z._3 }
                } z._1
      )
      { _1 = None a, _2 = [] : List a, _3 = [] : List (List a) }
   in [ws._2] # ws._3
   : List (List a)

-- uses the last value if there is a collision
let nubBy =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> List/build
      a
      (   \(list : Type)
       -> \(cons : a -> list -> list)
       -> \(nil : list)
       -> let t = { _1 : Optional a, _2 : list }
          let ws =
            List/fold
              a
              (sortBy a cmp xs)
              t
              (   \(x : a)
               -> \(z : t)
               -> { _1 = Some x
                  , _2 = merge { None = cons x z._2
                               , Some =
                                     \(w : a)
                                  -> if oo.isEQ (cmp w x)
                                     then z._2
                                     else cons x z._2
                              } z._1
                  }
              )
              { _1 = None a, _2 = nil }
          in ws._2
       )
    : List a

let multisetBy =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> let s = { _1 : a, _2 : Natural }
    in List/build
        { _1 : a, _2 : Natural }
        (   \(list : Type)
         -> \(cons : s -> list -> list)
         -> \(nil : list)
         -> let t = { _1 : Optional a, _2 : Natural, _3 : list }
            let ws =
              List/fold
                a
                (sortBy a cmp xs)
                t
                (   \(x : a)
                 -> \(z : t)
                 -> merge {
                       None = { _1 = Some x, _2 = 1, _3 = nil }
                     , Some =
                        \(w : a)
                     -> if oo.isEQ (cmp w x)
                        then { _1 = z._1, _2 = z._2 + 1, _3 = z._3 }
                        else { _1 = Some x, _2 = 1, _3 = cons { _1 = w, _2 = z._2 } z._3 }
                    } z._1
                )
                { _1 = None a, _2 = 0, _3 = nil }
            in merge {
               None = nil
             , Some = \(x : a) -> cons { _1 = x, _2 = ws._2 } ws._3
             } ws._1
         )
          : List s

let elem =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(y : a)
 -> \(xs : List a)
 -> List/fold
      a
      xs
      Bool
      (   \(x : a)
       -> \(z : Bool)
       -> if z then True else oo.isEQ (cmp x y)
      )
      False
  : Bool

let intersectBy =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> \(ys : List a)
 -> let zs = nubBy a cmp ys
    in List/build
      a
      (   \(list : Type)
       -> \(cons : a -> list -> list)
       -> \(nil : list)
       ->
      List/fold
        a
        (nubBy a cmp xs)
        list
        (   \(x : a)
         -> \(z : list)
         -> if elem a cmp x zs then cons x z else z
        )
        nil
     )
     : List a

let isNub =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> pp.Natural.equal (List/length a xs) (List/length a (nubBy a cmp xs))
 : Bool

let intersectByProof =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> \(ys : List a)
 -> \(prf1 : Proof/fromBool ^^"intersectByProof: duplicate found for xs" (isNub a cmp xs))
 -> \(prf2 : Proof/fromBool ^^"intersectByProof: duplicate found for ys" (isNub a cmp ys))
 -> intersectBy a cmp xs ys
   : List a

let unionBy =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> \(ys : List a)
 -> nubBy a cmp (xs # ys)
   : List a

let deleteBy =
    \(a : Type)
 -> \(cmp : a -> a -> oo.Ordering)
 -> \(x : a)
 -> \(xs : List a)
 -> let t = { _1 : Bool, _2 : List a }
    let ret =
      foldl
      a
      xs
      t
      (\(z : t) -> \(y : a) ->
         if z._1 then { _1 = True, _2 = z._2 # [y] }
         else if oo.isEQ (cmp x y) then { _1 = True, _2 = z._2 }
         else { _1 = False, _2 = z._2 # [y] }
      )
      { _1 = False, _2 = [] : List a }
   in ret._2
      : List a

let deleteFirstsBy =
    \(a : Type)
 -> \(cmp : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> \(ys : List a)
 -> List/fold
      a
      ys
      (List a)
      (deleteBy a cmp)
      xs
      : List a

let sortNatural = sortBy Natural oo.compareNatural
let sortInteger = sortBy Integer oo.compareInteger
let sortNonZero = sortBy NonZero oo.compareNonZero
let sortRational = sortBy Rational oo.compareRational
let sortText = sortBy Text oo.compareText
let sortTextIgnore = sortBy Text oo.compareTextIgnore
let sortDateTime = sortBy DateTime oo.compareDateTime
let sortBool = sortBy Bool oo.compareBool

let nubNatural = nubBy Natural oo.compareNatural
let nubInteger = nubBy Integer oo.compareInteger
let nubNonZero = nubBy NonZero oo.compareNonZero
let nubRational = nubBy Rational oo.compareRational
let nubText = nubBy Text oo.compareText
let nubTextIgnore = nubBy Text oo.compareTextIgnore
let nubDateTime = nubBy DateTime oo.compareDateTime
let nubBool = nubBy Bool oo.compareBool

let multisetNatural = multisetBy Natural oo.compareNatural
let multisetInteger = multisetBy Integer oo.compareInteger
let multisetNonZero = multisetBy NonZero oo.compareNonZero
let multisetRational = multisetBy Rational oo.compareRational
let multisetText = multisetBy Text oo.compareText
let multisetTextIgnore = multisetBy Text oo.compareTextIgnore
let multisetDateTime = multisetBy DateTime oo.compareDateTime
let multisetBool = multisetBy Bool oo.compareBool

let groupNatural = groupBy Natural oo.compareNatural
let groupInteger = groupBy Integer oo.compareInteger
let groupNonZero = groupBy NonZero oo.compareNonZero
let groupRational = groupBy Rational oo.compareRational
let groupText = groupBy Text oo.compareText
let groupTextIgnore = groupBy Text oo.compareTextIgnore
let groupDateTime = groupBy DateTime oo.compareDateTime
let groupBool = groupBy Bool oo.compareBool

let unionNatural = unionBy Natural oo.compareNatural
let unionInteger = unionBy Integer oo.compareInteger
let unionNonZero = unionBy NonZero oo.compareNonZero
let unionRational = unionBy Rational oo.compareRational
let unionText = unionBy Text oo.compareText
let unionTextIgnore = unionBy Text oo.compareTextIgnore
let unionDateTime = unionBy DateTime oo.compareDateTime
let unionBool = unionBy Bool oo.compareBool

let intersectNatural = intersectBy Natural oo.compareNatural
let intersectInteger = intersectBy Integer oo.compareInteger
let intersectNonZero = intersectBy NonZero oo.compareNonZero
let intersectRational = intersectBy Rational oo.compareRational
let intersectText = intersectBy Text oo.compareText
let intersectTextIgnore = intersectBy Text oo.compareTextIgnore
let intersectDateTime = intersectBy DateTime oo.compareDateTime
let intersectBool = intersectBy Bool oo.compareBool

let deleteNatural = deleteBy Natural oo.compareNatural
let deleteInteger = deleteBy Integer oo.compareInteger
let deleteNonZero = deleteBy NonZero oo.compareNonZero
let deleteRational = deleteBy Rational oo.compareRational
let deleteText = deleteBy Text oo.compareText
let deleteTextIgnore = deleteBy Text oo.compareTextIgnore
let deleteDateTime = deleteBy DateTime oo.compareDateTime
let deleteBool = deleteBy Bool oo.compareBool

let deleteFirstsNatural = deleteFirstsBy Natural oo.compareNatural
let deleteFirstsInteger = deleteFirstsBy Integer oo.compareInteger
let deleteFirstsNonZero = deleteFirstsBy NonZero oo.compareNonZero
let deleteFirstsRational = deleteFirstsBy Rational oo.compareRational
let deleteFirstsText = deleteFirstsBy Text oo.compareText
let deleteFirstsTextIgnore = deleteFirstsBy Text oo.compareTextIgnore
let deleteFirstsDateTime = deleteFirstsBy DateTime oo.compareDateTime
let deleteFirstsBool = deleteFirstsBy Bool oo.compareBool

let test1 = assert : sortNatural [5,4,3,2,1,1] === [1,1,2,3,4,5]
let test2 = assert : sortDateTime [ ^2020, ^1900, ^1901-04-12, ^1901] === [^1900, ^1901, ^1901-04-12, ^2020]
let test3 = assert : sortRational [ +5 % !3, +4 % !7, -3 % !1] === [-3 % !1, +4 % !7, +5 % !3]
let test4 = assert : sortText [ "d","a","bb","b","c","a"] === ["a","a","b","bb","c","d"]
let test5 = assert : sortNonZero [!5,!4,!3,!2,!1,!1] === [!1,!1,!2,!3,!4,!5]

let test6 = assert : nubNatural [5,4,3,2,1,1] === [1,2,3,4,5]
let test7 = assert : nubDateTime [ ^2020, ^1900, ^1901-04-12, ^1901] === [^1900, ^1901, ^1901-04-12, ^2020]
let test8 = assert : nubDateTime [ ^2020, ^1900, ^1901-04-12, ^2020, ^1900, ^1901] === [^1900, ^1901, ^1901-04-12, ^2020]
let test9 = assert : nubRational [ +5 % !3, +4 % !7, -3 % !1, +5 % !3, -5 % !3] === [-3 % !1, -5 % !3, +4 % !7, +5 % !3]
let test10 = assert : nubText [ "d","a","bb","b","c","a","d"] === ["a","b","bb","c","d"]

let test11 = assert : multisetInteger [+5,-4,+3,-2,-1,-1,+5,-4]
===
[ { _1 = -4, _2 = 2 }
, { _1 = -2, _2 = 1 }
, { _1 = -1, _2 = 2 }
, { _1 = +3, _2 = 1 }
, { _1 = +5, _2 = 2 }
]

let test12 = assert : nubRational ([] : List Rational) === ([] : List Rational)

let test13 = assert : nubNatural [1,2,3] === [1,2,3]
let test14 = assert : nubNatural ([] : List Natural) === ([] : List Natural)
let test15 = assert : nubNatural [16,1,2,3,1,1,2,4,3] === [1,2,3,4,16]
let test16 = assert : nubNatural [1,1] === [1]
let test17 = assert : nubNatural [5,3,1,2,5] === [1,2,3,5]

let test18 = assert : multisetNatural [9,10,10,10,10,9]
===
[ { _1 = 9, _2 = 2 }, { _1 = 10, _2 = 4 } ]

let test19 = assert : multisetNatural [9]
===
[ { _1 = 9, _2 = 1 } ]

let test20 = assert : multisetNatural [3,9]
===
[ { _1 = 3, _2 = 1 }, { _1 = 9, _2 = 1 } ]

let test21 = assert : multisetNatural [3,9,3]
===
[ { _1 = 3, _2 = 2 }, { _1 = 9, _2 = 1 } ]

let test22 = assert : multisetNatural [10,7,3,5]
===
[ { _1 = 3, _2 = 1 }
, { _1 = 5, _2 = 1 }
, { _1 = 7, _2 = 1 }
, { _1 = 10, _2 = 1 }
]

let test23 = assert : multisetNatural ([] : List Natural)
===
([] : List { _1 : Natural, _2 : Natural })

let test24 = assert : multisetNatural [10,10]
===
[ { _1 = 10, _2 = 2 } ]

let test25 = assert : multisetBool [True,False,True,False,False]
===
[ { _1 = False, _2 = 3 }
, { _1 = True, _2 = 2 }
]

let test26 = assert : nubBool [True,False,True,False,False]
===
[False,True]

let test27 = assert : sortBool [True,False,True,False,False]
===
[False,False,False,True,True]

let test28 = assert : sortTextIgnore ["ab","b","Ab","AB","c","b"]
===
["ab","Ab","AB","b","b","c"]

let test29 = assert : nubTextIgnore ["ab","b","Ab","AB","c","b"]
===
["AB","b","c"]

let test30 = assert : nubTextIgnore ["AB","ab","b","Ab","c","b"]
===
["Ab","b","c"]

let test31 = assert : groupTextIgnore ["AB","ab","b","Ab","c","B", "b"]
===
[ [ "AB", "ab" ], [ "b" ], [ "Ab" ], [ "c" ], [ "B", "b" ] ]

let test32 = assert : intersectNatural [1,10,12,3,1] [1,1,1] === [1]
let test33 = assert : intersectNatural [1,10,12,3,1] ([] : List Natural) === ([] : List Natural)
let test34 = assert : intersectNatural [1,10,12,3,1] [9,9,9] === ([] : List Natural)
let test35 = assert : intersectNatural [1,10,12,3,1] [3,4,5,10,12] === [3,10,12]

let test36 = assert : multisetTextIgnore ["ab","b","Ab","AB","c","b"]
===
[ { _1 = "AB", _2 = 3 }
, { _1 = "b", _2 = 2 }
, { _1 = "c", _2 = 1 }
]

let test37 = assert : isNub Text oo.compareTextIgnore ["ab","b","Ab","AB","c","b"] === False
let test38 = assert : isNub Text oo.compareTextIgnore ["ab","Ab","AB","c","b"] === False
let test39 = assert : isNub Text oo.compareText ["ab","Ab","AB","c","b"] === True

let test40 = assert : intersectByProof Natural oo.compareNatural [3,2,1] [4,5,3] Prf Prf === [3]

let test41 = assert : foldl Natural [1,2,3,4] (List Natural) (\(xs : List Natural) -> \(x : Natural) -> [x] # xs) [9999] === [4,3,2,1,9999]

let test42 = assert : deleteNatural 1 [2,3,4] === [2,3,4]
let test43 = assert : deleteNatural 1 [1,2,3,4] === [2,3,4]
let test44 = assert : deleteNatural 1 [1,1,2,1,3,4] === [1,2,1,3,4]
let test45 = assert : deleteNatural 1 [2,3,1,4,1] === [2,3,4,1]
let test46 = assert : deleteNatural 1 [1] === ([] : List Natural)
let test47 = assert : deleteNatural 1 ([] : List Natural) === ([] : List Natural)

let test48 = assert : deleteFirstsNatural [1,2,3] [1,1,2] === [3]
let test49 = assert : deleteFirstsNatural [1,2,1,3,1,5] [2,1,1] === [3,1,5]
let test50 = assert : deleteFirstsNatural [1,2,1,3,1,5] [10,11,12] === [1,2,1,3,1,5]
let test51 = assert : deleteFirstsNatural [1,2,4,1,3] [2,1] === [4,1,3]
let test52 = assert : deleteFirstsNatural [1,1] [1] === [1]
let test53 = assert : deleteFirstsNatural [1] [1] === ([] : List Natural)


in {
, sortBy
, sortNatural
, sortInteger
, sortNonZero
, sortRational
, sortText
, sortTextIgnore
, sortDateTime
, sortBool

, nubBy
, nubNatural
, nubInteger
, nubNonZero
, nubRational
, nubText
, nubTextIgnore
, nubDateTime
, nubBool

, multisetBy
, multisetNatural
, multisetInteger
, multisetNonZero
, multisetRational
, multisetText
, multisetTextIgnore
, multisetDateTime
, multisetBool

, groupBy
, groupNatural
, groupInteger
, groupNonZero
, groupRational
, groupText
, groupTextIgnore
, groupDateTime
, groupBool

, unionBy
, unionNatural
, unionInteger
, unionNonZero
, unionRational
, unionText
, unionTextIgnore
, unionDateTime
, unionBool

, intersectBy
, intersectNatural
, intersectInteger
, intersectNonZero
, intersectRational
, intersectText
, intersectTextIgnore
, intersectDateTime
, intersectBool

, deleteFirstsNatural
, deleteFirstsInteger
, deleteFirstsNonZero
, deleteFirstsRational
, deleteFirstsText
, deleteFirstsTextIgnore
, deleteFirstsDateTime
, deleteFirstsBool

, deleteNatural
, deleteInteger
, deleteNonZero
, deleteRational
, deleteText
, deleteTextIgnore
, deleteDateTime
, deleteBool

, elem
, intersectByProof
, isNub
, foldl
, deleteBy
, deleteFirstsBy
}