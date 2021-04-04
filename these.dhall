-- add tests
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let ll = ./list.dhall
let oo = ./ordering.dhall
let tp = ./tuple.dhall
{-
let TheseCopy :
     forall (a : Type)
  -> forall (b : Type)
  -> Type -- < This : a | That : b | These : { _1 : a, _2 : b } > [[this is key: has to be Type]] else fails
  = \(a : Type)
  -> \(b : Type)
  -> < This : a | That : b | These : {_1 : a, _2 : b } >
-}
let These =
     \(a : Type)
  -> \(b : Type)
  -> < This : a | That : b | These : {_1 : a, _2 : b } >

let def =
   \(a : Type)
-> \(b: Type)
-> \(b1 : Bool)
-> \(b2 : Bool)
-> \(b3 : Bool)
->  { This = \(_ : a) -> b1
           , That = \(_ : b) -> b2
           , These = \(z : {_1 : a, _2 : b }) -> b3
           }

let mkThis =
     \(a : Type)
  -> \(b : Type)
  -> \(x : a)
  -> (These a b).This x

let mkThat =
     \(a : Type)
  -> \(b : Type)
  -> \(y : b)
  -> (These a b).That y

let mkThese =
     \(a : Type)
  -> \(b : Type)
  -> \(x : a)
  -> \(y : b)
  -> (These a b).These { _1 = x, _2 = y }

let fromTheseWith =
     \(a : Type)
  -> \(b : Type)
  -> \(c : Type)
  -> \(th : These a b)
  -> \(aDef : a)
  -> \(bDef : b)
  -> \(f : a -> b -> c)
  -> merge { This = \(x : a) -> f x bDef
           , That = f aDef
           , These = \(z : {_1 : a, _2 : b }) -> f z._1 z._2
           } th
  : c

let these =
     \(a : Type)
  -> \(b : Type)
  -> \(c : Type)
  -> \(th : These a b)
  -> \(f1 : a -> c)
  -> \(f2 : b -> c)
  -> \(f3 : a -> b -> c)
  -> merge { This = \(x : a) -> f1 x
           , That = \(y : b) -> f2 y
           , These = \(z : {_1 : a, _2 : b }) -> f3 z._1 z._2
           } th
  : c

let mergeTheseWith =
     \(a : Type)
  -> \(b : Type)
  -> \(c : Type)
  -> \(th : These a b)
  -> \(f1 : a -> c)
  -> \(f2 : b -> c)
  -> \(f3 : c -> c -> c)
  -> merge { This = \(x : a) -> f1 x
           , That = \(y : b) -> f2 y
           , These = \(z : {_1 : a, _2 : b }) -> f3 (f1 z._1) (f2 z._2)
           } th
  : c

{-
let mergeTheseCopy =
     \(a : Type)
  -> \(th : These a a)
  -> \(f : a -> a -> a)
  -> mergeTheseWith a a a th (pp.Function.identity a) (pp.Function.identity a) f
     : a
-}

let mergeThese =
     \(a : Type)
  -> \(th : These a a)
  -> \(f : a -> a -> a)
  -> merge { This = \(x : a) -> x
           , That = \(y : a) -> y
           , These = \(z : {_1 : a,  _2 : a }) -> f z._1 z._2
           } th
           : a

let isThis =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> merge (def a b True False False) th
           : Bool

let isThat =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> merge (def a b False True False) th
           : Bool

let isThese =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> merge (def a b False False True) th
           : Bool
{-
let theseCopy =
     \(a : Type)
  -> \(b : Type)
  -> \(x : a)
  -> \(y : b)
  -> < This : a | That : b | These : { _1 : a, _2 : b } >.These { _1 = x, _2 = y }
-}
let partitionThis =
     \(a : Type)
  -> \(b : Type)
  -> \(ths : List (These a b))
  -> List/fold
       (These a b)
       ths
       (List a)
       (    \(th : These a b)
         -> \(lst : List a)
         -> merge { This = \(x : a) -> [x] # lst
                  , That = \(_ : b) -> lst
                  , These = \(_ : { _1 : a, _2 : b }) -> lst
                  } th
       )
       ([] : List a)

let partitionThat =
     \(a : Type)
  -> \(b : Type)
  -> \(ths : List (These a b))
  -> List/fold
       (These a b)
       ths
       (List b)
       (    \(th : These a b)
         -> \(lst : List b)
         -> merge { This = \(_ : a) -> lst
                  , That = \(y : b) -> [y] # lst
                  , These = \(_ : { _1 : a, _2 : b }) -> lst
                  } th
       )
       ([] : List b)

let partitionTheseOnly =
     \(a : Type)
  -> \(b : Type)
  -> \(ths : List (These a b))
  -> List/fold
       (These a b)
       ths
       (List { _1 : a, _2 : b})
       (    \(th : These a b)
         -> \(lst : List { _1 : a, _2 : b})
         -> merge { This = \(_ : a) -> lst
                  , That = \(_ : b) -> lst
                  , These = \(z : { _1 : a, _2 : b }) -> [{ _1 = z._1, _2 = z._2 }] # lst
                  } th
       )
       ([] : List { _1 : a, _2 : b})

let partitionThese =
     \(a : Type)
  -> \(b : Type)
  -> \(ths : List (These a b))
  -> { this = partitionThis a b ths
     , that = partitionThat a b ths
     , these = partitionTheseOnly a b ths
     }
     : { this : List a
       , that : List b
       , these : List { _1 : a, _2 : b }
       }

let fromThisProof =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> \(prf : Proof/fromBool ^^"these.dhall: fromThisProof expected This"
         (isThis a b th)
      )
  -> merge { This = \(x : a) -> x
           , That = \(_ : b) -> PVoid/undefined a
           , These = \(z : {_1 : a, _2 : b }) -> PVoid/undefined a
           } th
           : a

let fromThatProof =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> \(prf : Proof/fromBool ^^"these.dhall: fromThatProof expected That"
         (isThat a b th)
      )
  -> merge { This = \(_ : a) -> PVoid/undefined b
           , That = \(x : b) -> x
           , These = \(z : {_1 : a, _2 : b }) -> PVoid/undefined b
           } th
           : b

let fromTheseProof =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> \(prf : Proof/fromBool ^^"these.dhall: fromTheseProof expected These"
         (isThese a b th)
      )
  -> let t = { _1 : a, _2 : b }
     in merge { This = \(_ : a) -> PVoid/undefined t
           , That = \(_ : b) -> PVoid/undefined t
           , These = \(z : t) -> z
           } th
           : t

let fromThisDef =
     \(a : Type)
  -> \(b : Type)
  -> \(aDef : a)
  -> \(th : These a b)
  -> merge { This = \(x : a) -> x
           , That = \(_ : b) -> aDef
           , These = \(z : {_1 : a, _2 : b }) -> aDef
           } th
           : a

let fromThatDef =
     \(a : Type)
  -> \(b : Type)
  -> \(bDef : b)
  -> \(th : These a b)
  -> merge { This = \(_ : a) -> bDef
           , That = \(y : b) -> y
           , These = \(z : {_1 : a, _2 : b }) -> bDef
           } th
           : b

let fromTheseDef =
     \(a : Type)
  -> \(b : Type)
  -> \(aDef : a)
  -> \(bDef : b)
  -> \(th : These a b)
  -> fromTheseWith a b {_1 : a, _2 : b } th aDef bDef (\(x : a) -> \(y : b) -> { _1 = x, _2 = y })
   : {_1 : a, _2 : b }


let justThis =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> merge { This = \(x : a) -> Some x
           , That = \(_ : b) -> None a
           , These = \(z : {_1 : a, _2 : b }) -> None a
           } th
           : Optional a

let justThat =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> merge { This = \(_ : a) -> None b
           , That = \(y : b) -> Some y
           , These = \(z : {_1 : a, _2 : b }) -> None b
           } th
           : Optional b

let justThese =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> merge { This = \(_ : a) -> None { _1 : a, _2 : b }
           , That = \(_ : b) -> None { _1 : a, _2 : b }
           , These = \(z : {_1 : a ,_2 : b }) -> Some { _1 = z._1, _2 = z._2 }
           } th
           : Optional { _1 : a, _2 : b }

let swap =
     \(a : Type)
  -> \(b : Type)
  -> \(th : These a b)
  -> let t = These b a
     in merge { This = \(a : a) -> t.That a
              , That = \(b : b) -> t.This b
              , These = \(z : { _1 : a, _2 : b }) -> t.These { _1 = z._2, _2 = z._1 }
              } th
   : These b a

let zip =
     \(a : Type)
  -> \(b : Type)
  -> \(xs : List a)
  -> \(ys : List b)
  -> let s = { _1 : a, _2 : b }
     let t = These a b
     let zs = pp.List.map s t (\(p : s) -> mkThese a b p._1 p._2) (ll.zipTrunc a b xs ys)
     let l1 = List/length a xs
     let l2 = List/length b ys
     in zs # (if pp.Natural.greaterThan l1 l2 then
                  pp.List.map
                          a
                          t
                          (mkThis a b)
                          (pp.List.drop l2 a xs)
        else if pp.Natural.lessThan l1 l2 then
                  pp.List.map
                          b
                          t
                          (mkThat a b)
                          (pp.List.drop l1 b ys)
        else [] : List t)
     : List t

{-
-- not a valid monoid: constructs These so we can never have That or This once we use mempty
let mempty =
   \(a : Type)
-> \(b : Type)
-> \(m : a)
-> \(n : b)
-> mkThese a b m n
  : These a b
-}
let mappend =
   \(a : Type)
-> \(b : Type)
-> \(m : a -> a -> a)
-> \(n : b -> b -> b)
-> \(x : These a b)
-> \(y : These a b)
-> let tothis = mkThis a b
   let tothat = mkThat a b
   let tothese = mkThese a b
   let p2 = { _1 : a, _2 : b }
   in merge
   { This = \(a1 : a) -> merge { This = \(a2 : a) -> tothis (m a1 a2)
                               , That = \(b2 : b) -> tothese a1 b2
                               , These = \(t2 : p2) -> tothese (m a1 t2._1) t2._2
                               } y
   , That = \(b1 : b) -> merge { This = \(a2 : a) -> tothese a2 b1
                               , That = \(b2 : b) -> tothat (n b1 b2)
                               , These = \(t2 : p2) -> tothese t2._1 (n b1 t2._2)
                               } y
   , These = \(t1 : p2) -> merge { This = \(a2 : a) -> tothese (m t1._1 a2) t1._2
                               , That = \(b2 : b) -> tothese t1._1 (n t1._2 b2)
                               , These = \(t2 : p2) -> tothese (m t1._1 t2._1) (n t1._2 t2._2)
                               } y
   } x
  : These a b

-- partitionThese
let filterThese =
    \(a : Type)
 -> \(b : Type)
 -> \(ths : List (These a b))
 -> let t = { _1 : a, _2 : b }
    in List/fold
      (These a b)
      ths
      (List t)
      (   \(x : These a b)
       -> \(ys : List t)
       -> merge { This = \(z : a) -> ys
                , That = \(z : b) -> ys
                , These = \(z : t) -> [z] # ys
                } x
      )
      ([] : List t)
      : List t

let compare =
    \(a : Type)
 -> \(b : Type)
 -> \(cmpa : a -> a -> oo.Ordering)
 -> \(cmpb : b -> b -> oo.Ordering)
 -> \(th1 : These a b)
 -> \(th2 : These a b)
 -> merge {
    , This = \(x : a) -> merge { This = cmpa x, That = \(_ : b) -> oo.LT, These = \(_ : { _1 : a, _2 : b}) -> oo.LT } th2
    , That = \(x : b) -> merge { That = cmpb x, This = \(_ : a) -> oo.GT, These = \(_ : { _1 : a, _2 : b}) -> oo.LT } th2
    , These = \(x : { _1 : a, _2 : b}) -> merge { These = tp.compare a b cmpa cmpb x, This = \(_ : a) -> oo.GT, That = \(_ : b) -> oo.GT } th2
    } th1
    : oo.Ordering

let test1 = assert : swap Natural Bool (mkThis Natural Bool 20) === mkThat Bool Natural 20
let test2 = assert : swap Natural Bool (mkThese Natural Bool 20 True) === mkThese Bool Natural True 20

let test3 = assert : zip Natural Bool [1,2,3,4,5] [True,True,False] ===
       (let b = mkThese Natural Bool
        let l = mkThis Natural Bool
        let r = mkThat Natural Bool
        in [ b 1 True, b 2 True, b 3 False, l 4, l 5 ]
   )
let test4 = assert : zip Natural NonZero [1,2,3,4] [!10,!11,!12,!13] ===
       (let b = mkThese Natural NonZero
        let l = mkThis Natural NonZero
        let r = mkThat Natural NonZero
        in [ b 1 !10, b 2 !11, b 3 !12, b 4 !13 ]
   )

let test5 = assert : zip Natural NonZero [1,2,3,4] [!10,!11,!12,!13,!14,!15] ===
       (let b = mkThese Natural NonZero
        let l = mkThis Natural NonZero
        let r = mkThat Natural NonZero
        in [ b 1 !10, b 2 !11, b 3 !12, b 4 !13, r !14, r !15 ]
   )
let test6 = assert : zip Natural NonZero [1,2,3,4] ([] : List NonZero) ===
       (let b = mkThese Natural NonZero
        let l = mkThis Natural NonZero
        let r = mkThat Natural NonZero
        in [ l 1, l 2, l 3, l 4 ]
   )
let test7 = assert : zip Natural NonZero ([] : List Natural) [!10,!11,!12] ===
       (let b = mkThese Natural NonZero
        let l = mkThis Natural NonZero
        let r = mkThat Natural NonZero
        in [ r !10, r !11, r !12 ]
   )

let test8 =
   let f1 = \(a : Type) -> \(b : Type) -> \(x : a) -> \(y : b) -> < This : a | That : b | These : { _1 : a, _2 : b } >.This x
   in assert : f1 NonZero DateTime !12 ^2020-02-03T01:12:13 === < This : NonZero | That : DateTime | These : { _1 : NonZero, _2 : DateTime } >.This !12

let test9 = assert : mappend (List Natural) oo.Ordering (ll.mappend Natural) oo.mappend (mkThis (List Natural) oo.Ordering [4,5,6]) (mkThat (List Natural) oo.Ordering oo.LT) === mkThese (List Natural) oo.Ordering [4,5,6] oo.LT
let test10 = assert : mappend (List Natural) oo.Ordering (ll.mappend Natural) oo.mappend (mkThese (List Natural) oo.Ordering [4,5,6] oo.GT) (mkThese (List Natural) oo.Ordering [1] oo.LT) === mkThese (List Natural) oo.Ordering [4,5,6,1] oo.GT

let test11 = assert : partitionThese Natural Integer [swap Integer Natural (mkThis Integer Natural +14), mkThese Natural Integer 44 -999, mkThese Natural Integer 123 -0] ===
  { that = [ +14 ]
  , these = [ { _1 = 44, _2 = -999 }, { _1 = 123, _2 = +0 } ]
  , this = [] : List Natural
  }

let test12 = assert : filterThese Natural Integer [swap Integer Natural (mkThis Integer Natural +14), mkThese Natural Integer 44 -999, mkThese Natural Integer 123 -0] ===
  [ { _1 = 44, _2 = -999 }, { _1 = 123, _2 = +0 } ]

let test13 = assert : mappend (List Natural) Text (ll.mappend Natural) (\(a : Text) -> \(b : Text) -> a ++ b) (mkThat (List Natural) Text "xxx") (mkThat (List Natural) Text "yyy") === mkThat (List Natural) Text "xxxyyy"
let test14 = assert : mappend (List Natural) Text (ll.mappend Natural) (\(a : Text) -> \(b : Text) -> a ++ b) (mkThat (List Natural) Text "xxx") (mkThis (List Natural) Text [1,2,3]) === mkThese (List Natural) Text [1,2,3] "xxx"

let test15 = assert : zip Natural Integer [1,2,3] [+12,+13,+14,+15,+16]
===
[ < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 1, _2 = +12 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 2, _2 = +13 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 3, _2 = +14 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.That
    +15
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.That
    +16
]

let test16 = assert : zip Natural Integer [1,2,3,4,5,6] [+12,+13]
  ===
[ < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 1, _2 = +12 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 2, _2 = +13 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    3
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    4
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    5
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    6
]

let test17 = assert : zip Natural Integer [1,2,3] [+12,+13,+14]
  ===
[ < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 1, _2 = +12 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 2, _2 = +13 }
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.These
    { _1 = 3, _2 = +14 }
]


let test18 = assert : zip Natural Integer [1,2,3] ([] : List Integer)
  ===
[ < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    1
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    2
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.This
    3
]

let test19 = assert : zip Natural Integer ([] : List Natural) [+12,+13,+14]
  ===
[ < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.That
    +12
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.That
    +13
, < That : Integer
  | These : { _1 : Natural, _2 : Integer }
  | This : Natural
  >.That
    +14
]

let test20 = assert : zip Natural Integer ([] : List Natural) ([] : List Integer)
  ===
([] : List
       < That : Integer
       | These : { _1 : Natural, _2 : Integer }
       | This : Natural
       >)

let test21 = assert : fromTheseProof Natural Bool (mkThese Natural Bool 123 True) Prf === { _1 = 123, _2 = True }
let test22 = assert : fromThisProof Natural Bool (mkThis Natural Bool 123) Prf === 123
let test23 = assert : fromThatProof Natural Bool (mkThat Natural Bool True) Prf === True

let test24 = assert : fromTheseDef Natural Bool 999 False (mkThese Natural Bool 123 True) === { _1 = 123, _2 = True }
let test25 = assert : fromTheseDef Natural Bool 999 False (mkThis Natural Bool 123) === { _1 = 123, _2 = False }
let test26 = assert : fromTheseDef Natural Bool 999 False (mkThat Natural Bool True) === { _1 = 999, _2 = True }

let test27 = assert : fromThisDef Natural Bool 999 (mkThis Natural Bool 123) === 123
let test28 = assert : fromThisDef Natural Bool 999 (mkThat Natural Bool True) === 999
let test29 = assert : fromThisDef Natural Bool 999 (mkThese Natural Bool 123 True) === 999

let test30 = assert : fromThatDef Natural Bool False (mkThat Natural Bool True) === True
let test31 = assert : fromThatDef Natural Bool False (mkThis Natural Bool 123) === False
let test32 = assert : fromThatDef Natural Bool False (mkThese Natural Bool 123 True) === False

let test33 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThis Natural Text 123) (mkThat Natural Text "dude") === oo.LT
let test34 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThat Natural Text "dude") (mkThis Natural Text 123) === oo.GT
let test35 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThis Natural Text 123) (mkThis Natural Text 123) === oo.EQ
let test36 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThis Natural Text 122) (mkThis Natural Text 123) === oo.LT
let test37 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThis Natural Text 124) (mkThis Natural Text 123) === oo.GT
let test38 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThese Natural Text 123 "abc") (mkThat Natural Text "dude") === oo.GT
let test39 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThese Natural Text 123 "abc") (mkThis Natural Text 12) === oo.GT
let test40 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThese Natural Text 123 "abc") (mkThese Natural Text 123 "ABC") === oo.EQ
let test41 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThese Natural Text 123 "abc") (mkThese Natural Text 124 "xyz") === oo.LT
let test42 = assert : compare Natural Text oo.compareNatural oo.compareTextIgnore (mkThese Natural Text 123 "abc") (mkThese Natural Text 122 "xyz") === oo.GT
let test43 = assert : compare Natural Text oo.compareNatural oo.compareText (mkThese Natural Text 123 "dude") (mkThese Natural Text 123 "DudE") === oo.GT

in
{
, These
, mkThis
, mkThat
, mkThese
, these
, mergeTheseWith
, mergeThese
, isThis
, isThat
, isThese
, fromThisProof
, fromThatProof
, fromTheseProof
, justThis
, justThat
, justThese
, fromTheseWith
, fromThisDef
, fromThatDef
, fromTheseDef
, partitionThese
, swap
, zip
, mappend
, filterThese
, compare
}
