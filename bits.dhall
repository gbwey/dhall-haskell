-- rotate bits is the same as shift for unbounded types
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let ll = ./list.dhall
let nn = ./natural.dhall

-- just for testing: use NonZero/toBits
{-
let toBitsALT =
  \(n : Natural)
  -> let s = List Bool
     in if Natural/isZero n then [False]
        else
          let t = { left : Natural, ret : s }
          let r =
            Natural/fold
              (1 + NonZero/log !1 (NonZero/clamp n)) -- n is not zero here also NonZero/log !1 is base 2 as base 1 is not defined
               t
              (   \(z : t)
               -> if Natural/isZero z.left then z
                  else
                    let w = nn.divMod z.left !2
                    let b = Natural/isZero w._2 == False
                    in {
                       , left = w._1
                       , ret = [b] # z.ret
                       }
              )
              { left = n, ret = [] : s }
          in r.ret
        : s
-}
-- use List/build
let toBitsALT =
  \(n : Natural)
  -> if Natural/isZero n then [False]
     else
       List/build
          Bool
          (   \(list : Type)
           -> \(cons : Bool -> list -> list)
           -> \(nil : list)
           ->
              let t = { left : Natural, ret : list }
              let r =
                Natural/fold
                  (1 + NonZero/log !1 (NonZero/clamp n)) -- n is not zero here also NonZero/log !1 is base 2 as base 1 is not defined
                   t
                  (   \(z : t)
                   -> if Natural/isZero z.left then z
                      else
                        let w = nn.divMod z.left !2
                        let b = Natural/isZero w._2 == False
                        in {
                           , left = w._1
                           , ret = cons b z.ret
                           }
                  )
                  { left = n, ret = nil }
               in r.ret
           )
       : List Bool

let fromBitsOLD =
  \(bs : List Bool)
  -> let t = { mult : Natural, ret : Natural }
     let w = List/fold
       Bool
       bs
       t
       (\(x : Bool) -> \(z : t) -> { mult = z.mult * 2, ret = z.mult * (if x then 1 else 0) + z.ret })
       { mult = 1, ret = 0 }
     in w.ret
     : Natural

let fromBits =
  \(bs : List Bool)
  -> List/fold
       Bool
       (List/reverse Bool bs)
       Natural
       (\(x : Bool) -> \(z : Natural) -> (if x then 1 else 0) + z * 2)
       0
     : Natural

let shiftL =
    \(n : Natural)
 -> \(i : Natural)
 -> let bs = Natural/toBits n
    in fromBits (bs # pp.List.replicate i Bool False)
    : Natural

let shiftR =
    \(n : Natural)
 -> \(i : Natural)
 -> let bs = Natural/toBits n
    let len = List/length Bool bs
    in fromBits (pp.List.take (Natural/subtract i len) Bool bs)
    : Natural

let overBit =
    \(n : Natural)
 -> \(i : Natural)
 -> \(f : Bool -> Bool)
 -> let bs = Natural/toBits n
    let len = List/length Bool bs
    let ret =
      if pp.Natural.greaterThanEqual i len then
        [f False] # pp.List.replicate (Natural/subtract len i) Bool False # bs
      else
        let pos = Natural/subtract (i + 1) len
        let a1 = pp.List.take pos Bool bs -- pre
        let a2 = pp.List.take (pos + 1) Bool bs -- target
        let val = merge { None = PVoid/undefined Bool, Some = \(x : Bool) -> x } (List/last Bool a2)
        let a3 = pp.List.drop (pos + 1) Bool bs -- post
        in a1 # [f val] #  a3
    in fromBits ret
       : Natural

let flipBit =
    \(n : Natural)
 -> \(i : Natural)
 -> overBit n i (\(x : Bool) -> x == False)

let setBit =
    \(n : Natural)
 -> \(i : Natural)
 -> overBit n i (\(_ : Bool) -> True)

let clearBit =
    \(n : Natural)
 -> \(i : Natural)
 -> overBit n i (\(_ : Bool) -> False)

let testBit =
    \(n : Natural)
 -> \(i : Natural)
 -> let bs = Natural/toBits n
    let len = List/length Bool bs
    in if pp.Natural.greaterThanEqual i len then False
       else
         let a2 = pp.List.take (Natural/subtract i len) Bool bs
         in merge { None = PVoid/undefined Bool, Some = \(x : Bool) -> x } (List/last Bool a2)
    : Bool

let flipBits =
    \(n : Natural)
 -> let bs = Natural/toBits n
    in fromBits (pp.List.map Bool Bool (\(x : Bool) -> x == False) bs)
    : Natural

let apply =
    \(m : Natural)
 -> \(n : Natural)
 -> \(f : Bool -> Bool -> Bool)
 -> let z =
      ll.fill
        Bool
        Bool
        True
        (Natural/toBits m)
        (Natural/toBits n)
        False
        False
    let xs =
      ll.zipWithTrunc
        Bool
        Bool
        Bool
        f
        z._1
        z._2
    in fromBits xs
    : Natural

let xor =
    \(m : Natural)
 -> \(n : Natural)
 -> pp.Integer.abs (Integer/xor (Natural/toInteger m) (Natural/toInteger n))
    : Natural

let and =
    \(m : Natural)
 -> \(n : Natural)
 -> pp.Integer.abs (Integer/and (Natural/toInteger m) (Natural/toInteger n))
    : Natural

let or =
    \(m : Natural)
 -> \(n : Natural)
 -> let complement = \(i : Integer) -> Integer/negate (Integer/add +1 i)
    in pp.Integer.abs
     (complement
       (Integer/and
         (complement (Natural/toInteger m))
         (complement (Natural/toInteger n))
       )
     )
     : Natural

let unset =
    \(m : Natural)
 -> \(n : Natural)
 -> apply m n (\(x : Bool) -> \(y : Bool) -> if y then False else x)
    : Natural

let popCount =
    \(n : Natural)
 -> List/fold
      Bool
      (Natural/toBits n)
      Natural
      (\(x : Bool) -> \(z : Natural) -> (if x then 1 else 0) + z)
      0
  : Natural

let take =
    \(i : NonZero)
 -> \(n : Natural)
 -> let xs = Natural/toBits n
    let ret = pp.List.drop (Natural/subtract (NonZero/toNatural i) (List/length Bool xs)) Bool xs
    in fromBits ret
   : Natural

let invert =
    \(n : Natural)
 -> let xs = Natural/toBits n
    let ret = pp.List.map Bool Bool (\(x : Bool) -> x == False) xs
    in fromBits ret
   : Natural

let reverse =
    \(n : Natural)
 -> fromBits (List/reverse Bool (Natural/toBits n))
   : Natural

let show =
    \(n : Natural)
 -> \(i : NonZero)
 -> List/fold
     Natural
     (pp.Natural.enumerate (NonZero/toNatural i))
     Text
     (\(x : Natural) -> \(z : Text) -> z ++ (if testBit n x then "1" else "0"))
     ""
    : Text

let test1 = assert : shiftR 7 1 === 3
let test2 = assert : shiftR 8 1 === 4
let test3 = assert : shiftL 8 1 === 16
let test4 = assert : shiftR 0 0 === 0
let test5 = assert : shiftL 0 0 === 0
let test6 = assert : shiftL 1 8 === 256
let test7 = assert : shiftL 0 8 === 0
let test8 = assert : shiftR 0 8 === 0
let test9 = assert : shiftR 255 0 === 255
let test10 = assert : shiftL 255 0 === 255

let test11 = assert : shiftR 2597 5 === 81
let test12 = assert : shiftL 2597 5 === 83104

let test13 = assert : xor 0 0 === 0
let test14 = assert : xor 12345 822 === 13071
let test15 = assert : xor 822 12345 === 13071

let test16 = assert : flipBits 256 === 255

let test17 = assert : flipBit 256 3 === 264
let test18 = assert : flipBit 256 8 === 0

let test19 = assert : setBit 12345 3 === 12345
let test20 = assert : setBit 12345 5 === 12345
let test21 = assert : setBit 12345 9 === 12857
let test22 = assert : setBit 0 9 === 512

let test23 = assert : flipBit 12345 9 === 12857
let test24 = assert : flipBit 12345 5 === 12313
let test25 = assert : flipBit 12313 5 === 12345

let test26 = assert : testBit 12345 3 === True
let test27 = assert : testBit 12345 5 === True
let test28 = assert : testBit 12345 9 === False
let test29 = assert : testBit 7 9 === False
let test30 = assert : testBit 7 0 === True
let test31 = assert : testBit 7 1 === True
let test32 = assert : testBit 7 2 === True
let test33 = assert : testBit 7 3 === False
let test34 = assert : testBit 7 4 === False

let test35 = assert : clearBit 12345 3 === 12337
let test36 = assert : clearBit 12345 300 === 12345

let test37 = assert : and 1234 765 === 208
let test38 = assert : or 1234 765 === 1791

let test39 = assert : popCount 255 === 8
let test40 = assert : popCount 256 === 1
let test41 = assert : popCount 0 === 0
let test42 = assert : popCount 1 === 1

let test43 = assert : Natural/toBits 0 === [False]
let test44 = assert : Natural/toBits 1 === [True]
let test45 = assert : Natural/toBits 2 === [True,False]
let test46 = assert : Natural/toBits 3 === [True,True]
let test47 = assert : Natural/toBits 4 === [True,False,False]
let test48 = assert : Natural/toBits 5 === [True,False,True]
let test49 = assert : Natural/toBits 6 === [True,True,False]
let test50 = assert : Natural/toBits 7 === [True,True,True]
let test51 = assert : Natural/toBits 8 === [True,False,False,False]

let test52 = assert : toBitsALT 0 === [False]
let test53 = assert : toBitsALT 1 === [True]
let test54 = assert : toBitsALT 2 === [True,False]
let test55 = assert : toBitsALT 3 === [True,True]
let test56 = assert : toBitsALT 4 === [True,False,False]
let test57 = assert : toBitsALT 5 === [True,False,True]
let test58 = assert : toBitsALT 6 === [True,True,False]
let test59 = assert : toBitsALT 7 === [True,True,True]
let test60 = assert : toBitsALT 8 === [True,False,False,False]
let test61 = assert : fromBits (Natural/toBits 12334) === 12334
let test62 = assert : fromBits (Natural/toBits 987) === 987
let test63 = assert : fromBits (toBitsALT 12334) === 12334
let test64 = assert : fromBits (toBitsALT 987) === 987
let test64 = assert : fromBits [True,False,False,False] === 8
let test64 = assert : fromBits [False,False,False,True,False,False,False] === 8

let test64 = assert : fromBitsOLD [False,False,False,True,False,False,False] === 8

let test65 = assert : take !4 24 === 8
let test66 = assert : take !1 9 === 1
let test67 = assert : take !2 9 === 1
let test68 = assert : invert 19 === 12
let test69 = assert : invert 12 === 3
let test70 = assert : invert 1 === 0
let test71 = assert : invert 7 === 0
let test72 = assert : invert 8 === 7
let test73 = assert : reverse 19 === 25
let test74 = assert : reverse 7 === 7
let test75 = assert : reverse 1 === 1
let test76 = assert : reverse 0 === 0

let test77 = assert : pp.List.map Natural { _1  : Natural, _2 : List Bool } (\(n : Natural) -> { _1 = n, _2 = Natural/toBits n }) (pp.Natural.enumerate 50)
===
[ { _1 = 0, _2 = [ False ] }
, { _1 = 1, _2 = [ True ] }
, { _1 = 2, _2 = [ True, False ] }
, { _1 = 3, _2 = [ True, True ] }
, { _1 = 4, _2 = [ True, False, False ] }
, { _1 = 5, _2 = [ True, False, True ] }
, { _1 = 6, _2 = [ True, True, False ] }
, { _1 = 7, _2 = [ True, True, True ] }
, { _1 = 8, _2 = [ True, False, False, False ] }
, { _1 = 9, _2 = [ True, False, False, True ] }
, { _1 = 10, _2 = [ True, False, True, False ] }
, { _1 = 11, _2 = [ True, False, True, True ] }
, { _1 = 12, _2 = [ True, True, False, False ] }
, { _1 = 13, _2 = [ True, True, False, True ] }
, { _1 = 14, _2 = [ True, True, True, False ] }
, { _1 = 15, _2 = [ True, True, True, True ] }
, { _1 = 16, _2 = [ True, False, False, False, False ] }
, { _1 = 17, _2 = [ True, False, False, False, True ] }
, { _1 = 18, _2 = [ True, False, False, True, False ] }
, { _1 = 19, _2 = [ True, False, False, True, True ] }
, { _1 = 20, _2 = [ True, False, True, False, False ] }
, { _1 = 21, _2 = [ True, False, True, False, True ] }
, { _1 = 22, _2 = [ True, False, True, True, False ] }
, { _1 = 23, _2 = [ True, False, True, True, True ] }
, { _1 = 24, _2 = [ True, True, False, False, False ] }
, { _1 = 25, _2 = [ True, True, False, False, True ] }
, { _1 = 26, _2 = [ True, True, False, True, False ] }
, { _1 = 27, _2 = [ True, True, False, True, True ] }
, { _1 = 28, _2 = [ True, True, True, False, False ] }
, { _1 = 29, _2 = [ True, True, True, False, True ] }
, { _1 = 30, _2 = [ True, True, True, True, False ] }
, { _1 = 31, _2 = [ True, True, True, True, True ] }
, { _1 = 32, _2 = [ True, False, False, False, False, False ] }
, { _1 = 33, _2 = [ True, False, False, False, False, True ] }
, { _1 = 34, _2 = [ True, False, False, False, True, False ] }
, { _1 = 35, _2 = [ True, False, False, False, True, True ] }
, { _1 = 36, _2 = [ True, False, False, True, False, False ] }
, { _1 = 37, _2 = [ True, False, False, True, False, True ] }
, { _1 = 38, _2 = [ True, False, False, True, True, False ] }
, { _1 = 39, _2 = [ True, False, False, True, True, True ] }
, { _1 = 40, _2 = [ True, False, True, False, False, False ] }
, { _1 = 41, _2 = [ True, False, True, False, False, True ] }
, { _1 = 42, _2 = [ True, False, True, False, True, False ] }
, { _1 = 43, _2 = [ True, False, True, False, True, True ] }
, { _1 = 44, _2 = [ True, False, True, True, False, False ] }
, { _1 = 45, _2 = [ True, False, True, True, False, True ] }
, { _1 = 46, _2 = [ True, False, True, True, True, False ] }
, { _1 = 47, _2 = [ True, False, True, True, True, True ] }
, { _1 = 48, _2 = [ True, True, False, False, False, False ] }
, { _1 = 49, _2 = [ True, True, False, False, False, True ] }
]

let test78 = assert : pp.List.map Natural (List Bool) Natural/toBits (pp.Natural.enumerate 50)
=== pp.List.map Natural (List Bool) toBitsALT (pp.Natural.enumerate 50)

let test79 = assert : unset 7 20 === 3
let test80 = assert : unset 0 20 === 0
let test81 = assert : unset 20 0 === 20
let test82 = assert : unset 1234 1 === 1234
let test83 = assert : unset 734 218 === 516

--  overBit not needed as set/clear/flip cover all possibilities
in {
, shiftL
, shiftR
, fromBits
, flipBits
, setBit
, clearBit
, flipBit
, testBit
, apply
, and
, or
, xor
, bit = shiftL 1
, popCount
, take
, reverse
, invert
, unset
, show

, fromBitsOLD
, toBitsALT

}