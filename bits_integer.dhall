let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let bb = ./bits.dhall
let nz = ./nonzero.dhall

let complement =
    \(n : Integer)
 -> Integer/negate (Integer/add +1 n)
    : Integer

let or =
    \(m : Integer)
 -> \(n : Integer)
 -> complement (Integer/and (complement m) (complement n))
    : Integer

let testBit =
    \(n : Integer)
 -> \(i : Natural)
 -> let x = pp.Integer.abs n
    in if pp.Integer.negative n then bb.testBit (pp.Integer.abs (complement n)) i == False
       else bb.testBit x i
    : Bool

let setBit =
    \(n : Integer)
 -> \(i : Natural)
 -> or n (NonZero/toInteger (nz.pow !2 i))
   : Integer

let clearBit =
    \(n : Integer)
 -> \(i : Natural)
 -> Integer/and n (complement (NonZero/toInteger (nz.pow !2 i)))
   : Integer

let flipBit =
    \(n : Integer)
 -> \(i : Natural)
 -> if testBit n i then clearBit n i else setBit n i
   : Integer

let shiftL =
    \(n : Integer)
 -> \(i : Natural)
 -> let ret = Natural/toInteger (bb.shiftL (pp.Integer.abs n) i)
    in if pp.Integer.negative n
       then Integer/negate ret
       else ret
   : Integer

let shiftR =
    \(n : Integer)
 -> \(i : Natural)
 -> let ret = Natural/toInteger (bb.shiftR (pp.Integer.abs n) i)
    in if pp.Integer.negative n
       then complement ret
       else ret
    : Integer

let popCount =
    \(n : Integer)
 -> let ret = Natural/toInteger (bb.popCount (pp.Integer.abs n))
    in if pp.Integer.negative n
       then Integer/negate ret
       else ret
  : Integer

let show =
    \(n : Integer)
 -> \(i : NonZero)
 -> List/fold
     Natural
     (pp.Natural.enumerate (NonZero/toNatural i))
     Text
     (\(x : Natural) -> \(z : Text) -> z ++ (if testBit n x then "1" else "0"))
     ""
     : Text

let test1 = assert : pp.List.map Integer Integer complement [-3,-2,-1,+0,+1,+2,+3] === [+2,+1,+0,-1,-2,-3,-4]

let test2 = assert : Integer/and +123 +70 === +66
let test3 = assert : Integer/and -123 -70 === -128
let test4 = assert : Integer/and -123 +70 === +4
let test5 = assert : Integer/and +123 -70 === +58

let test6 = assert : or +123 +70 === +127
let test7 = assert : or -123 -70 === -65
let test8 = assert : or -123 +70 === -57
let test9 = assert : or +123 -70 === -5

let test10 = assert : Integer/and +123 +0 === +0
let test11 = assert : Integer/and -0 +0 === +0
let test12 = assert : Integer/and -12 +0 === -0
let test13 = assert : Integer/and +1 +0 === +0
let test14 = assert : Integer/and +0 -1 === -0

let test15 = assert : Integer/and +111 -154 === +102

let test16 = assert : or +123 +0 === +123
let test17 = assert : or -0 +0 === +0
let test18 = assert : or -12 +0 === -12
let test19 = assert : or +1 +0 === +1
let test20 = assert : or +0 -1 === -1

let test21 = assert : show -2 !5
===
"11110"

let test22 = assert : show -7 !5
===
"11001"

let test23 = assert : show -8 !5
===
"11000"

let test24 = assert : show -8 !20
===
"11111111111111111000"

let test25 = assert : clearBit -8 40 === -1099511627784
let test26 = assert : setBit -8 40 === -8
let test27 = assert : flipBit -8 40 === -1099511627784

let test28 = assert : clearBit -1234 4 === -1234
let test29 = assert : flipBit -1234 4 === -1218
let test30 = assert : clearBit -1234 3 === -1242
let test31 = assert : flipBit -1234 3 === -1242
let test32 = assert : setBit -1242 3 === -1234

let test33 = assert : shiftL -134 3 === -1072
let test34 = assert : shiftL +134 3 === +1072

let test35 = assert : shiftR -134 3 === -17
let test36 = assert : shiftR +134 3 === +16

let test37 = assert : shiftR +97 10 === -0
let test38 = assert : shiftR -97 10 === -1

let test39 = assert : shiftL -97 10 === -99328
let test40 = assert : shiftR -97 10 === -1
let test41 = assert : popCount -145 === -3
let test42 = assert : popCount +145 === +3
let test43 = assert : popCount -256 === -1
let test44 = assert : popCount -255 === -8
let test45 = assert : popCount +255 === +8

let test46 = assert : show -15 !11 === "11111110001"
let test47 = assert : show -16 !11 === "11111110000"

in {
, complement
, or
, testBit
, setBit
, clearBit
, flipBit
, popCount

, shiftL
, shiftR

, show
}

{-
>mapM_ print $ map (\y -> (y,map (\x -> if testBit (-y) x then '1' else '0') [10,9 .. 0])) [1 .. 16]
(1,"11111111111")
(2,"11111111110")
(3,"11111111101")
(4,"11111111100")
(5,"11111111011")
(6,"11111111010")
(7,"11111111001")
(8,"11111111000")
(9,"11111110111")
(10,"11111110110")
(11,"11111110101")
(12,"11111110100")
(13,"11111110011")
(14,"11111110010")
(15,"11111110001")
(16,"11111110000")
it :: ()
-}