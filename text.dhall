-- ascii text functions only
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let bb = ./bool.dhall
let oo = ./ordering.dhall
let nn = ./natural.dhall
let ll = ./list.dhall
-- 97 122 -- lower
-- 65 90 -- upper

let all =
    \(p : Natural -> Bool)
 -> \(t : Text)
 -> pp.List.all Natural p (Text/unpack t)
 : Bool

let any =
    \(p : Natural -> Bool)
 -> \(t : Text)
 -> pp.List.any Natural p (Text/unpack t)
 : Bool

let compare = oo.compareText
let compareIgnore = oo.compareTextIgnore

let mempty = "" : Text

let mappend =
    \(xs : Text)
 -> \(ys : Text) -> xs ++ ys
   : Text

let mconcat =
    \(xs : List Text)
  -> List/fold Text xs Text (\(a : Text) -> \(b : Text) -> a ++ b) ""
  : Text

let lessThan =
    \(t1 : Text)
 -> \(t2 : Text)
 -> oo.isLT (compare t1 t2)
  : Bool

let lessThanEqual =
    \(t1 : Text)
 -> \(t2 : Text)
 -> oo.isLE (compare t1 t2)
  : Bool

let greaterThan =
    \(t1 : Text)
 -> \(t2 : Text)
 -> oo.isGT (compare t1 t2)
  : Bool

let greaterThanEqual =
    \(t1 : Text)
 -> \(t2 : Text)
 -> oo.isGE (compare t1 t2)
  : Bool

let min =
    \(m : Text)
 -> \(n : Text)
 -> if greaterThan m n then n else m
  : Text

let max =
    \(m : Text)
 -> \(n : Text)
 -> if greaterThan m n then m else n
  : Text

let equal =
    \(m : Text)
 -> \(n : Text)
 -> oo.isEQ (oo.compareText m n)
    : Bool

let equalIgnore =
    \(m : Text)
 -> \(n : Text)
 -> oo.isEQ (oo.compareTextIgnore m n)
    : Bool

let newline = Text/pack [10] : Text
let tab = Text/pack [9] : Text

let isSpace = \(n : Natural) -> pp.List.any Natural (pp.Natural.equal n) [9,10,11,12,13,32] : Bool

let isPunctuation = \(n : Natural) -> pp.List.any Natural (pp.Natural.equal n) [33,34,35,37,38,39,40,41,42,44,45,46,47,58,59,63,64,91,92,93,95,123,125] : Bool

let isSymbol = \(n : Natural) -> pp.List.any Natural (pp.Natural.equal n) [36,43,60,61,62,94,96,124,126] : Bool
let isLower = nn.between 97 122 : Natural -> Bool
let isUpper = nn.between 65 90 : Natural -> Bool
let isAlpha = \(n : Natural) -> isLower n || isUpper n : Bool
let isDigit = nn.between 48 57 : Natural -> Bool
let isAscii = nn.between 0 127 : Natural -> Bool
let isHex = bb.ors Natural [isDigit, nn.between 97 102, nn.between 65 70] : Natural -> Bool
let isOct = nn.between 48 55 : Natural -> Bool
let isBin = nn.between 48 49 : Natural -> Bool
let isPrint = bb.ors Natural [isAlpha, isDigit, isSymbol, isPunctuation, pp.Natural.equal 32] : Natural -> Bool

let mapt =
    \(f : Natural -> Natural)
 -> \(t : Text)
 -> Text/pack (pp.List.map Natural Natural f (Text/unpack t))
 : Text

let toUpperNat = \(n : Natural) -> if isLower n then Natural/subtract 32 n else n : Natural
let toLowerNat = \(n : Natural) -> if isUpper n then 32 + n else n : Natural

let flipNat = \(n : Natural) -> if isLower n then toUpperNat n else toLowerNat n : Natural
let flips = mapt flipNat : Text -> Text

let reverse =
    \(t : Text)
  -> Text/pack (List/reverse Natural (Text/unpack t)) : Text

let splitAt =
     \(n : Natural)
  -> \(txt : Text)
  -> let z = ll.splitAt Text n (Text/toList txt)
     in { _1 = pp.Text.concat z._1, _2 = pp.Text.concat z._2 }
     : { _1 : Text, _2 : Text }

let allInList =
    \(needles : List Text) -- check these to make sure they all members of haystack
 -> \(haystack : List Text) -- these are valid
 -> pp.List.all Text (\(t : Text) -> ll.elem Text haystack (equal t)) needles

let replicate =
    \(n : Natural)
 -> \(xs : Text)
 -> Natural/fold
      n
      Text
      (\(a : Text) -> a ++ xs)
      ""
   : Text

--let isAllLower = \(t : Text) -> Text/unpack
let test1 = assert : Text/toLower "abcDEFG123_" === "abcdefg123_"
let test2 = assert : Text/toUpper "abcDEFG123_" === "ABCDEFG123_"

let test3 = assert : Text/unpack "Ab!v" === [ 65, 98, 33, 118 ]
let test4 = assert : Text/pack [ 65, 98, 33, 118 ] === "Ab!v"

let test5 = assert : mapt flipNat "frEdABCdef! !@#$%" === "FReDabcDEF! !@#\$%"
let test6 = assert : all isUpper "abcz" === False
let test7 = assert : all isUpper "ABCZ" === True
let test8 = assert : all isLower "abcz" === True
let test9 = assert : all isLower "aBbc" === False
let test10 = assert : all isUpper "aXbc" === False
let test11 = assert : pp.List.all Natural isDigit (Text/unpack "1234") === True
let test12 = assert : pp.List.map Natural Bool isDigit (Text/unpack "09AB1") === [ True, True, False, False, True ]
let test13 = assert : pp.List.map Natural Bool isUpper (Text/unpack "AZaz09") === [ True, True, False, False, False, False ]
let test14 = assert : pp.List.map Natural Bool isLower (Text/unpack "AZaz09") === [ False, False, True, True, False, False ]
let test15 = assert : pp.List.map Natural Bool isBin (Text/unpack "aA0123") === [ False, False, True, True, False, False ]
let test16 = assert : pp.List.all Natural isHex (Text/unpack "01234567890abcdefABCDEF") === True
let test17 = assert : pp.List.all Natural isHex (Text/unpack "Ggghi") === False
let test18 = assert : pp.List.all Natural isOct (Text/unpack "01234567") === True
let test19 = assert : pp.List.all Natural isOct (Text/unpack "Ggghi89abcdef") === False
let test20 = assert : pp.List.all Natural isBin (Text/unpack "010111") === True
let test21 = assert : pp.List.all Natural isBin (Text/unpack "23456789Ggghi89abcdef") === False

let test22 = assert : Text/toLower "abcDEFG123_" === "abcdefg123_"
let test23 = assert : Text/toUpper "abcDEFG123_" === "ABCDEFG123_"

let test24 = assert : Text/unpack "Ab!v" === [ 65, 98, 33, 118 ]
let test25 = assert : Text/pack [ 65, 98, 33, 118 ] === "Ab!v"

let test26 = assert : let a = "ABC" in Text/toLower ''
  ${a}DEFG123
  '' === ''
  abcdefg123
  ''
-- these two tests dont work in vscode as newlines are \r\n
-- unless the file is lf: not crlf: see icon bottom right
let test27 = assert : ("abc" ++ newline ++ "def" ++ newline) === ''
abc
def
''

let test28 = assert : "abc${newline}def${newline}" === ''
abc
def
''

let test29 = assert : compare "abc" "abx" === oo.LT
let test30 = assert : compare "abc" "Abx" === oo.GT
let test31 = assert : compare "abc" "Aaxxx" === oo.GT
let test32 = assert : compare "abc" "abc" === oo.EQ
let test33 = assert : compare "abc" "" === oo.GT
let test34 = assert : compare "" "abc" === oo.LT
let test35 = assert : compare "" "" === oo.EQ

let test36 = assert : splitAt 99 "abc" === { _1 = "abc", _2 = "" }
let test37 = assert : splitAt 3 "abcdefgh" === { _1 = "abc", _2 = "defgh" }
let test38 = assert : splitAt 0 "abcdefgh" === { _1 = "", _2 = "abcdefgh" }
let test39 = assert : splitAt 3 "" === { _1 = "", _2 = "" }
let test40 = assert : splitAt 3 "ab" === { _1 = "ab", _2 = "" }

let test41 = assert : Text/toList "abcdef" === ["a","b","c","d","e","f"]
let test42 = assert : Text/toList "" === ([] : List Text)
let test43 = assert : Text/length "abcdef" === 6
let test44 = assert : Text/length "" === 0
let test45 = assert : Text/unpack "" === ([] : List Natural)
let test46 = assert : Text/pack ([] : List Natural) === ""
let test47 = assert : Text/unpack "abc" === [97,98,99]
let test48 = assert : Text/pack [97,98,99] === "abc"

let test49 = assert : allInList ["x"] ["a","b","c"] === False
let test50 = assert : allInList ["a","b","b","a"] ["a","b","c"] === True
let test51 = assert : allInList ["a","b","b","w","a"] ["a","b","c"] === False

let test52 = assert : compare "abc" "abc" === oo.Ordering.EQ
let test53 = assert : compare "aBc" "abc" === oo.Ordering.LT
let test54 = assert : compare "abc" "aBc" === oo.Ordering.GT
let test55 = assert : compare "abc" "abc   " === oo.Ordering.LT
let test56 = assert : compare "abc  " "abc" === oo.Ordering.GT
let test57 = assert : compare "" "" === oo.Ordering.EQ

let test58 = assert : compareIgnore "abc" "AbC" === oo.Ordering.EQ
let test59 = assert : compareIgnore "aBc" "abc" === oo.Ordering.EQ
let test60 = assert : compareIgnore "ABC" "abc" === oo.Ordering.EQ
let test61 = assert : compareIgnore "abc" "ABC  " === oo.Ordering.LT
let test62 = assert : compareIgnore "ABC  " "abc" === oo.Ordering.GT
let test63 = assert : compareIgnore "" "" === oo.Ordering.EQ

let test64 = assert : equalIgnore "abc" "AbC" === True
let test65 = assert : equalIgnore "abc" "AbCd" === False
let test66 = assert : equal "abc" "AbC" === False
let test67 = assert : equal "ABC" "ABC" === True
let test68 = assert : equal "abc" "abc" === True

let test69 = assert : Regex/replix ~"(\d)" (mapt (\(y : Natural) -> if pp.Natural.equal y 57 then 49 else y + 1)) "123.144.2.89"
===
"234.255.3.91"

let test70 = assert : all isBin "23456789Ggghi89abcdef" === False
let test71 = assert : all isAlpha "abcD" === True
let test72 = assert : all isBin "00011010" === True
let test73 = assert : all isBin "000110102" === False
let test74 = assert : all isBin "" === True
let test75 = assert : all isHex "123aFa" === True
let test76 = assert : any isBin "23456789Ggghi89abcdef" === False
let test77 = assert : any isBin "234567189Ggghi89abcdef" === True

let test78 = assert : pp.List.filter Natural isSymbol (nn.enumerate 100)
===
[ 36, 43, 60, 61, 62, 94, 96 ]

let test79 = assert : reverse "abcdef" === "fedcba"
let test80 = assert : let xs = "asfjksfjk12930131!" in reverse (reverse xs) === xs
let test81 = assert : replicate 0 "abcd" === ""
let test82 = assert : replicate 0 "" === ""
let test83 = assert : replicate 100 "" === ""
let test84 = assert : replicate 10 "a" === "aaaaaaaaaa"


in {
, mempty
, mappend
, mconcat
, compare
, equal
, lessThanEqual
, lessThan
, greaterThanEqual
, greaterThan
, compareIgnore
, equalIgnore
, newline
, tab
, isSpace
, isPunctuation
, isSymbol
, isLower
, isUpper
, isAlpha
, isDigit
, isAscii
, isHex
, isOct
, isBin
, isPrint
, mapt
, toUpperNat
, toLowerNat
, flipNat
, flips
, reverse
, splitAt
, allInList
, all
, min
, max
, replicate
}