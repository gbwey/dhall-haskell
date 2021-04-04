-- use (./text.dhall).mapt with replix for map chars
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude

let ScanT0 = { _1 : Text, _2 : List Text }
let ScanT = List ScanT0

let scan =
    \(r : Regex)
 -> \(t : Text)
 -> Regex/scan r t !100
  : ScanT

let split =
    \(r : Regex)
 -> \(t : Text)
 -> Regex/split r t !100
 : List Text

let scanFsts =
    \(r : Regex)
 -> \(t : Text)
 -> pp.List.map ScanT0 Text (\(z : ScanT0) -> z._1) (scan r t)
 : List Text

let scanSnds =
    \(r : Regex)
 -> \(t : Text)
 -> pp.List.map ScanT0 (List Text) (\(z : ScanT0) -> z._2) (scan r t)
  : List (List Text)

let scanSndsOne =
    \(r : Regex)
 -> \(t : Text)
 -> merge { None = [] : List Text, Some = \(x : List Text) -> x } (List/head (List Text) (scanSnds r t))
  : List Text

let words = \(t : Text) -> scanFsts ~"\S+" t : List Text

let lines = split ~"\n" : Text -> List Text

let ip4RE = ~"^(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])\.(25[0-5]|2[0-4][0-9]|1[0-9][0-9]|[1-9][0-9]|[0-9])$"

let ip4Parse4 =
  \(t : Text)
  -> pp.List.map
      Text
      Natural
      (\(x : Text) ->
          merge
            { None = PVoid/undefined Natural
            , Some = \(y : Natural) -> y
            } (Natural/parse x)
      )
      (scanSndsOne ip4RE t)
    : List Natural

let ip4Parse4ALT =
  \(t : Text)
  -> let s = ListFixed !!4 Natural
     let ret =
       pp.List.map
        Text
        Natural
        (\(x : Text) ->
            merge
              { None = PVoid/error ^^"ip4Parse4ALT: Natural/parse failed" Natural
              , Some = \(y : Natural) -> y
              } (Natural/parse x)
        )
        (scanSndsOne ip4RE t)
     in if pp.List.null Natural ret then None s
        else Some (ListFixed/fromList !!4 Natural (PVoid/error ^^"expected exactly 4 Naturals" Natural) ret)
    : Optional s

let test1 = assert : Regex/scan ~"^(.{0,4})(.*)" "abc" !10 === [ { _1 = "abc", _2 = [ "abc", "" ] } ]

let test2 = assert : Regex/scan ~"^(.{0,4})(.*)" "abcd" !10 === [ { _1 = "abcd", _2 = [ "abcd", "" ] } ]

let test3 = assert : Regex/scan ~"^(.{0,4})(.*)" "abcde" !10 === [ { _1 = "abcde", _2 = [ "abcd", "e" ] } ]

let test4 = assert : Regex/scan ~"^(.{0,4})(.*)" "" !10 === ([] : List { _1 : Text, _2 : List Text })

let test5 = assert : Regex/scan ~"^(.{0,4})(.*)" "a" !10 === [ { _1 = "a", _2 = [ "a", "" ] } ]

let test6 = assert : Regex/scan ~"^(.{0,4})(.*)" "abcdefghij" !10 === [ { _1 = "abcdefghij", _2 = [ "abcd", "efghij" ] } ]

let test7 = assert : Regex/scan ~"." "abcde" !10 ===
  [ { _1 = "a", _2 = [] : List Text }
  , { _1 = "b", _2 = [] : List Text }
  , { _1 = "c", _2 = [] : List Text }
  , { _1 = "d", _2 = [] : List Text }
  , { _1 = "e", _2 = [] : List Text }
  ]
let test8 = assert : Regex/split ~"\." "141.214.155.2" !10 === ["141","214","155","2"]
let test9 = assert : Regex/split ~"x" "abc" !10 === ["abc"]
let test10 = assert : Regex/parse "14" === Some ~"14"
let test11 = assert : Regex/parse "\\" === None Regex
let test12 = assert : Regex/parse "" === None Regex
let test13 = assert : Regex/scan ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" "141.214.155.2" !10 === [ { _1 = "141.214.155.2", _2 = [ "141", "214", "155", "2" ] } ]
let test14 = assert : Regex/scan ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" "141.214.155." !10 === ([] : List { _1 : Text, _2 : List Text })
let test15 = assert : Regex/match ~"xyz" "abc  xyzweb" === True
let test16 = assert : Regex/match ~"xyz" "abc  Xyzweb" === False
let test17 = assert : Regex/match ~"(?i)xyz" "abc  Xyzweb" === True
let test18 = assert : Regex/toText ~"xyz" === "xyz"
let test19 = assert : Regex/split ~"\." "1.2.3.4.555." !10 === [ "1", "2", "3", "4", "555", "" ]
let test20 = assert : Regex/parse "\\d+" === Some ~"\d+"
let test21 = assert : Regex/parse "\\" === None Regex

let test22 = assert : Regex/parse "" === None Regex -- dont allow empty strings for regex else loop

let test23 =
  let xs = Regex/split ~"\." "141.213.111.13" !10
  in assert : pp.List.map Text (Optional Natural) Natural/parse xs === [ Some 141, Some 213, Some 111, Some 13 ]

let test24 =
  let xs = Regex/split ~"\." "141.213.111.13" !10
  in assert : pp.List.map Text Natural (\(x : Text) -> merge { None = PVoid/error ^^"Natural/parse failed unexpectedly in test24" Natural, Some = \(n : Natural) -> n } (Natural/parse x)) xs
  ===
  [ 141, 213, 111, 13 ]

let test25 = assert : Regex/match ~"sdf" "xyz sdfwsdf " === True
let test26 = assert : Regex/match ~"^sdf$" "sdf " === False
let test27 = assert : Regex/match ~"^sdf$" "sdf" === True
let test28 = assert : Regex/match ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" "sdf " === False
let test29 = assert : Regex/match ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" "1.2.3.4" === True
let test30 = assert : Regex/match ~"^(\d+)\.(\d+)\.(\d+)\.(\d+)$" "1.2.3.4.5" === False

let test31 = assert : Regex/scan ~"abc" "abc def" !10 === [ { _1 = "abc", _2 = [] : List Text } ]
let test32 = assert : Regex/scan ~"(abc)" "abc" !10 === [ { _1 = "abc", _2 = [ "abc" ] } ]
let test33 = assert : Regex/scan ~"(abd)" "abc" !10 === ([] : List { _1 : Text, _2 : List Text })

let test34 = assert : Regex/parse "^\\d+$" === Some ~"^\d+$"
let test35 = assert : Regex/parse "^\\d+$\\" === None Regex
let test36 = assert : Regex/toText ~"^\d+$" === "^\\d+$"
let test37 = assert : Regex/parse "a[]" === None Regex
let test38 = assert : Regex/parse "" === None Regex

let test39 = assert : Regex/scan ~"(\d+)\." "1.2.3.4" !10 ===
              [ { _1 = "1.", _2 = [ "1" ] }
              , { _1 = "2.", _2 = [ "2" ] }
              , { _1 = "3.", _2 = [ "3" ] }
              ]

let test40 = assert : scanFsts ~"(\d+)\." "1.2.3.4" === ["1.","2.","3."]
let test41 = assert : scanSnds ~"(\d+)\." "1.2.3.4" === [["1"],["2"],["3"]]

-- test infinite loop on scan
let test42 = assert : Regex/scan ~"(.?)*" "xyz" !15 === ([ {_1 = "xyz", _2 = [""] } ] # pp.List.replicate 14 { _1 : Text, _2 : List Text } { _1 = "", _2 = [ "" ] })

-- test41a works?
-- let test41 = assert : Regex/scan ~"(.?)*" "xyz" === ([ {_1 = "xyz", _2 = [""] } ] # pp.List.replicate 99 { _1 : Text, _2 : List Text } { _1 = "", _2 = [ "" ] })

-- test infinite loop on split
let test43 = assert : Regex/split ~".?" "xyz" !27 === pp.List.replicate 27 Text ""

let test44 = assert : Regex/replace ~"\d+" "888" "121.131.111" === "888.888.888"
let test45 = assert : Regex/replix ~"\d+" (\(a : Text) -> "(" ++ a ++ ")") "abc123def9x" === "abc(123)def(9)x"
let test46 = assert : Regex/replix ~"\d+" (\(a : Text) -> "(" ++ a ++ ")") "abcdef" === "abcdef"
let test47 = assert : Regex/replix ~"\d+" (\(a : Text) -> "(" ++ a ++ ")") "" === ""


let test48 = assert : Regex/replace ~"\d+" "hello" "abc1def2" === "abchellodefhello"

let test49 = assert : Regex/replix ~"\d+" (\(x : Text) -> "(" ++ x ++ ")") "abc1def2" === "abc(1)def(2)"

let test50 = assert : Regex/replix ~"\d+" (\(x : Text) -> "()") "abc1def2" === "abc()def()"

let test51 = assert : Regex/scan ~"\"|(')" "a\"b''c" !100 ===
  [ { _1 = "\"", _2 = [] : List Text }
  , { _1 = "'", _2 = [ "'" ] }
  , { _1 = "'", _2 = [ "'" ] }
  ]

let test52 = assert : pp.List.null Text (pp.List.filter Text (\(a : Text) -> Regex/match ~"(?i)sql" a) (Regex/split ~";" ("sqlpathexists;" ++ env:Path as Text ? "sqlpathmissing") !1000)) === False
let test53 = assert : pp.List.null Text (pp.List.filter Text (\(a : Text) -> Regex/match ~"(?i)sql" a) (Regex/split ~";" ("sqlpathexists;" ++ env:Pathxx as Text ? "sqlpathmissing") !1000)) === False

let test54 = assert : scan ~"\d+" "123.111.2.4"
 ===
    [ { _1 = "123", _2 = [] : List Text }
    , { _1 = "111", _2 = [] : List Text }
    , { _1 = "2", _2 = [] : List Text }
    , { _1 = "4", _2 = [] : List Text }
    ]

let test55 = assert : scanFsts ~"\d+" "123.111.2.4"
 === [ "123", "111", "2", "4" ]


let test56 = assert :  split ~"\." "123.111.2.4" === [ "123", "111", "2", "4" ]

let test57 = assert : Regex/replix ~"."
     (\(x : Text) -> let a = Text/unpack x
                     let b = pp.List.map Natural Natural (\(c : Natural) -> c + 1) a
                     in Text/pack b) "abc" === "bcd"

let test58 = assert : words "   abc     def ghi A%12 $$# " === ["abc","def","ghi","A%12","$$#"]
let test59 = assert : let nl = Text/pack [10] in lines " abc${nl}xy${nl} ${nl}${nl}" === [ " abc", "xy", " ", "", "" ]
let test60 = assert : let nl = Text/pack [10] in lines (" abc" ++ nl ++ "xy" ++ nl ++ " " ++ nl ++ nl) === [ " abc", "xy", " ", "", "" ]

-- testing parsing
let test61 =
   let f = \(r : Regex) -> \(s : Regex) -> { _1 = r, _2 = s }
   in assert : f ~"abc" ~"def" === { _1 = ~"abc", _2 = ~"def" }


let test62 = assert : scan ip4RE "123.1.11.23" === [ { _1 = "123.1.11.23", _2 = [ "123", "1", "11", "23" ] } ]

let test63 = assert : scan ip4RE "123.1.11.2x3" === ([] : List { _1 : Text, _2 : List Text })

let test64 = assert : scan ip4RE "123.1.11.256" === ([] : List { _1 : Text, _2 : List Text })

let test65 = assert : scan ip4RE "123.1.11.256.12" === ([] : List { _1 : Text, _2 : List Text })

let test66 = assert : scan ip4RE "123.1.11.256." === ([] : List { _1 : Text, _2 : List Text })

let test67 = assert : ip4Parse4 "123.22.12.11"
===
[ 123, 22, 12, 11 ]

let test68 = assert : ip4Parse4 "99.255.110.123"
===
[ 99, 255, 110, 123 ]

let test69 = assert : ip4Parse4 "299.255.110.123"
===
([] : List Natural)

let test70 = assert : ip4Parse4ALT "123.22.12.11"
===
Some ~[ 123, 22, 12, 11 ]

let test71 = assert : ip4Parse4ALT "123.22.12.256"
===
None (ListFixed !!4 Natural)

let test71 = assert : pp.List.map Text Text Text/toUpper (words "asf\nduDe aBc  !!! ")
===
[ "ASF", "DUDE", "ABC", "!!!" ]

in {
, scanFsts
, scanSnds
, scanSndsOne
, ScanT0
, ScanT
, scan
, split
, words
, lines
, ip4RE
, ip4Parse4
, ip4Parse4ALT
}

{-
> :let a = http://worldtimeapi.org/api/ip using [ { mapKey = "User-Agent", mapValue = "Dhall" } ] as Text

> a
"{\"week_number\":7,\"utc_offset\":\"-05:00\",\"utc_datetime\":\"2020-02-12T20:27:30.067413+00:00\",\"unixtime\":1581539250,\"timezone\":\"America/Detroit\",\"raw_offset\":-18000,\"dst_until\":null,\"dst_offset\":0,\"dst_from\":null,\"dst\":false,\"day_of_year\":43,\"day_of_week\":3,\"datetime\":\"2020-02-12T15:27:30.067413-05:00\",\"client_ip\":\"141.214.125.15\",\"abbreviation\":\"EST\"}"

> x.pp.Optional.map Text (Optional DateTime) (\(t : Text) -> DateTime/parse t) (List/head Text (x.pp.List.concat Text  (scanSnds ~"\"datetime\":\"([^\.]+)" a)))
Some (Some ^2020-02-12T15:27:30)

> scan ~"^.*?\s\K|(\w+)" "abb cde fgg"

[ { _1 = "", _2 = [] : List Text }
, { _1 = "cde", _2 = [ "cde" ] }
, { _1 = "fgg", _2 = [ "fgg" ] }
]

> scan ~"^.*?\s\K|(\w+)" "abb cde fgg dd dd ff easfd"

[ { _1 = "", _2 = [] : List Text }
, { _1 = "cde", _2 = [ "cde" ] }
, { _1 = "fgg", _2 = [ "fgg" ] }
, { _1 = "dd", _2 = [ "dd" ] }
, { _1 = "dd", _2 = [ "dd" ] }
, { _1 = "ff", _2 = [ "ff" ] }
, { _1 = "easfd", _2 = [ "easfd" ] }
]

> scan ~"(?:\G(?!\A)|^one) (\S+)" "abb cde fgg dd dd ff easfd"

[] : List { _1 : Text, _2 : List Text }

> scan ~"(?:\G(?!\A)|^one) (\S+)" "one cde fgg dd dd ff easfd"

[ { _1 = "one cde", _2 = [ "cde" ] }
, { _1 = " fgg", _2 = [ "fgg" ] }
, { _1 = " dd", _2 = [ "dd" ] }
, { _1 = " dd", _2 = [ "dd" ] }
, { _1 = " ff", _2 = [ "ff" ] }
, { _1 = " easfd", _2 = [ "easfd" ] }
]

> scan ~"(?:\G(?!\A)) (\S+)" "cde fgg dd dd ff easfd"

[] : List { _1 : Text, _2 : List Text }

> scan ~"(?:\G(?!\A)|^\w+) (\S+)" "one cde fgg dd dd ff easfd"

[ { _1 = "one cde", _2 = [ "cde" ] }
, { _1 = " fgg", _2 = [ "fgg" ] }
, { _1 = " dd", _2 = [ "dd" ] }
, { _1 = " dd", _2 = [ "dd" ] }
, { _1 = " ff", _2 = [ "ff" ] }
, { _1 = " easfd", _2 = [ "easfd" ] }
]

> scan ~"\G(\.\d+){1,5}" "1.2.3.4.5"

[] : List { _1 : Text, _2 : List Text }

> scan ~"(\.\d+)+" "1.2.3.4.5"

[ { _1 = ".2.3.4.5", _2 = [ ".5" ] } ]

> scan ~"\G(\.\d+)+" "1.2.3.4.5"

[] : List { _1 : Text, _2 : List Text }

> scan ~"(\.\d+)+\G" "1.2.3.4.5"

[] : List { _1 : Text, _2 : List Text }

> scan ~"(?:(simple).*?)+" "this is a simple thing simple dude simple"

[ { _1 = "simple", _2 = [ "simple" ] }
, { _1 = "simple", _2 = [ "simple" ] }
, { _1 = "simple", _2 = [ "simple" ] }
]

> scan ~"(?:(\w+).*?)+" "this is a simple thing simple dude simple"

[ { _1 = "this", _2 = [ "this" ] }
, { _1 = "is", _2 = [ "is" ] }
, { _1 = "a", _2 = [ "a" ] }
, { _1 = "simple", _2 = [ "simple" ] }
, { _1 = "thing", _2 = [ "thing" ] }
, { _1 = "simple", _2 = [ "simple" ] }
, { _1 = "dude", _2 = [ "dude" ] }
, { _1 = "simple", _2 = [ "simple" ] }
]

> scan ~"(?:(\d+).*?)+" "1.2.3.4.5"

[ { _1 = "1", _2 = [ "1" ] }
, { _1 = "2", _2 = [ "2" ] }
, { _1 = "3", _2 = [ "3" ] }
, { _1 = "4", _2 = [ "4" ] }
, { _1 = "5", _2 = [ "5" ] }
]

(?:^one|(?<!\A)\G).*?\K\S+

Sat 03 11:07:35 C:\work\dh>echo Regex/replix ~"\d+" (\(a : Text) -^^^> "(" ++ a ++ ")") ^"abc123def9x^" | dhall normalize
"abc(123)def(9)x"

Sat 03 11:07:42 C:\work\dh>echo Regex/replix ~"\d+" (\(a : Text) -^^^> "(" ++ a ++ ")")  | dhall normalize
Regex/replix ~\d+ (\(a : Text) -> "(${a})")

Sat 03 11:08:07 C:\work\dh>echo Regex/replix ~"\d+" (\(a : Text) -^^^> "(" ++ a ++ ")")  | dhall resolve
Regex/replix ~\d+ (\(a : Text) -> "(" ++ a ++ ")")

Sat 03 11:08:33 C:\work\dh>echo Regex/replix ~"\d+" (\(a : Text) -^^^> "(" ++ a ++ ")")  | dhall type
Text -> Text
-}
