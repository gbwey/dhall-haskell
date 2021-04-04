let test1 = assert : Double/parse "14.3" === Some 14.3
let test2 = assert : Double/parse "+14.3" === Some 14.3
let test3 = assert : Double/parse "-14.3" === Some -14.3
-- +0.0 and 0.0 are different from -0.0
let test4 = assert : Double/parse "-0.0" === Some -0.0
let test5 = assert : Double/parse "+0.0" === Some +0.0
let test6 = assert : Double/parse "0.0" === Some +0.0
let test7 = assert : Double/parse "1" === None Double
let test8 = assert : Double/parse "+99" === None Double
let test9 = assert : Double/parse "-1" === None Double
let test10 = assert : Double/parse "+0" === None Double

let test11 = assert : -0.0 === -0.0
let test12 = assert : +0.0 === +0.0
let test13 = assert : +0.0 === 0.0
let test14 = assert : 0.0 === +0.0
let test15 = assert : 0.0 === 0.0

let f = \(t : Type) -> \(d : Double) -> \(x : t) -> True : Bool

in { f }