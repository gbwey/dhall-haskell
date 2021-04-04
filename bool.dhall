let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let sr = ./semiring.dhall
let oo = ./ordering.dhall

let bool =
    \(a : Type)
 -> \(t : a)
 -> \(f : a)
 -> \(b : Bool)
 -> if b then t else f
    : a

let compare = oo.compareBool

-- list of predicates
let ors =
    \(a : Type)
 -> \(ps : List (a -> Bool))
 -> \(x : a)
 -> List/fold (a -> Bool) ps Bool (\(p : a -> Bool) -> \(b : Bool) -> b || p x) False
   : Bool

let ands =
    \(a : Type)
 -> \(ps : List (a -> Bool))
 -> \(x : a)
 -> List/fold (a -> Bool) ps Bool (\(p : a -> Bool) -> \(b : Bool) -> b && p x) True
   : Bool

let boolTest = \(f : Bool -> Bool -> Bool) ->
  let f = \(a : Bool) -> \(b : Bool) -> { _1 = a, _2 = b, _3 = f a b }
  in [
     , f False False
     , f False True
     , f True False
     , f True True
     ]

let xor =
     \(a : Bool)
  -> \(b : Bool)
  -> a != b
     : Bool

let imply =
     \(a : Bool)
  -> \(b : Bool)
  -> a == False || b
    : Bool

let numInstance =
  { multiply = \(x : Bool) -> \(y : Bool) -> x && y
  , add = \(x : Bool) -> \(y : Bool) -> x || y
  , zero = False
  , one = True
  , fromNatural = \(x : Natural) -> Natural/isZero (Integer/clamp (NonZero/mod (Natural/toInteger x) !2))
  }
  : sr.Type Bool

let enumerate = sr.enumerate Bool numInstance
 {-
    \(n : Natural)
 -> let t = { index : Bool, ret : List Bool }
    let r = Natural/fold
         n
         t
         (\(z : t) -> { index = z.index == False, ret = z.ret # [z.index] })
         { index = False, ret = [] : List Bool }
    in r.ret
    : List Bool
-}

let test1 = assert : boolTest imply ===
  [ { _1 = False, _2 = False, _3 = True  }
  , { _1 = False, _2 = True,  _3 = True  }
  , { _1 = True,  _2 = False, _3 = False }
  , { _1 = True,  _2 = True,  _3 = True  }
  ]

let test2 = assert : ands Natural [pp.Natural.greaterThan 7, pp.Natural.lessThan 3] 4 === True
let test3 = assert : ands Natural [pp.Natural.greaterThan 7, pp.Natural.lessThan 3] 7 === False
let test4 = assert : ors Natural [pp.Natural.greaterThan 7, pp.Natural.lessThan 3, pp.Natural.greaterThan 20, pp.Natural.lessThan 17] 18 === True
let test5 = assert : ors Natural [pp.Natural.lessThan 3, pp.Natural.lessThan 17, pp.Natural.equal 2] 4 === True
let test6 = assert : ors Natural [pp.Natural.lessThan 3, pp.Natural.lessThan 17, pp.Natural.equal 2] 3 === False
let test7 = assert : ors Natural [pp.Natural.lessThan 3, pp.Natural.lessThan 17, pp.Natural.equal 2] 1 === False
let test8 = assert : ors Natural [pp.Natural.greaterThan 7, pp.Natural.equal 3, pp.Natural.greaterThan 20, pp.Natural.equal 21] 22 === False

let test9 = assert : enumerate 5 === [False,True,True,True,True]

in {
bool,
boolTest,
imply,
xor,
ors,
ands,
numInstance,
enumerate,
compare
}
