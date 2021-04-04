-- cant eta reduce on merge but can on 'either'
-- use let t = Either aa bb  to make life easier
--let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let oo = ./ordering.dhall

let Either : forall (a : Type) -> forall (b : Type) -> Type =
    \(a : Type)
 -> \(b : Type)
 -> < Left : a | Right : b >

let def =
   \(a : Type)
-> \(b: Type)
-> \(b1 : Bool)
-> \(b2 : Bool)
->  { Left = \(_ : a) -> b1
    , Right = \(_ : b) -> b2
    }

let mkLeft =
    \(a : Type)
 -> \(b : Type)
 -> \(x : a)
 -> (Either a b).Left x
    : Either a b

let mkRight =
    \(a : Type)
 -> \(b : Type)
 -> \(y : b)
 -> (Either a b).Right y
    : Either a b

-- fold
let either =
     \(a : Type)
  -> \(b : Type)
  -> \(c : Type)
  -> \(f : a -> c)
  -> \(g : b -> c)
  -> \(lr : Either a b)
  -> merge { Left = f, Right = g } lr
   : c

let mappend =
     \(a : Type)
  -> \(b : Type)
  -> \(lr1 : Either a b)
  -> \(lr2 : Either a b)
  -> let t = Either a b
     in merge
       { Left = \(_ : a) -> merge
                            { Left = \(_ : a) -> lr1
                            , Right = \(_ : b) -> lr2
                            } lr2
       , Right = \(_ : b) -> lr1
       } lr1
     : t

let fromLeft =
     \(a : Type)
  -> \(b : Type)
  -> \(x : a)
  -> either a b a (\(w : a) -> w) (\(_ : b) -> x)
   : Either a b -> a

let fromRight =
     \(a : Type)
  -> \(b : Type)
  -> \(y : b)
  -> either a b b (\(_ : a) -> y) (\(w : b) -> w)
   : Either a b -> b

let swap =
     \(a : Type)
  -> \(b : Type)
  -> \(lr : Either a b)
  -> let t = Either b a
     in merge { Left = t.Right, Right = t.Left } lr
: t

let isLeft =
     \(a : Type)
  -> \(b : Type)
  -> \(lr : Either a b)
  -> merge (def a b True False) lr
   : Bool

let isRight =
     \(a : Type)
  -> \(b : Type)
  -> \(lr : Either a b)
  -> merge (def a b False True) lr
   : Bool

let fromLeftProof  =
     \(a : Type)
  -> \(b : Type)
  -> \(lr : Either a b)
  -> \(prf : Proof/fromBool ^^"either.dhall: fromLeftProof found right not left"
        (isLeft a b lr)
      )
  -> merge { Left = \(x : a) -> x, Right = \(_ : b) -> PVoid/undefined a } lr
   : a

let fromRightProof  =
     \(a : Type)
  -> \(b : Type)
  -> \(lr : Either a b)
  -> \(prf : Proof/fromBool ^^"either.dhall: fromRightProof found left not right"
        (isRight a b lr)
      )
  -> merge { Left = \(_ : a) -> PVoid/undefined b, Right = \(x : b) -> x } lr
   : b

let left =
     \(a : Type)
  -> \(b : Type)
  -> \(aa : Type)
  -> \(f : a -> aa)
  -> let t = Either aa b -- much easier
     in either
          a
          b
          t
          (\(w : a) -> t.Left (f w))
          t.Right
             : Either a b -> t

let right =
     \(a : Type)
  -> \(b : Type)
  -> \(bb : Type)
  -> \(f : b -> bb)
  -> let t = Either a bb
     in either
          a
          b
          t
          t.Left
          (\(w : b) -> t.Right (f w))
             : Either a b -> t

let both =
     \(a : Type)
  -> \(b : Type)
  -> \(aa : Type)
  -> \(bb : Type)
  -> \(f : a -> aa)
  -> \(g : b -> bb)
  -> let t = Either aa bb -- much easier
     in either
          a
          b
          t
          (\(w : a) -> t.Left (f w))
          (\(w : b) -> t.Right (g w))
        : Either a b -> t


let partitionEithers =
    \(a : Type)
 -> \(b : Type)
 -> \(xs : List (Either a b))
 -> let t = { _1 : List a, _2 : List b }
    in List/fold
        (Either a b)
        xs
        t
        (\(lr : Either a b)
           -> \(ys : t)
           -> merge { Left  = \(x : a) -> ys // { _1 = ys._1 # [x] }
                    , Right = \(x : b) -> ys // { _2 = ys._2 # [x] }
                    } lr)
        { _1 = [] : List a, _2  = [] : List b }
  : t

let compare =
    \(a : Type)
 -> \(b : Type)
 -> \(cmpa : a -> a -> oo.Ordering)
 -> \(cmpb : b -> b -> oo.Ordering)
 -> \(lr1 : Either a b)
 -> \(lr2 : Either a b)
 -> merge {
    , Left = \(x : a) -> merge { Left = cmpa x, Right = \(_ : b) -> oo.LT } lr2
    , Right = \(x : b) -> merge { Right = cmpb x, Left = \(_ : a) -> oo.GT } lr2
    } lr1
    : oo.Ordering

let test1 = assert : either Natural NonZero Integer Natural/toInteger (\(w : NonZero) -> Natural/toInteger (NonZero/toNatural w)) ((Either Natural NonZero).Left 10) === +10
let test2 = assert : swap Natural NonZero ((Either Natural NonZero).Left 10) === ((Either NonZero Natural).Right 10)
let test3 = assert : swap NonZero Natural (swap Natural NonZero ((Either Natural NonZero).Left 10)) === ((Either Natural NonZero).Left 10)
let test4 = assert : isLeft Natural NonZero ((Either Natural NonZero).Left 10) === True
let test5 = assert : isRight Natural NonZero ((Either Natural NonZero).Left 10) === False
let test6 = assert : both Integer Bool Integer Bool (Integer/add +99) (\(b : Bool) -> b == False) ((Either Integer Bool).Left +10) === ((Either Integer Bool).Left +109)
let test7 = assert : both Integer Bool Integer Bool (Integer/add +99) (\(b : Bool) -> b == False) ((Either Integer Bool).Right True) === ((Either Integer Bool).Right False)
let test8 = assert : partitionEithers Integer Bool [mkLeft Integer Bool +10, mkRight Integer Bool True] === { _1 = [+10], _2 = [True] }
let test9 = assert : mappend (List Natural) Text (mkRight (List Natural) Text "xxx") (mkRight (List Natural) Text "yyy") === < Left : List Natural | Right : Text >.Right "xxx"
let test10 = assert : mappend (List Natural) Text (mkRight (List Natural) Text "xxx") (mkLeft (List Natural) Text [1,2,3]) === < Left : List Natural | Right : Text >.Right "xxx"

let test11 = assert : fromLeft Natural Bool 123 (mkLeft Natural Bool 999) === 999
let test12 = assert : fromLeft Natural Bool 123 (mkRight Natural Bool True) === 123
let test13 = assert : fromRight Bool Natural 123 (mkRight Bool Natural 999) === 999
let test14 = assert : fromRight Bool Natural 123 (mkLeft Bool Natural True) === 123

let test15 = assert : fromLeftProof Natural Bool (mkLeft Natural Bool 999) Prf === 999
--let test10 = assert : fromLeftProof Natural Bool (mkRight Natural Bool True) Prf === 123
let test16 = assert : fromRightProof Bool Natural (mkRight Bool Natural 999) Prf === 999
--let test10 = assert : fromRightProof Bool Natural (mkLeft Bool Natural True) Prf === 123

in {
Either,
mkLeft,
mkRight,
either,
fromLeftProof,
fromRightProof,
fromLeft,
fromRight,
isLeft,
isRight,
swap,
left,
right,
both,
partitionEithers,
mappend,
compare
}

-- named vs named union vars
{- different: the second one requires the { z = .. }
> < Left : Natural | Right : Bool >. Left 10
< Left : Natural | Right : Bool >.Left 10

> < Left : { z : Natural } | Right : Bool >. Left { z = 10 }
< Left : { z : Natural } | Right : Bool >.Left { z = 10 }

-}
