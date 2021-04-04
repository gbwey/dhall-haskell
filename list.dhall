let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude
let nn = ./natural.dhall
let oo = ./ordering.dhall
let ss = ./sort.dhall

let splitAt =
    \(a : Type)
 -> \(n : Natural)
 -> \(xs : List a)
 -> let t = { index : Natural, _1 : List a, _2 : List a }
    let len = List/length a xs
    let n0 = Natural/subtract n len
    let ret =
      List/fold
         a
         xs
         t
         (    \(x : a)
           -> \(z : t)
           -> { index = z.index + 1 }
               /\
              (if pp.Natural.lessThan z.index n0
              then { _1 = z._1, _2 = [x] # z._2 }
              else { _1 = [x] # z._1, _2 = z._2 })
         )
         { index = 0, _1 = [] : List a, _2 = [] : List a }
    in ret.{_1,_2}

{-
let splits =
    \(a : Type)
 -> \(xs : List a)
 -> let t = { _1 : List a, _2 : List a }
    in List/fold
      Natural
      (pp.Natural.enumerate (Natural/subtract 1 (List/length a xs)))
      (List t)
      (\(n : Natural) -> \(z : List t) -> [splitAt a (n + 1) xs] # z)
      ([] : List t)
      : List t
-}
let splits =
    \(a : Type)
 -> \(xs : List a)
 -> let t = { _1 : List a, _2 : List a }
    in List/build
         t
         (   \(list : Type)
          -> \(cons : t -> list -> list)
          -> \(nil : list)
          -> List/fold
               Natural
               (pp.Natural.enumerate (Natural/subtract 1 (List/length a xs)))
               list
               (\(n : Natural) -> \(z : list) -> cons (splitAt a (n + 1) xs) z)
               nil
         )
      : List t

let cons =
   \(a : Type)
   -> \(x : a)
   -> \(xs : List a)
   -> [x] # xs : List a

let flipCons =
   \(a : Type)
   -> \(xs : List a)
   -> \(x : a)
   -> [x] # xs : List a

let snoc =
   \(a : Type)
   -> \(xs : List a)
   -> \(x : a)
   -> xs # [x] : List a

let flipSnoc =
   \(a : Type)
   -> \(x : a)
   -> \(xs : List a)
   -> xs # [x] : List a

let mempty =
  \(a : Type)
  -> ([] : List a)
   : List a

let mappend =
    \(a : Type)
 -> \(xs : List a)
 -> \(ys : List a)
 -> xs # ys
   : List a

let mconcat =
    \(a : Type)
 -> \(xs : List (List a))
 -> List/fold
     (List a)
     xs
     (List a)
     (\(x : List a) -> \(y : List a) -> x # y)
     ([] : List a)
    : List a

{-
let traverse =
     \(a : Type)
  -> \(b : Type)
  -> \(xs : List (List a))
  -> \(f : List a -> List b)
  -> List/fold
      (List a)
      xs
      (List (List b))
      (   \(x : List a)
       -> \(z : List (List b))
       -> [f x] # z
      )
      ([] : List (List b))
      : List (List b)
-}
let traverse =
     \(a : Type)
  -> \(b : Type)
  -> \(xs : List (List a))
  -> \(f : List a -> List b)
  -> List/build
       (List b)
       (   \(list : Type)
        -> \(cons : List b -> list -> list)
        -> \(nil : list)
        -> List/fold
            (List a)
            xs
            list
            (   \(x : List a)
            -> \(z : list)
            -> cons (f x) z
            )
            nil
       )
      : List (List b)

let fill =
  \(a : Type)
 -> \(b : Type)
 -> \(left : Bool)
 -> \(xs : List a)
 -> \(ys : List b)
 -> \(aDef : a)
 -> \(bDef : b)
 -> let l1 = List/length a xs
    let l2 = List/length b ys
    in merge
    {
    , LT = let aa = pp.List.replicate (Natural/subtract l1 l2) a aDef
           in { _1 = if left then aa # xs else xs # aa, _2 = ys }
    , EQ = { _1 = xs, _2 = ys }
    , GT = let bb = pp.List.replicate (Natural/subtract l2 l1) b bDef
           in { _1 = xs, _2 = if left then bb # ys else ys # bb }
    } (oo.compareNatural l1 l2)
    : { _1 : List a, _2 : List b }

let cartesianWith =
    \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b -> c)
 -> \(xs : List a)
 -> \(ys : List b)
 -> pp.List.map a (List c) (\(x : a) -> pp.List.map b c (f x) ys) xs
    : List (List c)

let cartesian =
    \(a : Type)
 -> \(b : Type)
 -> \(xs : List a)
 -> \(ys : List b)
 -> let t = { _1 : a, _2 : b }
    in cartesianWith a b t (\(x : a) -> \(y : b) -> { _1 = x, _2 = y }) xs ys
   : List (List t)

let zipWithTrunc =
    \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b -> c)
 -> \(xs : List a)
 -> \(ys : List b)
 -> let t = List c
    let s = { _1 : List b, _2 : t }
    let g = \(z : s) -> \(x : a) ->
               merge
                 { None = z
                 , Some = \(y : b) -> { _1 = pp.List.drop 1 b z._1, _2 = z._2 # [ f x y ] }
                 } (List/head b z._1)
    let ret =
      ss.foldl
      a
      xs
      { _1 : List b, _2 : t }
      g
      { _1 = ys, _2 = [] : t }
    in ret._2
    : t

let zipTrunc =
    \(a : Type)
 -> \(b : Type)
 -> \(xs : List a)
 -> \(ys : List b)
 -> let t = { _1 : a, _2 : b }
    in zipWithTrunc a b t (\(x : a) -> \(y : b) -> { _1 = x, _2 = y }) xs ys
   : List t

let zipWithProof =
    \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(f : a -> b -> c)
 -> \(xs : List a)
 -> \(ys : List b)
 -> \(prf : Proof/fromBool ^^"size of the lists are not the same"
       (pp.Natural.equal (List/length a xs) (List/length b ys))
     )
 -> zipWithTrunc a b c f xs ys
  : List c

let zipProof =
    \(a : Type)
 -> \(b : Type)
 -> \(xs : List a)
 -> \(ys : List b)
 -> \(prf : Proof/fromBool ^^"size of the lists are not the same"
       (pp.Natural.equal (List/length a xs) (List/length b ys))
     )
 -> zipTrunc a b xs ys

-- skip the empty element
let tails =
    \(a : Type)
 -> \(xs : List a)
 -> let t = { _1 : List a, _2 : List (List a) }
    let ret = Natural/fold
      (List/length a xs)
      t
      (   \(z : t)
       -> { _1 = pp.List.drop 1 a z._1
          , _2 = z._2 # [z._1]
          }
      )
      { _1 = xs, _2 = [] : List (List a) }
    in ret._2
{-
let inits =
    \(a : Type)
 -> \(xs : List a)
 -> let t = { _1 : List a, _2 : List (List a) }
    let ret = Natural/fold
      (List/length a xs)
      t
      (   \(z : t)
       -> { _1 = pp.List.take (Natural/subtract 1 (List/length a z._1)) a z._1
          , _2 = [z._1] # z._2
          }
      )
      { _1 = xs, _2 = [] : List (List a) }
    in ret._2
-}
let inits =
    \(a : Type)
 -> \(xs : List a)
 -> List/build
      (List a)
      (   \(list : Type)
       -> \(cons : List a -> list -> list)
       -> \(nil : list)
       -> let t = { _1 : List a, _2 : list }
          let ret = Natural/fold
            (List/length a xs)
            t
            (   \(z : t)
            -> { _1 = pp.List.take (Natural/subtract 1 (List/length a z._1)) a z._1
               , _2 = cons z._1 z._2
               }
            )
            { _1 = xs, _2 = nil }
          in ret._2
      ) : List (List a)

let pairsWith =
    \(a : Type)
 -> \(b : Type)
 -> \(f : a -> a -> b)
 -> \(xs : List a)
 -> zipWithTrunc a a b f xs (pp.List.drop 1 a xs)
  : List b

let pairs =
    \(a : Type)
 -> \(xs : List a)
 -> zipTrunc a a xs (pp.List.drop 1 a xs)
  : List { _1 : a, _2 : a }

let allEQ =
  pp.List.all oo.Ordering oo.isEQ
   : List oo.Ordering -> Bool

let allNE =
  pp.List.all oo.Ordering oo.isNE
   : List oo.Ordering -> Bool

let allLE =
  pp.List.all oo.Ordering oo.isLE
   : List oo.Ordering -> Bool

let allLT =
  pp.List.all oo.Ordering oo.isLT
   : List oo.Ordering -> Bool

let allGE =
  pp.List.all oo.Ordering oo.isGE
   : List oo.Ordering -> Bool

let allGT =
  pp.List.all oo.Ordering oo.isGT
   : List oo.Ordering -> Bool

let compareAdjacent =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> \(f : List oo.Ordering -> Bool)
 -> \(xs : List a)
 -> f (pairsWith a oo.Ordering cmp xs)
   : Bool

let equals =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> compareAdjacent a cmp allEQ
   : List a -> Bool

let notEquals =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> compareAdjacent a cmp allNE
   : List a -> Bool

let asc =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> compareAdjacent a cmp allLE
   : List a -> Bool

let ascStrict =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> compareAdjacent a cmp allLT
   : List a -> Bool

let desc =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> compareAdjacent a cmp allGE
   : List a -> Bool

let descStrict =
    \(a : Type)
 -> \(cmp: a -> a -> oo.Ordering)
 -> compareAdjacent a cmp allGT
   : List a -> Bool

let compare =
    \(a : Type)
 -> \(f : a -> a -> oo.Ordering)
 -> \(xs : List a)
 -> \(ys : List a)
 -> let t = { _1 : a, _2 : a}
    let g = \(w : t) -> f w._1 w._2
    let ret = oo.foldMap t oo.Ordering g oo.mempty oo.mappend (zipTrunc a a xs ys)
    in merge { LT = ret, GT = ret, EQ = oo.compareNatural (List/length a xs) (List/length a ys) } ret
    : oo.Ordering

-- same order of vars as List/fold
let scan =
   \(a : Type)
-> \(xs : List a)
-> \(b : Type)
-> \(f : a -> b -> b)
-> \(z : b)
-> List/build
      b
      (   \(list : Type)
       -> \(cons : b -> list -> list)
       -> \(nil : list)
       -> let t = { _1 : b, _2 : list }
          let r =
            List/fold
            a
            xs
            t
            (  \(x : a)
            -> \(y : t)
            -> let w = f x y._1
               in { _1 = w, _2 = cons y._1 y._2 }
            )
            { _1 = z, _2 = nil }
         in cons r._1 r._2
      )
    : List b

let scanl =
   \(a : Type)
-> \(xs : List a)
-> \(b : Type)
-> \(f : b -> a -> b)
-> \(z : b)
-> let t = { _1 : b, _2 : List b }
   let r =
    ss.foldl
    a
    xs
    t
    (\(y : t) -> \(x : a) -> let w = f y._1 x in { _1 = w, _2 = y._2 # [y._1] })
    { _1 = z, _2 = [] : List b }
   in r._2 # [r._1]
    : List b

let takeWhile =
   \(a : Type)
-> \(p : a -> Bool)
-> \(xs : List a)
-> List/fold
    a
    xs
    (List a -> List a)
    (   \(x : a)
     -> \(k : List a -> List a)
     -> \(v : List a)
     -> if p x then [x] # k v
        else []
        : List a
     )
    (pp.Function.identity (List a))
    ([] : List a)
    : List a

let dropWhile =
   \(a : Type)
-> \(p : a -> Bool)
-> \(xs : List a)
-> List/fold
    a
    xs
    (Bool -> List a)
    (   \(x : a)
     -> \(k : Bool -> List a)
     -> \(b : Bool)
     -> if b then [x] # k b
        else if p x then k b
             else [x] # k True
    )
    (\(w : Bool) -> [] : List a)
    False
    : List a

let span =
   \(a : Type)
-> \(p : a -> Bool)
-> \(xs : List a)
-> let t = { _1 : List a, _2 : List a }
   let s  = { _1 : Bool, _2 : t }
   in List/fold
    a
    xs
    (s -> t)
    (   \(x : a)
     -> \(k : s -> t)
     -> \(z : s)
     -> if p x && z._1 == False
        then k { _1 = z._1, _2 = { _1 = z._2._1 # [x], _2 = z._2._2 } }
        else k { _1 = True, _2 = { _1 = z._2._1, _2 = z._2._2 # [x] } }
    )
    (\(w : s) -> w._2)
    { _1 = False, _2 = { _1 = [] : List a, _2 = [] : List a } }
    : t

let break =
   \(a : Type)
-> \(p : a -> Bool)
-> span a (\(w : a) -> p w == False)
   : List a -> { _1 : List a, _2 : List a }

let itoList =
   \(a : Type)
-> \(xs : List a)
-> let s = List { _1 : Natural, _2 : a }
   let t = { _1 : Natural, _2 : s }
   let r =
     ss.foldl
     a
     xs
     t
     (   \(z : t)
      -> \(x : a)
      -> { _1 = 1 + z._1, _2 = z._2 # [ { _1 = z._1, _2 = x } ] }
     )
     { _1 = 0, _2 = [] : s }
   in r._2
   : s

-- need to integrate itoList within fold for one pass
let elemIndex =
    \(a : Type)
 -> \(xs : List a)
 -> \(p : a -> Bool)
 -> let s = { _1 : Natural, _2 : a }
    let t = Optional s
    in List/fold
         s
         (itoList a xs)
         (t -> t)
         (   \(a : s)
          -> \(k : t -> t)
          -> \(z : t)
          -> if p a._2 then Some a
             else k z
         )
         (pp.Function.identity t)
         (None s)
         : t

let index =
    \(a : Type)
 -> \(xs : List a)
 -> \(i : Natural)
 -> List/head a (pp.List.drop i a xs)
    : Optional a

let indexProof =
    \(a : Type)
 -> \(xs : List a)
 -> \(i : Natural)
 -> \(prf : Proof/fromBool ^^"list.dhall: indexProof is larger than size of list"
       (pp.Natural.lessThan i (List/length a xs))
     )
 -> merge { None = PVoid/undefined a, Some = \(x : a) -> x } (List/head a (pp.List.drop i a xs))
    : a

let elem =
    \(a : Type)
 -> \(xs : List a)
 -> \(p : a -> Bool)
 -> List/fold
      a
      xs
      Bool
      (   \(x : a)
       -> \(z : Bool)
       -> p x || z
      )
      False
      : Bool

let elemIndexProof =
    \(a : Type)
 -> \(xs : List a)
 -> \(p : a -> Bool)
 -> \(prf : Proof/fromBool ^^"list.dhall: elemIndexProof could not find element"
       (elem a xs p)
     )
 -> let s = { _1 : Natural, _2 : a }
    in List/fold
         s
         (itoList a xs)
         (s -> s)
         (   \(a : s)
          -> \(k : s -> s)
          -> \(z : s)
          -> if p a._2 then a
             else k z
         )
         (pp.Function.identity s)
         (PVoid/undefined s)
         : s

let allInList =
    \(a : Type)
 -> \(eq : a -> a -> Bool)
 -> \(needles : List a) -- check these to make sure they all members of haystack
 -> \(haystack : List a) -- these are valid
 -> pp.List.all a (\(t : a) -> elem a haystack (eq t)) needles
  : Bool

let allInListNat =
    \(needles : List Natural)
 -> \(haystack : List Natural)
 ->  allInList Natural pp.Natural.equal needles haystack
  : Bool

let allInListInt =
    \(needles : List Integer)
 -> \(haystack : List Integer)
 -> allInList Integer pp.Integer.equal needles haystack
  : Bool

let ip4Proof =
    \(i1 : Natural)
 -> \(i2 : Natural)
 -> \(i3 : Natural)
 -> \(i4 : Natural)
 -> Proof/fromBool
      ^^"list.dhall: ip4Proof one or of the octets >= 256"
     (pp.List.all Natural (pp.Natural.greaterThan 256) [i1,i2,i3,i4])

let ascNatProof =
    \(xs : List Natural)
 -> Proof/fromBool
      ^^"list.dhall: ascNatProof list is not in monotone ascending order"
     (asc Natural oo.compareNatural xs)

let singletonProof =
    \(a : Type)
 -> \(xs : List a)
 -> \(prf : Proof/fromBool ^^"expected only one value in the list"
        (pp.Natural.equal 1 (List/length a xs))
     )
 -> merge { None = PVoid/undefined a, Some = \(x : a) -> x } (List/head a xs)
   : a

let chunksOf =
    \(n : NonZero)
 -> \(step : NonZero)
 -> \(a : Type)
 -> \(xs : List a)
 -> let t = { _1 : List a, _2 : List (List a) }
    let step0 = NonZero/toNatural step
    let n0 = NonZero/toNatural n
    let ret =
      Natural/fold
        (nn.div (List/length a xs) step)
        t
        (\(z : t) -> let w = pp.List.take n0 a z._1
                     in { _1 = pp.List.drop step0 a z._1
                        , _2 = if pp.Natural.equal n0 (List/length a w) then z._2 # [w] else z._2
                        }
        )
        { _1 = xs, _2 = [] : List (List a) }
    in ret._2
    : List (List a)

let substring =
    \(a : Type)
 -> \(xs : List a)
 -> \(start : Natural)
 -> \(len : Natural)
 -> pp.List.take len a (pp.List.drop start a xs)
   : List a

let substringProof =
    \(a : Type)
 -> \(xs : List a)
 -> \(start : Natural)
 -> \(len : NonZero)
 -> \(prf1 : Proof/fromBool ^^"list.dhall: substringProof: start index must be less than the size of the list" (pp.Natural.lessThan start (List/length a xs)))
 -> \(prf2 : Proof/fromBool ^^"list.dhall: substringProof: length must be less than or equal to the size of the list" (pp.Natural.lessThanEqual (start + NonZero/toNatural len) (List/length a xs)))
 -> substring a xs start (NonZero/toNatural len)
   : List a

let indexReplace =
    \(a : Type)
 -> \(xs : List a)
 -> \(ns : List Natural)
 ->  List/fold
       Natural
       ns
       (List a)
       (   \(n : Natural)
        -> \(z : List a)
        -> pp.List.take 1 a (pp.List.drop n a xs) # z
       )
       ([] : List a)

let chooseProof =
    \(a : Type)
 -> \(k : Natural)
 -> \(xs : List a)
 -> \(prf : Proof/fromBool ^^"list.dhall: chooseProof: k must be less than the length xs"
      (pp.Natural.lessThan k (List/length a xs))
     )
 -> List/choose a k xs
   : List (List a)

let chooseFastList =
    \(n : Natural)
 -> pp.List.map Natural Natural (nn.chooseFast n) (nn.enumerate (n + 1))
 : List Natural

let subsequences =
    \(a : Type)
 -> \(xs : List a)
 -> List/fold
      Natural
      (pp.Natural.enumerate (1 + List/length a xs))
      (List (List a))
      (\(x : Natural) -> \(z : List (List a)) -> List/choose a x xs # z)
      ([] : List (List a))

let select =
    \(a : Type)
 -> \(xs : List a)
 -> let len = List/length a xs
    let ys = List/choose a (Natural/subtract 1 len) xs
    let zs = List/reverse a xs
    in zipTrunc a (List a) zs ys
    : List { _1 : a, _2 : List a }

let pascal =
    \(n : Natural)
 -> Natural/fold
      n
      (List Natural)
      (\(xs : List Natural) ->
         let t = { _1 : Natural, _2 : List Natural}
         let ret =
           List/fold
             Natural
             xs
             t
             (   \(x : Natural)
              -> \(z : t)
              -> { _1 = x, _2 = z._2 # [x + z._1] }
             )
             { _1 = 0, _2 = [] : List Natural }
          in ret._2 # [1]
      )
      [1]
      : List Natural

let fib =
    \(n : Natural)
 -> let t = { _1 : Natural, _2 : Natural, _3 : List Natural }
    let ret =
      Natural/fold
        n
        t
        (\(z : t) -> { _1 = z._2, _2 = z._1 + z._2, _3 = z._3 # [z._1] })
        { _1 = 0, _2 = 1, _3 = [] : List Natural }
     in ret._3
      : List Natural

let mapAmp =
    \(a : Type)
 -> \(b : Type)
 -> \(f : a -> b)
 -> \(xs : List a)
 -> let t = { _1 : a, _2 : b }
   in pp.List.map a t (\(x : a) -> { _1 = x, _2 = f x }) xs
 : List t

let sortBy =
    \(a : Type)
 -> \(cmp  : a -> a -> oo.Ordering)
 -> \(xs : List (List a))
 -> ss.sortBy (List a) (compare a cmp) xs
    : List (List a)

let test1 = assert : cons Natural 1 [2,3,4] === [1,2,3,4]
let test2 = assert : snoc Natural [2,3,4] 1 === [2,3,4,1]
let test3 = assert : flipSnoc Natural 1 [2,3,4] === [2,3,4,1]
let test4 = assert : flipCons Natural [2,3,4] 1 === [1,2,3,4]
let test5 = assert : mempty Integer === ([] : List Integer)
let test6 = assert : mappend Integer [+4,+3,-9] [+2,-3] === [+4,+3,-9,+2,-3]
let test7 = assert : mappend Integer [+4,+3,-9] (mempty Integer) === [+4,+3,-9]
let test8 = assert : mappend Integer (mempty Integer) [+2,-3] === [+2,-3]

let test9 = assert : splitAt Natural 99 [1,2,3] === { _1 = [1,2,3], _2 = [] : List Natural }
let test10 = assert : splitAt Natural 3 [1,2,3,4,5,6,7,8] === { _1 = [1,2,3], _2 = [4,5,6,7,8] }
let test11 = assert : splitAt Natural 0 [1,2,3,4,5,6,7,8] === { _1 = [] : List Natural, _2 = [1,2,3,4,5,6,7,8] }
let test12 = assert : splitAt Natural 3 ([] : List Natural) === { _1 = [] : List Natural, _2 = [] : List Natural }
let test13 = assert : splitAt Natural 3 [1,2] === { _1 = [1,2], _2 = [] : List Natural }

let test14 = assert : splitAt Natural 0 [1,2,3,4]
===
{ _1 = [] : List Natural, _2 = [ 1, 2, 3, 4 ] }

let test15 = assert : splitAt Natural 1 [1,2,3,4]
===
{ _1 = [ 1 ], _2 = [ 2, 3, 4 ] }

let test16 = assert : splitAt Natural 3 [1,2,3,4]
===
{ _1 = [ 1, 2, 3 ], _2 = [ 4 ] }

let test17 = assert : splitAt Natural 4 [1,2,3,4]
===
{ _1 = [ 1, 2, 3, 4 ], _2 = [] : List Natural }

let test18 = assert : splitAt Natural 5 [1,2,3,4]
===
{ _1 = [ 1, 2, 3, 4 ], _2 = [] : List Natural }


let test19 = assert : compare Natural oo.compareNatural [1,1] [1] === oo.GT
let test20 = assert : compare Natural oo.compareNatural [1] [1,1] === oo.LT
let test21 = assert : compare Natural oo.compareNatural [1,2] [1] === oo.GT
let test22 = assert : compare Natural oo.compareNatural [1] [1,2] === oo.LT
let test23 = assert : compare Natural oo.compareNatural [1,2,0] [1,2] === oo.GT
let test24 = assert : compare Natural oo.compareNatural [1,2] [1,2] === oo.EQ
let test25 = assert : compare Natural oo.compareNatural [2] [1,2] === oo.GT
let test26 = assert : compare Natural oo.compareNatural [1,20] [10,2] === oo.LT
let test27 = assert : compare Natural oo.compareNatural [1,20] [10] === oo.LT
let test28 = assert : compare Natural oo.compareNatural [10] [1,20] === oo.GT
let test29 = assert : compare Natural oo.compareNatural ([] : List Natural) [1,20] === oo.LT
let test30 = assert : compare Natural oo.compareNatural [1,20] ([] : List Natural) === oo.GT
let test31 = assert : compare Natural oo.compareNatural ([] : List Natural) ([] : List Natural) === oo.EQ

let test32 = assert : elemIndex Natural [10,99,13,3,4,7,21] (pp.Natural.equal 21) === Some { _1 = 6, _2 = 21 }
let test33 = assert : elemIndex Natural [10,99,13,3,4,7,21] (pp.Natural.equal 1) === None { _1 : Natural, _2 : Natural }
let test34 = assert : elemIndex Natural [10,99,13,3,4,7,21] (pp.Natural.equal 99) === Some { _1 = 1, _2 = 99 }
let test35 = assert : elemIndex Integer ([] : List Integer) (pp.Integer.equal +99) === None { _1 : Natural, _2 : Integer }
let test36 = assert : elemIndex Natural [10,99,21,13,3,4,7,21] (pp.Natural.equal 21) === Some { _1 = 2, _2 = 21 }
let test37 = assert : indexProof NonZero [!13, !4, !17, !18, !100, !2] 4 Prf === !100
--let test30 = assert : indexProof NonZero [!13, !4, !17, !18, !100, !2] 40 Prf === None NonZero
let test38 = assert : indexProof NonZero [!13, !4, !17, !18, !100, !2] 0 Prf === !13
let test39 = assert : indexProof NonZero [!13, !4, !17, !18, !100, !2] 1 Prf === !4
--let test33 = assert : indexProof NonZero [!13] 1 Prf === None NonZero
let test40 = assert : indexProof NonZero [!13] 0 Prf === !13
--let test35 = assert : indexProof NonZero ([] : List NonZero) 0 Prf === None NonZero
--let test36 = assert : indexProof NonZero ([] : List NonZero) 1 Prf === None NonZero

let test41 = assert : takeWhile Natural (pp.Natural.lessThan 10) [12,30,12,11,10,9] === [ 12, 30, 12, 11 ]
let test42 = assert : dropWhile Natural (pp.Natural.lessThan 10) [12,30,12,11,10,9,8,7] === [10,9,8,7]
let test43 = assert : span Natural (pp.Natural.lessThan 10) [12,30,12,11,10,9,8,7] === { _1 = [ 12, 30, 12, 11 ], _2 = [ 10, 9, 8, 7 ] }
let test44 = assert : span Natural (pp.Natural.lessThan 10) [1,2,3] === { _1 = [] : List Natural, _2 = [ 1, 2, 3 ] }
let test45 = assert : span Natural (pp.Natural.lessThan 10) [12,13,15] === { _1 = [ 12, 13, 15 ], _2 = [] : List Natural }
let test46 = assert : span Natural (pp.Natural.lessThan 10) ([] : List Natural) === { _1 = [] : List Natural, _2 = [] : List Natural }
let test47 = assert : itoList Integer [+4,-5,+20,-0] ===
 [ { _1 = 0, _2 = +4 }
 , { _1 = 1, _2 = -5 }
 , { _1 = 2, _2 = +20 }
 , { _1 = 3, _2 = +0 }
 ]

--let test25 = assert : scanl Natural [1,2,3,4,5] (List Natural) (ll.flipCons Natural) [999] ===
let test48 = assert : scanl Natural [1,2,3,4,5] (List Natural) (\(b : List Natural) -> \(a : Natural) -> [a] # b) [999] ===
  [ [ 999 ]
  , [ 1, 999 ]
  , [ 2, 1, 999 ]
  , [ 3, 2, 1, 999 ]
  , [ 4, 3, 2, 1, 999 ]
  , [ 5, 4, 3, 2, 1, 999 ]
  ]

--let test26 = assert : scan Natural [1,2,3,4,5] (List Natural) (ll.cons Natural) [999] ===
let test49 = assert : scan Natural [1,2,3,4,5] (List Natural) (\(a : Natural) -> \(b : List Natural) -> [a] # b) [999] ===
  [ [ 1, 2, 3, 4, 5, 999 ]
  , [ 2, 3, 4, 5, 999 ]
  , [ 3, 4, 5, 999 ]
  , [ 4, 5, 999 ]
  , [ 5, 999 ]
  , [ 999 ]
  ]
--let test27 = assert : scan Natural [1,2,3,4,5] Natural nn.add 999 === [ 1014, 1013, 1011, 1008, 1004, 999 ]
let test50 = assert : scan Natural [1,2,3,4,5] Natural (\(a : Natural) -> \(b : Natural) -> a + b) 999 === [ 1014, 1013, 1011, 1008, 1004, 999 ]
-- let test28 = assert : scanl Natural [1,2,3,4,5] Natural nn.add 999 === [ 999, 1000, 1002, 1005, 1009, 1014 ]
let test51 = assert : scanl Natural [1,2,3,4,5] Natural (\(a : Natural) -> \(b : Natural) -> a + b) 999 === [ 999, 1000, 1002, 1005, 1009, 1014 ]

let test52 = assert : equals Natural oo.compareNatural [10,12,33] === False
let test53 = assert : equals Natural oo.compareNatural [10] === True
let test54 = assert : equals Natural oo.compareNatural ([] : List Natural) === True
let test55 = assert : equals Natural oo.compareNatural [10,10,10,10] === True
let test56 = assert : equals Natural oo.compareNatural [10,10,10,1] === False

let test57 = assert : notEquals Natural oo.compareNatural [10,12,10,11] === True
let test58 = assert : notEquals Natural oo.compareNatural [10,12,12,10,11] === False
let test59 = assert : notEquals Natural oo.compareNatural ([] : List Natural) === True
let test60 = assert : notEquals Natural oo.compareNatural [10] === True
let test61 = assert : notEquals Natural oo.compareNatural [10,11] === True
let test62 = assert : notEquals Natural oo.compareNatural [10,10] === False

let test63 = assert : zipTrunc Natural Integer ([] : List Natural) ([] : List Integer)
===
([] : List { _1 : Natural, _2 : Integer })

let test64 = assert : zipTrunc Natural Integer [1,2,3] ([] : List Integer)
===
([] : List { _1 : Natural, _2 : Integer })

let test65 = assert : zipTrunc Natural Integer ([] : List Natural) [+1,+8]
===
([] : List { _1 : Natural, _2 : Integer })

let test66 = assert : zipTrunc Natural Integer [1,2,3] [+12,+13,+14,+15,+16] ===
[ { _1 = 1, _2 = +12 }, { _1 = 2, _2 = +13 }, { _1 = 3, _2 = +14 } ]

let test67 = assert : zipTrunc Natural Integer [1,2,3,4,5,6] [+12,+13] ===
[ { _1 = 1, _2 = +12 }, { _1 = 2, _2 = +13 } ]
let test68 = assert : zipTrunc Natural Integer [1,2,3] [+12,+13,+14] ===
[ { _1 = 1, _2 = +12 }, { _1 = 2, _2 = +13 }, { _1 = 3, _2 = +14 } ]

let test69 = assert : compareAdjacent Natural oo.compareNatural allLT [1,2,3,4,4] === False
let test70 = assert : compareAdjacent Natural oo.compareNatural allLE [1,2,3,4,4,10] === True
let test71 = assert : compareAdjacent Natural oo.compareNatural allLT [1,2,3,4] === True
let test72 = assert : compareAdjacent Natural oo.compareNatural allNE [1,2,3,4] === True
let test73 = assert : compareAdjacent Natural oo.compareNatural allNE [1,4,2,3,4] === True
let test74 = assert : compareAdjacent Natural oo.compareNatural allNE [1,4,2,4,4,7] === False
let test75 = assert : compareAdjacent Natural oo.compareNatural allEQ [1,4,2,4,4,7] === False
let test76 = assert : compareAdjacent Natural oo.compareNatural allEQ [4,4,4] === True
let test77 = assert : compareAdjacent Natural oo.compareNatural allEQ [4,4] === True
let test78 = assert : compareAdjacent Natural oo.compareNatural allEQ [4] === True
let test79 = assert : compareAdjacent Natural oo.compareNatural allEQ ([] : List Natural) === True
let test80 = assert : compareAdjacent Natural oo.compareNatural allGT [4,1,0] === True
let test81 = assert : compareAdjacent Natural oo.compareNatural allGT [5,4,4,0] === False
let test82 = assert : compareAdjacent Natural oo.compareNatural allGE [5,4,4,0] === True

let test83 = assert : asc Natural oo.compareNatural [1,1,1] === True
let test84 = assert : asc Natural oo.compareNatural [1,1,1,2,3,5] === True
let test85 = assert : asc Natural oo.compareNatural [1,2,3,2,4] === False
let test86 = assert : ascStrict Natural oo.compareNatural [1,1,1] === False
let test87 = assert : ascStrict Natural oo.compareNatural [1,1,1,2,3,5] === False
let test88 = assert : ascStrict Natural oo.compareNatural [1,2,3,2,4] === False
let test89 = assert : ascStrict Natural oo.compareNatural [1,2,3,5] === True

let test90 = assert : Proof/toBool (ip4Proof 1 2 3 256) === False
-- cos we got added Kind support in dhall TypeCheck
let test91 = assert : ip4Proof 1 2 3 255 === Proof ^^"dont care"

let test92 = assert : fill Natural Integer True [1,2,3,4,5,6,7] [+4,-9] 999 -999
=== { _1 = [1,2,3,4,5,6,7], _2 = [-999,-999,-999,-999,-999,+4,-9] }
let test93 = assert : fill Integer Natural True [+4,-9] [1,2,3,4,5,6,7] -999 999
=== { _1 = [-999,-999,-999,-999,-999,+4,-9], _2 = [1,2,3,4,5,6,7] }
let test94 = assert : fill Integer Natural True [+4,-9,-3,-1] [1,2,3,4] -999 999
=== { _1 = [+4,-9,-3,-1], _2 = [1,2,3,4] }
let test95 = assert : fill Integer Natural True ([] : List Integer) [1,2,3,4] -999 999
=== { _1 = [-999,-999,-999,-999], _2 = [1,2,3,4] }
let test96 = assert : fill Integer Natural True [+4,-9,-3,-1] ([] : List Natural) -999 999
=== { _1 = [+4,-9,-3,-1], _2 = [999,999,999,999] }

let test97 = assert : fill Natural Integer False [1,2,3,4,5,6,7] [+4,-9] 999 -999
=== { _1 = [1,2,3,4,5,6,7], _2 = [+4,-9,-999,-999,-999,-999,-999] }
let test98 = assert : fill Integer Natural False [+4,-9] [1,2,3,4,5,6,7] -999 999
=== { _1 = [+4,-9,-999,-999,-999,-999,-999], _2 = [1,2,3,4,5,6,7] }

let test99 = assert : fill Integer Natural True ([] : List Integer) ([] : List Natural) -999 999
=== { _1 = [] : List Integer, _2 = [] : List Natural }

let test100 = assert : elemIndexProof Natural [10,99,13,3,4,7,21] (pp.Natural.equal 21) Prf === { _1 = 6, _2 = 21 }
--let test97 = assert : elemIndexProof Natural [10,99,13,3,4,7,21] (pp.Natural.equal 1) Prf ===  { _1 : Natural, _2 : Natural }
let test101 = assert : elemIndexProof Natural [10,99,13,3,4,7,21] (pp.Natural.equal 99) Prf ===  { _1 = 1, _2 = 99 }
--let test99 = assert : elemIndexProof Integer ([] : List Integer) (pp.Integer.equal +99) Prf ===  { _1 : Natural, _2 : Integer }
let test102 = assert : elemIndexProof Natural [10,99,21,13,3,4,7,21] (pp.Natural.equal 21) Prf ===  { _1 = 2, _2 = 21 }

let test103 = assert : singletonProof Natural [10] Prf === 10
--let test96 = assert : singletonProof Natural [10,11] Prf === 10
--let test96 = assert : singletonProof Natural ([] : List Natural) Prf === 10

let test104 = assert : inits Natural ([] : List Natural) === ([] : List (List Natural))
let test105 = assert : tails Natural ([] : List Natural) === ([] : List (List Natural))
let test106 = assert : inits Natural [1,2,3]
===
[ [ 1 ], [ 1, 2 ], [ 1, 2, 3 ] ]

let test107 = assert : tails Natural [1,2,3]
===
[ [ 1, 2, 3 ], [ 2, 3 ], [ 3 ] ]

let test108 = assert : chunksOf !3 !1 Natural [10,11,12,13,14,15,16]
===
[ [ 10, 11, 12 ]
, [ 11, 12, 13 ]
, [ 12, 13, 14 ]
, [ 13, 14, 15 ]
, [ 14, 15, 16 ]
]

let test109 = assert : chunksOf !3 !1 Natural ([] : List Natural)
=== ([] : List (List Natural))

let test110 = assert : traverse Natural Text [[1,10],[11,3,7],[2,1]] (pp.List.map Natural Text Natural/show)
===
[ [ "1", "10" ], [ "11", "3", "7" ], [ "2", "1" ] ]

let test111 = assert : List/permutations Text ["a","b","c"]
===
[ [ "a", "b", "c" ]
, [ "a", "c", "b" ]
, [ "b", "a", "c" ]
, [ "b", "c", "a" ]
, [ "c", "a", "b" ]
, [ "c", "b", "a" ]
]

let test112 = assert : subsequences Text ["a","b","c"]
===
[ [] : List Text
, [ "a" ]
, [ "b" ]
, [ "c" ]
, [ "a", "b" ]
, [ "a", "c" ]
, [ "b", "c" ]
, [ "a", "b", "c" ]
]

let test113 = assert : select Natural [1,2,3,4]
===
[ { _1 = 4, _2 = [ 1, 2, 3 ] }
, { _1 = 3, _2 = [ 1, 2, 4 ] }
, { _1 = 2, _2 = [ 1, 3, 4 ] }
, { _1 = 1, _2 = [ 2, 3, 4 ] }
]

let test114 = assert : select Natural [1,2,1,4]
===
[ { _1 = 4, _2 = [ 1, 2, 1 ] }
, { _1 = 1, _2 = [ 1, 2, 4 ] }
, { _1 = 2, _2 = [ 1, 1, 4 ] }
, { _1 = 1, _2 = [ 2, 1, 4 ] }
]

let test115 = assert : select Text ["a","b","c","d"]
===
[ { _1 = "d", _2 = [ "a", "b", "c" ] }
, { _1 = "c", _2 = [ "a", "b", "d" ] }
, { _1 = "b", _2 = [ "a", "c", "d" ] }
, { _1 = "a", _2 = [ "b", "c", "d" ] }
]

let test116 = assert : select Text ["e","b","c","d"]
===
[ { _1 = "d", _2 = [ "e", "b", "c" ] }
, { _1 = "c", _2 = [ "e", "b", "d" ] }
, { _1 = "b", _2 = [ "e", "c", "d" ] }
, { _1 = "e", _2 = [ "b", "c", "d" ] }
]

let test117 = assert : select Text ["e"]
===
[ { _1 = "e", _2 = [] : List Text } ]

let test118 = assert : select Text ([] : List Text)
=== ([] : List { _1 : Text, _2 : List Text })

let test119 = assert : splits Natural [1,2,3]
===
[ { _1 = [ 1 ], _2 = [ 2, 3 ] }, { _1 = [ 1, 2 ], _2 = [ 3 ] } ]

let test120 = assert : splits Natural [1,2,3,4]
===
[ { _1 = [ 1 ], _2 = [ 2, 3, 4 ] }
, { _1 = [ 1, 2 ], _2 = [ 3, 4 ] }
, { _1 = [ 1, 2, 3 ], _2 = [ 4 ] }
]

let test121 = assert : splits Natural [1]
===
([] : List { _1 : List Natural, _2 : List Natural })

let test122 = assert : splits Natural [1,2]
===
[ { _1 = [ 1 ], _2 = [ 2 ] } ]

let test123 = assert : splits Natural ([] : List Natural)
===
([] : List { _1 : List Natural, _2 : List Natural })

let test124 = assert : substring Integer [+4,-3,+7,+12,-1,-2] 0 10
===
[+4,-3,+7,+12,-1,-2]

let test125 = assert : substring Integer [+4,-3,+7,+12,-1,-2] 2 1
===
[+7]

let test126 = assert : substring Integer [+4,-3,+7,+12,-1,-2] 2 0
===
([] : List Integer)

let test127 = assert : substringProof Integer [+4,-3,+7,+12,-1,-2] 2 !3 Prf Prf
===
[+7,+12,-1]

let test128 = assert : substringProof Integer [+4,-3,+7,+12,-1,-2] 3 !2 Prf Prf
===
[+12,-1]

let test129 = assert : substringProof Integer [+4,-3,+7,+12,-1,-2] 5 !1 Prf Prf
===
[-2]

let test130 = assert : mapAmp Natural { _1 : Natural, _2 : Natural } (\(y : Natural) -> nn.divMod y !3)  (nn.enumerate 10)
===
[ { _1 = 0, _2 = { _1 = 0, _2 = 0 } }
, { _1 = 1, _2 = { _1 = 0, _2 = 1 } }
, { _1 = 2, _2 = { _1 = 0, _2 = 2 } }
, { _1 = 3, _2 = { _1 = 1, _2 = 0 } }
, { _1 = 4, _2 = { _1 = 1, _2 = 1 } }
, { _1 = 5, _2 = { _1 = 1, _2 = 2 } }
, { _1 = 6, _2 = { _1 = 2, _2 = 0 } }
, { _1 = 7, _2 = { _1 = 2, _2 = 1 } }
, { _1 = 8, _2 = { _1 = 2, _2 = 2 } }
, { _1 = 9, _2 = { _1 = 3, _2 = 0 } }
]

let test131 = assert : pp.List.map Natural (List Natural) pascal (nn.enumerate 13)
===
[ [ 1 ]
, [ 1, 1 ]
, [ 1, 2, 1 ]
, [ 1, 3, 3, 1 ]
, [ 1, 4, 6, 4, 1 ]
, [ 1, 5, 10, 10, 5, 1 ]
, [ 1, 6, 15, 20, 15, 6, 1 ]
, [ 1, 7, 21, 35, 35, 21, 7, 1 ]
, [ 1, 8, 28, 56, 70, 56, 28, 8, 1 ]
, [ 1, 9, 36, 84, 126, 126, 84, 36, 9, 1 ]
, [ 1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1 ]
, [ 1, 11, 55, 165, 330, 462, 462, 330, 165, 55, 11, 1 ]
, [ 1, 12, 66, 220, 495, 792, 924, 792, 495, 220, 66, 12, 1 ]
]

let test132 = assert : pp.List.map Natural Natural (\(a : Natural) -> pp.Natural.sum (pascal a)) (nn.enumerate 13)
===
[ 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096 ]

let test133 = assert : fib 10
===
[ 0, 1, 1, 2, 3, 5, 8, 13, 21, 34 ]

let test134 = assert : List/choose Natural 2 [1,2,3]
===
[ [ 1, 2 ], [ 1, 3 ], [ 2, 3 ] ]

let test135 = assert : List/choose Natural 0 [1,2,3]
===
[ [] : List Natural ]

let test136 = assert : List/choose Natural 1 [1,2,3]
===
[ [1], [2], [3] ]

let test137 = assert : List/choose Natural 10 [1,2,3]
===
([] : List (List Natural))

let test138 = assert : List/choose Text 2 ["b","c","d"]
===
[ [ "b", "c" ], [ "b", "d" ], [ "c", "d" ] ]

let test139 = assert : List/permutations Natural [1,2,3]
===
[ [ 1, 2, 3 ], [ 1, 3, 2 ], [ 2, 1, 3 ], [ 2, 3, 1 ], [ 3, 1, 2 ], [ 3, 2, 1 ] ]

let test140 = assert : subsequences Natural [1,2,3]
===
[ [] : List Natural
, [ 1 ]
, [ 2 ]
, [ 3 ]
, [ 1, 2 ]
, [ 1, 3 ]
, [ 2, 3 ]
, [ 1, 2, 3 ]
]

let test141 = assert : subsequences Natural ([] : List Natural)
===
[ [] : List Natural ]

in {
, equals
, notEquals
, flipCons
, cons
, flipSnoc
, snoc

, mempty
, mappend
, mconcat

, traverse

, zipWithTrunc
, zipTrunc
, zipWithProof
, zipProof
, cartesianWith
, cartesian
, fill

, compare
, sortBy

, elemIndex
, elemIndexProof
, index
, indexProof
, indexReplace
, elem
, takeWhile
, dropWhile
, span
, break

, itoList
, scan
, scanl

, pairsWith
, pairs
, compareAdjacent
, allEQ
, allNE
, allLT
, allLE
, allGE
, allGT

, desc
, descStrict
, asc
, ascStrict

, allInList
, allInListNat
, allInListInt

, ip4Proof
, ascNatProof

, singletonProof
, inits
, tails
, chunksOf

, splitAt
, substring
, substringProof

, chooseProof
, chooseFastList
, subsequences
, select
, splits

, mapAmp
, pascal
, fib
}

{- record projection by expression
just have to provide label and the level above: ie 10 is Natural
Bool is Type
how to use Kind though?
let e = { a = 10, b = "Text", c = Bool } let s = { a : Natural, c : Type } in e.(s)
{ a = 10, c = Bool }
-}