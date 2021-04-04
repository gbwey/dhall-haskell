-- think agda: always spaces between stuff: eg "a + 1" not "a+1"
let pp = ./dhall/dhall-lang/Prelude/package.dhall ? env:dhall_prelude

let catOptionals =
     \(t : Type)
  -> \(lin : List (Optional t))
  -> List/fold
       (Optional t)
       lin
       (List t)
       (\(a : Optional t) -> \(xs : List t) -> merge { Some = \(x : t) -> [x] # xs, None = xs } a)
       (pp.List.empty t)
        : List t

let seq =
     \(t : Type)
  -> \(lin : List (Optional t))
  -> let z = catOptionals t lin
     in if pp.List.null t z then None (List t)
        else Some z
   : Optional (List t)

let unseq =
     \(t : Type)
  -> \(lin : Optional (List t))
  -> merge
     {
     , Some = \(lst : List t) -> (pp.List.map t (Optional t) (\(a : t) -> Some a)) lst
     , None = pp.List.empty (Optional t)
     } lin
    : List (Optional t)

let traverse =
     \(a : Type)
  -> \(b : Type)
  -> \(xs : List a)
  -> \(f : a -> Optional b)
  -> List/fold
      a
      xs
      (Optional (List b))
      (   \(x : a)
       -> \(z : Optional (List b))
       -> merge
          { None = None (List b)
          , Some = \(ys : List b) ->
              merge { None = None (List b)
                    , Some = \(y : b) -> Some ([y] # ys)
                    } (f x)
          } z
      )
      (Some ([] : List b))
      : Optional (List b)

let flatten =
     \(t : Type)
  -> \(o : Optional (Optional t))
  -> merge { Some = pp.Function.identity (Optional t), None = None t } o
     : Optional t

let lift2 =
     \(a : Type)
  -> \(b : Type)
  -> \(c : Type)
  -> \(ma : Optional a)
  -> \(mb : Optional b)
  -> \(f :  a -> b -> c)
  -> let f = \(a : a) -> merge { None = None c, Some = \(b : b) -> Some (f a b) } mb
     in merge { None = None c, Some = f } ma
    : Optional c

let tapp =
     \(a : Type)
  -> \(b : Type)
  -> \(f : a -> Optional b)
  -> \(x : a)
  -> \(xs : Optional (List b))
  -> merge
          { None = None (List b)
          , Some = \(ys : List b) ->
              merge { None = None (List b)
                    , Some = \(y : b) -> Some ([y] # ys)
                    } (f x)
          } xs
   : Optional (List b)

let tzero =
     \(b : Type)
  -> Some ([] : List b)
   : Optional (List b)

let traverseGeneric =
     \(a : Type)
  -> \(b : Type)
  -> \(m : Type -> Type)
  -> \(f : a -> m (List b) -> m (List b))
  -> \(xs : List a)
  -> \(z : m (List b))
  -> List/fold
      a
      xs
      (m (List b))
      f
      z
     : m (List b)
{-
let pure =
    \(a : Type)
 -> \(m : Type -> Type)
 -> \(f : a -> m a)
 -> \(x : a)
 -> f x
   : m a
-}

let pure =
    \(a : Type)
 -> \(x : a)
 -> Some x

let bind =
    \(a : Type)
 -> \(b : Type)
 -> \(ma : Optional a)
 -> \(amb : a -> Optional b)
 -> merge { None = None b, Some = \(x : a) -> amb x } ma
   : Optional b
{-
let app =
    \(a : Type)
 -> \(b : Type)
 -> \(c : Type)
 -> \(m : Type -> Type)
 -> \(bind1 : m a -> (a -> m b))
 -> \(bind2 : m a -> (a -> m b))
 -> \(pure : a -> m a)
 -> \(f : a -> b -> c)
 -> \(ma : m a)
 -> \(mb : m b)
 -> bind1 ma (\(x : a) -> bind2 mb (\(y : b) -> pure (f x y)))
   : m b
-}

let test1 = assert : flatten Natural (Some (Some 123)) === Some 123
let test2 = assert : flatten Bool (Some (None Bool)) === None Bool
let test3 = assert : flatten Bool (None (Optional Bool)) === None Bool
let test4 = assert : unseq Natural (seq Natural ([] : List (Optional Natural))) === ([] : List (Optional Natural))
let test5 = assert : unseq Natural (seq Natural [Some 4, Some 5, None Natural, None Natural, Some 7]) === [Some 4, Some 5, Some 7]
let test6 = assert : seq Natural [Some 4, Some 5, None Natural, None Natural, Some 7] === Some [4, 5, 7]
let test7 = assert : unseq Natural (Some [4, 5, 7]) === [Some 4, Some 5, Some 7]
let test8 = assert : seq Natural ([] : List (Optional Natural)) === None (List Natural)

let test9 = assert : lift2 Natural Natural { _1 : Natural, _2 : Natural } (Some 14) (Some 22) (\(a : Natural) -> \(b : Natural) -> { _1 = a, _2 = b }) === Some { _1 = 14, _2 = 22 }
let test10 = assert : let f = \(d : Double) -> \(i : Double) -> \(j : Double) -> {=} in f -1.3e-10  +14.0000001 -13.0000000000 === {=}

-- (http://ifconfig.me as Text)

let test11 = assert : traverse Text Natural (Regex/split ~"\." "107.221.197.155" !100) Natural/parse === Some [ 107, 221, 197, 155 ]
let test12 = assert : traverseGeneric Natural Natural Optional (tapp Natural Natural (\(a : Natural) -> if pp.Natural.lessThan a 4 then Some (a + 1) else None Natural)) [2,3,4] (tzero Natural) === None (List Natural)
let test13 = assert : traverseGeneric Natural Natural Optional (tapp Natural Natural (\(a : Natural) -> if pp.Natural.lessThan a 10 then Some (a + 1) else None Natural)) [2,3,4] (tzero Natural) === Some [ 3, 4, 5 ]


in {
, pure
, bind
, lift2
, seq
, unseq
, catOptionals
, flatten
, traverse
, traverseGeneric
, tzero
, tapp
}
