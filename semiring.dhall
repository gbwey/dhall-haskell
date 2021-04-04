let semiring =
    \(a : Type)
 -> { multiply : a -> a -> a
    , add : a -> a -> a
    , zero : a
    , one : a
    , fromNatural : Natural -> a
    }

let enumerateN =
    \(a : Type)
 -> \(add : a -> a -> a)
 -> \(n : Natural)
 -> \(start : a)
 -> \(step : a)
 -> let t = { index : a, ret : List a }
    let r = Natural/fold
         n
         t
         (\(z : t) -> { index = add step z.index, ret = z.ret # [z.index] })
         { index = start, ret = [] : List a }
    in r.ret
    : List a

let enumerate =
    \(a : Type)
 -> \(sr : semiring a)
 -> \(n : Natural)
 -> enumerateN a sr.add n sr.zero sr.one
    : List a

in {
, Type = semiring
, enumerate
, enumerateN
}