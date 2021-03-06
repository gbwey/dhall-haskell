let Nat = forall(N : Type) -> (N -> N) -> N -> N
let n2  = \(N : Type) -> \(s : N -> N) -> \(z : N) -> s (s z)
let n5  = \(N : Type) -> \(s : N -> N) -> \(z : N) -> s (s (s (s (s z))))

let mul =
  \(a : Nat) -> \(b : Nat) -> \(N : Type) -> \(s : N -> N) -> \(z : N) -> a N (b N s) z

let add =
  \(a : Nat) -> \(b : Nat) -> \(N : Type) -> \(s : N -> N) -> \(z : N) -> a N s (b N s z)

let succNat = (\ (x: Natural) -> x + 1)

let n10   = mul n2 n5
let n100  = mul n10 n10
let n1k   = mul n10 n100
let n10k  = mul n100 n100
{-
let n100k = mul n10 n10k
let n1M   = mul n10k n100
let n5M   = mul n1M n5
let n10M  = mul n1M n10
let n20M  = mul n10M n2

in n1M Natural (\ (x : Natural) -> x + 1) 0
-}
in { a = n10k Natural (\ (x: Natural) -> x + 1) 0
    , n10
    , n2
    , n5
    , Nat
    , mul
    , add
    , succNat
    }

{-
> x.mul x.n2 x.n5 Natural (\(x : Natural) -> x + 1) 0
10
-}