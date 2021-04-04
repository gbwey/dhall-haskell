let Eq : forall (A : Type) -> A -> A -> Type
  = \(A : Type) -> \(a : A) -> \(b : A) ->
     (forall (P : A -> Type) -> P a -> P b)

let refl : forall (A : Type) -> forall (a : A) -> Eq A a a
  = \(A : Type) -> \(a : A) -> \(P : A -> Type) -> \(pa : P a) -> pa

let exists =
  \(A : Type) -> \(B : A -> Type) ->
     forall (C : Type)
  -> forall (f : forall (a : A) -> B a -> C)
  -> C

-- pack : {A B} -> (a : A) -> B a -> exists A B
let pack = \(A : Type) -> \(B : A -> Type) -> \(a : A) -> \(ba : B a) ->
           \(C : Type) -> \(f : forall (a : A) -> B a -> C) ->
       f a ba

-- generically, the type of Bool-s which are true is the following:
let OnlyTrue = exists Bool (\(b : Bool) -> Eq Bool b True)

-- obviously verbose as hell
let myTrue : OnlyTrue
  = pack Bool (\(b : Bool) -> Eq Bool b True) True (refl Bool True)

in { myTrue, Eq, refl, exists, pack, OnlyTrue }

-- line comment fails if no newline after it! ie cannot be the last line!
-- :t a.pack Natural (\(b : Natural) -> Bool) 44 True
