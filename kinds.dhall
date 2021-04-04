-- https://github.com/dhall-lang/dhall-haskell/pull/563

\(j : Kind)
-> \(k : Kind)
-> \(c : j -> j -> Type)
-> \(d : k -> k -> Type)
-> \(f : j -> k)
-> { map : forall(a : j) -> forall(b : j) -> c a b -> d (f a) (f b) }

{-
let e = { a = 10, b = "Text", c = Bool, d = Type } let s = { a : Natural, c : Type, d : Kind } in e.(s)
{ a = 10, c = Bool, d = Type }

:t True
Bool

:t Bool
Type

:t Type
Kind

> :t Type
Kind

> :t { _1 : Type }
Kind

> :t Type -> Type
Kind

> :t { _1 : Bool }
Type

> :t { _1 : Bool, _2 : Type }
Kind

> :t { _1 : Bool, _2 : Kind }
Sort

> x Type Type (\(a : Type) -> \(b : Type) -> a -> b) (\(a : Type) -> \(b : Type) -> a -> b) Optional
{ map : forall(a : Type) -> forall(b : Type) -> (a -> b) -> Optional a -> Optional b }

> x Type Type (\(a : Type) -> \(b : Type) -> a -> b) (\(a : Type) -> \(b : Type) -> a -> b) List
{ map : forall(a : Type) -> forall(b : Type) -> (a -> b) -> List a -> List b }


> x (Type -> Type) Type (\(a : Type -> Type) -> \(b : Type -> Type) -> forall(i : Type) -> a i -> b i)  (\(a : Type) -> \(b : Type) -> a -> b) (\(f : Type -> Type) -> f Bool)
{ map :
      forall(a : Type -> Type)
    -> forall(b : Type -> Type)
    -> (forall(i : Type) -> a i -> b i)
    -> a Bool
    -> b Bool
}

> { foo = List, bar = Bool }
{ bar = Bool, foo = List }

> :t it
{ bar : Type, foo : Type -> Type }

> :t { foo = List, bar = Bool }
{ bar : Type, foo : Type -> Type }

> :t { bar : Type, foo : Type -> Type }
Kind

-}