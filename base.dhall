let const =
  \(a : Type) -> \(b : Type) -> \(x : a) -> \(y : b) -> x : a

let flipConst =
  \(a : Type) -> \(b : Type) -> \(x : a) -> \(y : b) -> y : b

let test1 = assert : const Natural Bool 12 True === 12
let test2 = assert : flipConst Natural Bool 12 True === True

in {
const,
flipConst
}