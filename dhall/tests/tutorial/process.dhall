    λ(union : < Left : Natural | Right : Bool >)
→   let handlers =
            { Left  = Natural/even  -- Natural/even is a built-in function
            , Right = λ(b : Bool) → b
            }
in  merge handlers union : Bool
