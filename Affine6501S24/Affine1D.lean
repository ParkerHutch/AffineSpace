import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field

section AffineSpace

universe u

variable
  {K : Type u}
  [Field K]
  [ToString K]
  
structure Point1D where
  rep : K

#check (@Point1D K)

instance : ToString (@Point1D K) where
  toString : (@Point1D K) -> String
    | { rep := r } => s!"({r})"


structure Vector1D
(rep : K)

structure Scalar1D
(rep : K)

end AffineSpace

#check (@Point1D)