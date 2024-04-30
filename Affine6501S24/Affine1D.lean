import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field
import Mathlib.Algebra.AddTorsor

universe u

section foo

variable
  {K : Type u}
  [Field K]
  [ToString K]

/-!
## POINT
-/  
  
structure Point1D where
  rep : K

instance : ToString (@Point1D K) where
  toString : (@Point1D K) -> String
    | { rep := r } => s!"Pt({r})"     -- {} matching notation, string interpolation 


/-!
## VECTOR
-/  
   
structure Vector1D where
(rep : K)

instance : ToString (@Vector1D K) where
  toString : (@Vector1D K) -> String
    | { rep := r } => s!"Pt({r})"     


/-!
SCALAR
-/

structure Scalar where
(rep : K)

instance : ToString (@Scalar K) where
  toString : (@Scalar K) -> String
    | { rep := r } => s!"Pt({r})"    


end foo

/-!
-/