import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field
import Mathlib.Algebra.AddTorsor
import Mathlib.Data.Vector        --https://github.com/leanprover-community/mathlib4/blob/a7ed535af2a1f78accefeaeee98233dd25714110/Mathlib/Data/Vector.lean#L20-L21


section k_affine_n

universe u
variable
  {K : Type u}  -- implicit type argument
  [Field K]     -- with an implementation of the Field typeclass
  (n : Nat)     -- the dimension of the space 
  [ToString K]  -- so that we can more easily print tuples of K values

/-!
## POINT uniquely identified by n-tuple of values from a field K 
-/

/-!
Note on the Vector type in Lean. Instance of this type do NOT
(necessarily) represent vectors in any sort of mathematical space
other than being fixed-length lists of values of some types. 

def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }

The notation on the second line is Lean's subtype notation. This
example defines the type of all List α values, l, whose length is
exactly n. A value of this type is a *dependent pair*, comprising
an List α value, l, and a proof that l.length = n.

A better name for this type would have been Tuple, but we're stuck 
with Vector. We'll pick names that don'e conflict when we get to 
defining mathematical vectors very shortly. For now the key idea
is that we can use Vector objects as representations of points and 
vectors in n-dimensional (affine) spaces. 
-/

example : Vector K 0 := @Vector.nil K
example : Vector ℚ 3 := 1/2::2/3::3/4
  
structure Point where
  rep : Vector K n

instance : ToString (@Point1D K n) where
  toString : (@Point1D K) -> String
    | { rep := r } => s!"Pt({r})"     -- new {} matching notation, string interpolation 

end k_affine_n

