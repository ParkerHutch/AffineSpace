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


/-!
We thus now have this notion of the type of n-tuples of K values,
where K is a field, and thus provides *, /, + -, etc., all of which
have been proven to behave in the expected ways (* distributes over
+, etc.).

Now we define our affine point and affine vector (as distict
from Lean Vector) types. Here we commit to the idea that the
scalar field from which tuple elements are drawn, and dimension
of an n-K-tuple, are parts of its *type*. Then when we define
operations that only make sense for, saw two same dimensional
vectors, we'll get type errors if we make mistakes like that.
-/

-- Implemented as list with a proof of length n

#check Vector K n   -- type of n-tuples of values from K represented as a list

instance : ToString (Vector K n) where
  toString : (Vector K n) -> String
    | ⟨ l, _ ⟩  => s!"{l}"     -- {} matching notation, string interpolation


structure AffPoint (K : Type u) [Field K] (n : Nat) where
  rep : Vector K n

instance : ToString (AffPoint K n) where
  toString : (AffPoint K n) -> String
    | ⟨ l ⟩   => s!"(Pt {l})"     -- {} matching notation, string interpolation


structure AffVector (K : Type u) [Field K] (n : Nat) where
  rep : Vector K n

instance : ToString (AffVector K n) where
  toString : (AffVector K n) -> String
    | ⟨ l ⟩    => s!"(Vc {l})"      -- {} matching notation, string interpolation

#check Repr
/-!
By representing n-K-tuples as length-n lists, we can use all
of the machiner of Lean's mathlib for working with lists to
implement our point-point subtraction affine space operator
abstraction.
-/

/-!
In our earlier work we overloaded the VSub typeclass,
by providing an implementation of (vsub : P → P → G),
where P is AffinePoint and G is AffineVector. Thereafter,
point-point subtraction will be denoted as `-ᵥ`.

class VSub (G : outParam (Type*)) (P : Type*) where
  vsub : P → P → G
-/

-- instance zero_vec : Zero (AffVector K n) := ⟨ Vector 0 ⟩

def add_vec : AffVector K n → AffVector K n → AffVector K n
| ⟨ l1, _ ⟩, ⟨ l2, _ ⟩ =>
  ⟨
    (List.zipWith (. + .) l1 l2),
    sorry
  ⟩

instance : Add (AffVector K n) := { add := add_vec n }

instance : AddSemigroup (AffVector K n) := { add_assoc := sorry }

instance : AddMonoid (AffVector K n) := {
  zero_add := sorry
  add_zero := sorry
}

def vadd_Aff : AffVector K n → AffPoint K n → AffPoint K n
| ⟨ l1, _ ⟩, ⟨ l2, _ ⟩ => sorry
  -- ⟨
  --   (List.zipWith (. - .) l1 l2),
  --   sorry
  -- ⟩

instance : VAdd (AffVector K n) (AffPoint K n) :=  { vadd := vadd_Aff n}

def vsub_Aff : AffPoint K n → AffPoint K n → AffVector K n
| ⟨ l1, _ ⟩, ⟨ l2, _ ⟩ =>
  ⟨
    (List.zipWith (. - .) l1 l2),
    sorry
  ⟩

instance : VSub (AffVector K n) (AffPoint K n) :=  { vsub := vsub_Aff n}

def inverse: AffVector K n → AffVector K n := sorry

instance AddAction AffVector AddPoint := sorry




instance : Add AffVector := { add := vadd_Aff }   -- using {} notation


instance : AddSemigroup AffVector := { add_assoc := sorry }


instance : AddMonoid AffVector := {
  zero_add := sorry
  add_zero := sorry
}

instance : SubNegMonoid AffVector := {
    neg := inverse,
    sub_eq_add_neg := sorry,
    zsmul_zero' := sorry,
    zsmul_succ' := sorry,
    zsmul_neg' := sorry
}
