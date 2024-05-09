import «Affine6501S24».AffineSpace
import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field
import Mathlib.Algebra.AddTorsor
import Mathlib.Data.Vector        --https://github.com/leanprover-community/mathlib4/blob/a7ed535af2a1f78accefeaeee98233dd25714110/Mathlib/Data/Vector.lean#L20-L21

-- Define some ℚ n-tuples
def t1 : Vector ℚ 3 := ⟨ [0, (1/2:ℚ), 2], rfl ⟩
def t2 : Vector ℚ 3 := ⟨ [2, (-1/2:ℚ), -2], rfl ⟩

-- see tuple toString delegate to List toString
#eval s!"{t1}"


-- Define some rational affine 3-points
def p1 : AffPoint ℚ 3  := ⟨ t1 ⟩
def p2 : AffPoint ℚ 3  := ⟨ t2 ⟩

-- AffPt toString
#eval s!"{p1}"
def v := p2 -ᵥ p1

#eval s!"{v}"

def v2 := p2 +ᵥ p1

#eval s!"{v2}"

def v3 := -v

#eval s!"{v2}"

#check ToString (AffPoint ℚ 3)

def main : IO Unit :=
  do
    IO.println s!"t1 = {t1}"
    IO.println s!"t2 = {t2}"
    IO.println s!"p1 = {p1}"
    IO.println s!"p2 = {p2}"
    IO.println s!"v = p1 -ᵥ p2 = {v}"
    IO.println s!"v2 = p1 +ᵥ p2 = {v2}"
    IO.println s!"-v = {v3}"


#eval main
