import «Affine6501S24».AffineSpace
import Std.Data.Rat.Basic         --https://leanprover-community.github.io/mathlib4_docs/Std/Data/Rat/Basic.html#Rat
import Mathlib.Algebra.Field.Defs --https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Field/Defs.html#Field
import Mathlib.Algebra.AddTorsor
import Mathlib.Data.Vector        --https://github.com/leanprover-community/mathlib4/blob/a7ed535af2a1f78accefeaeee98233dd25714110/Mathlib/Data/Vector.lean#L20-L21


def t1 : Vector ℚ 3 := ⟨ [0, (1/2:ℚ), 2], rfl ⟩ 
def t2 : Vector ℚ 3 := ⟨ [2, (-1/2:ℚ), -2], rfl ⟩ 

def p1 : AffPoint ℚ 3  := ⟨ t1 ⟩ 
def p2 : AffPoint ℚ 3  := ⟨ t2 ⟩ 

#reduce p2 -ᵥ p1

def v := p2 -ᵥ p1

def main : IO Unit :=
  do
    IO.println s!"t1 = {t1}"
    IO.println s!"t2 = {t2}"
    IO.println s!"p2 -ᵥ p2 = {v}""


#eval main