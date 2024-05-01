import «Affine6501S24».Affine1D

def pt1 := Point1D.mk (3.5 : Rat)
def pt2 := Point1D.mk (5.5 : Rat)

def main : IO Unit :=
  do
    IO.println s!"pt1 = {pt1}"
    IO.println s!"pt2 = {pt2}"

#eval main