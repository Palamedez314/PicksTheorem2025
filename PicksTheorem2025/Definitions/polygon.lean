import Mathlib.Algebra.Order.Field.Basic

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : R → K}
--def ι : Int → K := Int.cast
def Point (R : Type) := R × R
def maximum : Point R → R := sorry


class Polygon (R : Type) (len : Nat) where
  vertex : Fin (len + 1) → Point R


variable {len : Nat}


def isClosed (p : Polygon R len) := p.vertex 0 = p.vertex (Fin.ofNat (len +1) len)
def isBounded (p : Polygon R len) (bound : Nat)
    := ∀ i : Fin (len+1), maximum (p.vertex i) ≤ Nat.cast bound


--def p1 : Point Int := ⟨1, 1⟩
--def p2 : Point Int := ⟨1, 2⟩
--def p3 : Point Int := ⟨2, 1⟩

macro polygon:term "[" index:term "]" : term => `(($polygon).vertex ($index))

--def n: Nat
--def a := [(0:Int),(1:Int)]
--#check a[n]

instance toPolygon {R : Type} (l : List (Point R)) : Polygon R l.length where
  vertex (i) := l[@Fin.val (l.length+1) i]'(i.is_lt)
--def p : Polygon Int 3 := ⟨

#eval (4 : Fin 7).val
#check (4 : Fin 7).val

def trapezoidArea (u v : Point R) : K :=
  (ι u.1 - ι v.1) * (ι u.2 + ι v.2) / Int.cast 2


#eval trapezoidArea p2 p3
