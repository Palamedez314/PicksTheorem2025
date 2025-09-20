import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : R → K}
--def ι : Int → K := Int.cast
def Point (R : Type) := R × R
def maximum : Point R → R := sorry

class Polygon (R : Type) (len : Nat) where
  vertex : Fin (len + 1) → Point R

variable {len : Nat}

def isClosed (P : Polygon R len) := P.vertex 0 = P.vertex (Fin.ofNat (len +1) len)
def isBounded (P : Polygon R len) (bound : Nat)
    := ∀ i : Fin (len+1), maximum (P.vertex i) ≤ Nat.cast bound

def trapezoidArea (ι : R → K) (u v : Point R) : K :=
  ((ι u.1 - ι v.1) * (ι u.2 + ι v.2)) / (Int.cast 2)

def polygonArea {R : Type} {len : Nat} (ι : R → K) (P : Polygon R len) : K
    := ∑ i ∈ Finset.range len,
      trapezoidArea ι (P.vertex (Fin.ofNat (len+1) i)) (P.vertex (Fin.ofNat (len+1) (i+1)))
