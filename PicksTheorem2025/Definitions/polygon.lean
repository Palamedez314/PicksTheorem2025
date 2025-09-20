import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : R → K}

def Point (R : Type) := R × R

def Point.add (u v : Point R) : Point R := ⟨u.1 + v.1, u.2 + v.2⟩
def Point.sub (u v : Point R) : Point R := ⟨u.1 - v.1, u.2 - v.2⟩
def Point.cross (u v : Point R) : R := u.1 * v.2 - u.2 * v.1

def supNorm : Point R → R := fun p ↦ max |p.1| |p.2|

class Polygon (R : Type) (len : Nat) where
  vertex : Fin (len + 1) → Point R

variable {len : Nat}

def isClosed (P : Polygon R len) := P.vertex 0 = P.vertex (Fin.ofNat (len +1) len)
def isBounded (P : Polygon R len) (bound : Nat)
    := ∀ i : Fin (len+1), supNorm (P.vertex i) ≤ Nat.cast bound

def trapezoidArea (ι : R → K) (u v : Point R) : K :=
  ((ι u.1 - ι v.1) * (ι u.2 + ι v.2)) / (Int.cast 2)

def polygonArea {R : Type} {len : Nat} (ι : R → K) (P : Polygon R len) : K
    := ∑ i ∈ Finset.range len,
      trapezoidArea ι (P.vertex (Fin.ofNat (len+1) i)) (P.vertex (Fin.ofNat (len+1) (i+1)))

def κ : Point R → Point K := fun p ↦ ⟨ι p.1, ι p.2⟩


--def ι : Int → K := Int.cast


--instance instField : commGroup (Point R) where
--__


def p1 : Int × Int := ⟨1, 1⟩
def p2 : Int × Int := ⟨1, 2⟩


#eval p1-p2
