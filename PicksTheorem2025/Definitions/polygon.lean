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

def p1 : Point Int := ⟨1, 1⟩
def p2 : Point Int := ⟨1, 2⟩
def p3 : Point Int := ⟨2, 1⟩

--macro polygon:term "[" index:term "]" : term => `(($polygon).vertex ($index))

instance toPolygon {R : Type} (l : List (Point R)) (h : l.length > 0 := by decide)
    : Polygon R (l.length-1) where
  vertex (i) := l[Fin.val i]'(by
    have h1 : l.length - 1 + 1 = l.length := by
      calc
      l.length - 1 + 1 = max l.length 1 := by apply Nat.sub_add_eq_max
      max l.length 1 = l.length := by apply max_eq_left h
    nth_rewrite 2 [← h1]
    apply i.is_lt)

def l := [p1,p2,p3]
def h : l.length > 0 := by decide
def P := toPolygon l h

def trapezoidArea (ι : R → K) (u v : Point R) : K :=
  ((ι u.1 - ι v.1) * (ι u.2 + ι v.2)) / (Int.cast 2)

def A {R : Type} {len : Nat} (P : Polygon R len) : K
    := ∑ i ∈ List.range len, trapezoidArea (P.vertex (i-1)) (P.vertex i)

#check List.range 3
