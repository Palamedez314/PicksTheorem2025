import PicksTheorem2025.Definitions.imports

variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

-- abelian group of points later used with ℤ² and K²
abbrev Point (R : Type) := R × R

-- definition of a polygon with len sides as a tuple of its corner points
structure Polygon (R : Type) where
  len : Nat
  vertex : Fin (len+1) → Point R

-- additional properties of polygons
def isClosed (P : Polygon R) :=
  P.vertex 0 = P.vertex (Fin.ofNat (P.len+1) P.len)

def supNorm (p : Point R) : R := max |p.1| |p.2|

def isBounded (P : Polygon R) (bound : Nat)
    := ∀ i : Fin (P.len+1), supNorm (P.vertex i) ≤ (bound : R)
