import PicksTheorem2025.Definitions.imports

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

-- abelian group of points later used with ℤ² and K²
abbrev Point (R : Type*) := R × R

-- in Zukunft: Definitionen von mathlib benutzen?

-- definition of a polygon with len sides as a tuple of its corner points
structure Polygon (R : Type*) where
 len : Nat
 vertex : Fin (len+1) → Point R

-- additional properties of polygons
def isClosed (P : Polygon R) :=
  P.vertex 0 = P.vertex (Fin.ofNat (P.len+1) P.len)

-- wie könnte man sowas ähnliches hinkriegen
-- structure closedPolygon (R : Type*) extends (P : Polygon R) where
--   closed : isClosed P

def supNorm (p : Point R) : R := max |p.1| |p.2|

def getBound (P : Polygon R) : R :=
  (Finset.image (supNorm ∘ P.vertex) Finset.univ).max' (
    by
    unfold Finset.Nonempty
    simp only [Finset.mem_image, Finset.mem_univ, Function.comp_apply, true_and]
    exact ⟨supNorm (P.vertex (0: Fin (P.len+1))), 0, rfl⟩)

def isBounded (P : Polygon R) (bound : R)
    := ∀ i : Fin (P.len+1), supNorm (P.vertex i) ≤ (bound : R)

omit [IsStrictOrderedRing R] in
theorem correctBound (P : Polygon R) : isBounded P (getBound P)
    := by
  intro n
  unfold supNorm getBound
  simp
  apply sup_le_iff.mp
  apply Finset.le_max'
  simp
  use n
  constructor
