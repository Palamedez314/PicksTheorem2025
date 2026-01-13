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




def getBound (P : Polygon R) : R :=
  (Finset.image (supNorm ∘ P.vertex ∘ (Fin.ofNat (P.len+1))) (Finset.range (P.len+1))).max' (
    by
    unfold Finset.Nonempty
    simp
    use supNorm (P.vertex (0: Fin (P.len+1)))
    use 0
    simp
    rfl)


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
  ·exact n.is_lt
  ·(have typing : @Nat.cast (Fin (P.len + 1)) (Fin.NatCast.instNatCast (P.len + 1)) ↑n  = n
      := by exact (Fin.cast_val_eq_self n)
    rw[typing,supNorm])
