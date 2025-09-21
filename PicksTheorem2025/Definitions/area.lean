import PicksTheorem2025.Definitions.polygon

variable {K : Type} [Field K] {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

-- area of the trapezoid under two Points
def trapezoidArea (ι : R → K) (u v : Point R) : K :=
  ((ι u.1 - ι v.1) * (ι u.2 + ι v.2)) / (Int.cast 2)

-- area of a polygon
def polygonArea {R : Type} {len : Nat} (ι : R → K) (P : Polygon R len) : K
    := ∑ i ∈ Finset.range len,
      trapezoidArea ι (P.vertex (Fin.ofNat (len+1) i)) (P.vertex (Fin.ofNat (len+1) (i+1)))

-- inclusion of R² into K² using ι
def κ (ι : R → K) : Point R → Point K := fun p ↦ ⟨ι p.1, ι p.2⟩
