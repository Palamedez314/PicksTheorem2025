import PicksTheorem2025.Definitions.polygon

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

class AngleMeasure (μ : Point K → Point K → K) where
  scaling (u v : Point K) (a : K) (ha : a > 0) : μ (a • u) v = μ u (a • v)
  antisymm (u v : Point K) : μ u v = - μ v u
  neg_neg (u v : Point K) : μ (-u) (-v) = μ u v
  addition (u v Point K) (s : K) (h0 : 0 ≤ s) (h1 : s ≤ 1) : μ u v = μ u (u + s • (v - u)) + μ (u + s • (v - u)) u
  normalisation : μ (1,0) (0,1) = 4⁻¹
