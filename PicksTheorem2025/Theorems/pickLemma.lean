import PicksTheorem2025.Definitions.area
import PicksTheorem2025.Definitions.winding

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]


theorem Point_in_Box_le_r (r : Nat) (p : Point ℤ) (h1 : p ∈ Box2d r) : supNorm p ≤ r := by
  by_cases h1_le_2 :|p.1| ≤ |p.2|
  have supNorm_eq_p2: supNorm p = |p.2| := by
    sorry
  sorry
  sorry

theorem dang_switch_order (u v : Point R) : (dang u v : K) = - dang v u := by sorry


theorem dang_
