import PicksTheorem2025.Definitions.area
import PicksTheorem2025.Definitions.winding
import Mathlib.Tactic.Ring

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]


theorem Point_in_Box_le_r (r : Nat) (p : Point ℤ) (h1 : p ∈ Box2d r) : supNorm p ≤ r := by
  by_cases h1_le_2 :|p.1| ≤ |p.2|
  have supNorm_eq_p2: supNorm p = |p.2| := by
    sorry
  sorry
  sorry

open SignType

omit [IsStrictOrderedRing K] in
theorem dang_switch_order (u v : Point R) : (dang u v : K) = - dang v u := by
  have part_one_eq : abs ((sign u.1 - sign v.1):K) = |((sign v.1 - sign u.1):K)| := by
    have distr_neg (a b : K) : - (a -b) = (b - a) := by ring
    rw [← abs_neg, distr_neg]
  have part_two_neg_eq : (sign (u.1 * v.2 - u.2 * v.1) :K) = - sign (v.1 * u.2 - v.2 * u.1) := by
    have det_neg_eq (a1 a2 b1 b2 : R): (a1 * b2 - a2 * b1) = -(b1 * a2 - b2 * a1) := by ring
    rw [det_neg_eq,Left.sign_neg]
    simp

  change |((sign u.1 - sign v.1):K)| * sign (u.1 * v.2 - u.2 * v.1) / 4
      = - (|((sign v.1 - sign u.1):K)| * sign (v.1 * u.2 - v.2 * u.1) / 4)
  rw [part_one_eq,part_two_neg_eq]
  simp
  rw [neg_div]


theorem dang_change_sign (u v : Point R) : (dang u v : K) = dang (-u) (-v) := by sorry
