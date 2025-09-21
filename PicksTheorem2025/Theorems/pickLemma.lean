import PicksTheorem2025.Definitions.polygon
import PicksTheorem2025.Definitions.area
import PicksTheorem2025.Definitions.winding
import Mathlib.Tactic

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]


theorem Point_in_Box_le_r (r : Nat) (p : Point ℤ) (h1 : p ∈ Box2d r) : supNorm p ≤ r := by
  by_cases h1_le_2 :|p.1| ≤ |p.2|
  have supNorm_eq_p2: supNorm p = |p.2| := by
    sorry
  sorry
  sorry

theorem dang_switch_order (u v : Point R) : (dang u v : K) = - dang v u := by sorry


theorem dang_change_sign (u v : Point R) : (dang u v : K) = dang (-u) (-v) := by sorry



def bluebox_x (u v : Point ℤ) := Finset.image
    --argumente vor .toNat vielleicht im Nachhinein verändern. hier haben wir uns es leicht gemacht
    (fun n ↦ v.1 + Int.ofNat n) (Finset.range (|u.1 - v.1|.toNat + 1))
def bluebox_y (r : Nat) (u v : Point ℤ) := Finset.image
    (fun n ↦ v.2 + u.2 - r + Int.ofNat n) (Finset.range (2*r - (v.2 + u.2).toNat + 1))

def bluebox (r : Nat) (u v : Point ℤ) : Finset (Point ℤ) :=
  Finset.instSProd.sprod (bluebox_x u v) (bluebox_y r u v)

theorem case3 (r : Nat) (u v : Point ℤ) (hu : u ∈ (Box2d r)) (hv : v ∈ (Box2d r)) (huv : u.1 > v.1)
    : ∑ p ∈ (bluebox r u v), (dang (u-p) (v-p) : K) = 0 := by

  let f : Point ℤ → K := fun p ↦ (dang (u-p) (v-p) : K)
  let g : (p : Point ℤ) → (p ∈ bluebox r u v) → Point ℤ := fun p _ ↦ u + v - p
  have hg₁ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p + f (g p hp) = 0 := by
    intro p hp
    unfold f g
    have h1 : u - (u + v - p) = - (v - p) := by rw[add_sub_assoc, sub_add_cancel_left]
    have h2 : v - (u + v - p) = - (u - p) := by rw[add_comm, add_sub_assoc, sub_add_cancel_left]
    rw[h1, h2, dang_change_sign, dang_switch_order, neg_add_cancel]
  have hg₃ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p ≠ 0 → g p hp ≠ p := by
    have h1 : (2 : K) ≠ 0 := by
      rw[ne_comm]
      apply LT.lt.ne
      rw [← one_add_one_eq_two]
      apply lt_add_of_pos_of_lt zero_lt_one
      exact zero_lt_one
    intro p hp h2 h3
    have h4 : f p + f (g p hp) = 0 := hg₁ p hp
    rw [h3] at h4
    have h5 : f p + f p = 2 * f p := by ring
    have h6 : 2 * f p = 2 * 0 := by rw [h5, ← mul_zero (2 : K)] at h4; assumption
    have h7 : f p = 0 := by apply mul_left_cancel₀ h1 h6
    exact h2 h7

  -- schwieriger Teil des Beweises, bei dem die
  --(gerade relativ schlechte) Definition von bluebox_x bzw _y aufgegriffen wird
  have g_mem : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g p hp ∈ bluebox r u v := sorry

  have hg₄ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g (g p hp) (g_mem p hp) = p := by
    intro p hp
    unfold g
    simp
  apply Finset.sum_involution g hg₁ hg₃ g_mem hg₄
