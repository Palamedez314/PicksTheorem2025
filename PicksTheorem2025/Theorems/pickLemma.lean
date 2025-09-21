import PicksTheorem2025.Definitions.polygon
import PicksTheorem2025.Definitions.area
import PicksTheorem2025.Definitions.winding
import Mathlib.tactic.Ring

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
  have hg₁ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p + f (g p hp) = 0 := sorry
  have hg₃ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p ≠ 0 → g p hp ≠ p := by
    intro p hp h1 h2
    have h3 : f p + f (g p hp) = 0 := hg₁ p hp
    rw [h2] at h3
    have h4 : 2 * f p = 0 := sorry
    sorry

  have g_mem : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g p hp ∈ bluebox r u v := sorry
  have hg₄ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g (g p hp) (g_mem p hp) = p := by
    intro p hp
    unfold g
    simp
  sorry
  --apply Finset.sum_involution

def u : Point ℤ := sorry
def p : Point ℤ := sorry
#check u-p
