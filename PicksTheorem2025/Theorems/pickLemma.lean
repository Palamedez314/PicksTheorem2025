import PicksTheorem2025.Definitions.polygon
import PicksTheorem2025.Definitions.area
import PicksTheorem2025.Definitions.winding

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

-- theorem point_in_Box_le_r (r : Nat) (p : Point ℤ) : p ∈ Box2d r ↔ supNorm p ≤ r := by
--   constructor
--   · by_cases h1_le_2 :|p.1| ≤ |p.2|
--     · have supNorm_eq_p2: supNorm p = |p.2| := by
--         sorry
--       sorry
--     sorry
--   sorry

def PolygonBound (P : Polygon ℤ) : Nat := sorry

theorem polygon_bounded (P : Polygon ℤ)
    : ∀ r : Nat, r ≥ (PolygonBound P) → isBounded P r := by sorry



omit [IsStrictOrderedRing K] in

theorem dang_neg_symm (u v : Point R) :
    - dang v u = (dang u v : K) := by
  unfold dang
  rw [abs_sub_comm, ← neg_sub (v.2 * u.1),
    mul_comm v.2, mul_comm v.1, Left.sign_neg]
  rw [SignType.coe_neg, mul_neg, neg_div, neg_neg]



omit [IsStrictOrderedRing K] in
open SignType in

theorem dang_neg_neg (u v : Point R) :
    dang (-u) (-v) = (dang u v : K) := by
  unfold dang
  rw [abs_sub_comm]
  simp only [Prod.fst_neg, Left.sign_neg, coe_neg, sub_neg_eq_add, Prod.snd_neg, mul_neg, neg_mul,
    neg_neg]
  rw [add_comm, ← sub_eq_add_neg]



def leftBoxwithBorder (r : Nat) (u _v : Point ℤ) :=
  Finset.Icc ((-r : ℤ), (-r : ℤ)) (u.1 - 1, r)

def rightBoxwithBorder (r : Nat) (_u v : Point ℤ) :=
  Finset.Icc (v.1 + 1, (-r : ℤ)) (r, r)

def middleBox (r : Nat) (u v : Point ℤ) :=
  Finset.Icc (u.1, (-r : ℤ)) (v.1, r)

def bottomBox (r : Nat) (u v : Point ℤ) :=
  Finset.Icc (u.1, (-r: ℤ)) (v.1, u.2 + v.2 - r - 1)

def bluebox (r : Nat) (u v : Point ℤ) : Finset (Point ℤ) :=
  Finset.Icc (u.1, u.2 + v.2 - r) (v.1, r)



lemma and_iff_and_of_iff {a b c : Prop} : (a ↔ b) → (c ∧ a ↔ c ∧ b) := by
    intro hiff
    rw [hiff]



-- Das stimmt noch nicht ganz, die Box kann nach unten rausgehen
theorem middleBoxPartition
    (r : Nat) (u v : Point ℤ)
    (htemp1 : u.2 + v.2 ≥ 0) (hu : u ∈ Box2d r) (hv : v ∈ Box2d r):
    middleBox r u v = bottomBox r u v ∪ bluebox r u v
    := by
  ext x
  unfold middleBox bottomBox bluebox
  unfold Box2d at *
  simp [Prod.le_def] at *
  have upper_bound_u_v : u.2 + v.2 - r ≤ r :=by simp[hu.right.right,hv.right.right,add_le_add]
  rw [and_and_and_comm]
  nth_rewrite 2 [and_and_and_comm]
  nth_rewrite 3 [and_and_and_comm]
  rw [← and_or_left]
  apply and_iff_and_of_iff
  -- have temp (r:ℕ): -r ≤ x.2 ↔ ↑0 ≤ x.2 + r := by rw[←zero_sub r,tsub_le_iff_left, add_comm]
  -- nth_rewrite 2[←zero_sub]
  rw[add_comm x.2]
  rw[←tsub_le_iff_left]
  have sub_one_le (a:ℤ): a-1 ≤ a := by simp
  rw[Int.le_sub_one_iff]

  have upper_bound_u_v : u.2 + v.2 - r ≤ r :=by simp[hu.right.right,hv.right.right,add_le_add]

  by_cases lt_middle_box_bound : x.2 < u.2 + v.2 - r

  ·(have lower_bound : -r ≤ x.2 ∧ x.2 < u.2 + v.2 - r ∨ u.2 + v.2 -r ≤ x.2 ∧ x.2 ≤ r ↔ -r ≤ x.2
      := by
        ·calc -r ≤ x.2 ∧ x.2 < u.2 + v.2 - r ∨ u.2 + v.2 -r ≤ x.2 ∧ x.2 ≤ r
          _ ↔ -r ≤ x.2 ∧ x.2 < u.2 + v.2 - r ∨ False ∧ x.2 ≤ r
            := by rw[(Iff.intro (Int.not_le.mpr lt_middle_box_bound) False.elim)]
          _ ↔ -r ≤ x.2 ∧ True ∨ False ∧ x.2 ≤ r := by rw[(iff_true_intro lt_middle_box_bound)]
          _ ↔ -r ≤ x.2 ∧ True ∨ False := by rw[false_and]
          _ ↔ -r ≤ x.2 := by rw[or_false,and_true]

    constructor
    --Hinrichtung
    ·(intro lh_side
      rw[(Iff.intro (Int.not_le.mpr lt_middle_box_bound) False.elim),false_and,or_false]
      exact (And.intro lh_side.left lt_middle_box_bound))
    --Rückrichtung
    ·(intro rh_side
      constructor
      ·exact lower_bound.mp rh_side
      ·exact (Or.elim rh_side (fun a ↦
          (le_trans (Int.le_of_lt a.right) upper_bound_u_v))
        (·.right))))

  --case 2:
  ·(have ge_middle_box_bound := Int.lt_add_one_iff.mp (Int.not_le.mp lt_middle_box_bound)
      --keine Ahnung, warum hier not_le.mp hier ein +1 hinzufügt
    constructor
    --Hinrichtung
    ·(intro lh_side
      rw[(iff_true_intro ge_middle_box_bound), true_and]
      rw[(Iff.intro lt_middle_box_bound False.elim), and_false, false_or]
      exact lh_side.right)
    --Rückrichtung
    ·(intro rh_side
      constructor
      ·(apply (le_trans' ge_middle_box_bound)
        apply (Int.add_le_add_iff_right r).mp
        simp[htemp1])
      ·exact (Or.elim rh_side (fun a ↦
          (le_trans (Int.le_of_lt a.right) upper_bound_u_v))
        (·.right))))


theorem BoxPartition
    {r : Nat} {u v : Point ℤ} (hu : u ∈ Box2d r) (hv : v ∈ Box2d r)
    (hx : u.1 < v.1) (hy : u.2 + v.2 ≥ 0)
    : Box2d r = leftBoxwithBorder r u v ∪ rightBoxwithBorder r u v
              ∪ bottomBox r u v ∪ bluebox r u v
    := by
  rw [Finset.union_assoc]
  rw [← middleBoxPartition r u v]
  ext x
  unfold leftBoxwithBorder rightBoxwithBorder middleBox Box2d
  simp [Prod.le_def]
  nth_rewrite 2 [and_and_and_comm]
  nth_rewrite 3 [and_and_and_comm]
  nth_rewrite 4 [and_and_and_comm]
  rw [← or_and_right, ← or_and_right, and_comm]
  nth_rewrite 4 [and_comm]
  sorry



theorem sum_bluebox_dang_sub_sub --formally known as case3
    {r : Nat} {u v : Point ℤ} (hu : u ∈ Box2d r) (hv : v ∈ Box2d r) (huv : v.1 < u.1) :
    ∑ p ∈ bluebox r u v, (dang (u-p) (v-p) : K) = 0
    := by
  let f (p : Point ℤ) : K := dang (u-p) (v-p)
  let g (p : Point ℤ) : Point ℤ := u + v - p
  have hg₁ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p + f (g p) = 0 := by
    intro p hp
    unfold f g
    have h1 : u - (u + v - p) = - (v - p) := by rw[add_sub_assoc, sub_add_cancel_left]
    have h2 : v - (u + v - p) = - (u - p) := by rw[add_comm, add_sub_assoc, sub_add_cancel_left]
    rw[h1, h2, dang_neg_neg, ← dang_neg_symm, neg_add_cancel]
  have hg₃ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p ≠ 0 → g p ≠ p := by
    have h1 : (2 : K) ≠ 0 := by
      rw[ne_comm]
      apply LT.lt.ne
      rw [← one_add_one_eq_two]
      apply lt_add_of_pos_of_lt zero_lt_one
      exact zero_lt_one
    intro p hp h2 h3
    have h4 : f p + f (g p) = 0 := hg₁ p hp
    rw [h3] at h4
    have h5 : f p + f p = 2 * f p := by ring
    have h6 : 2 * f p = 2 * 0 := by rw [h5, ← mul_zero (2 : K)] at h4; assumption
    have h7 : f p = 0 := by apply mul_left_cancel₀ h1 h6
    exact h2 h7
  have g_mem : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g p ∈ bluebox r u v := by
    intro p hp
    simp [bluebox, g, Prod.le_def] at hp ⊢
    grind
  have hg₄ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g (g p) = p := by
    intro p hp
    unfold g
    simp
  apply Finset.sum_involution (fun a _ => g a) hg₁ hg₃ g_mem hg₄

-- theorem box_values (r : Nat) : Box1d r = {k : Int | k > -(r+1) ∧ k < (r+1)} := by
--   ext x
--   rw [Box1d]
--   simp only [Finset.coe_Icc, Set.mem_Icc, neg_add_rev, Int.reduceNeg, gt_iff_lt,
--     add_neg_lt_iff_lt_add, Set.mem_setOf_eq]
--   rw [Int.lt_add_one_iff, ← sub_lt_iff_lt_add, neg_sub_comm, sub_lt_iff_lt_add,
--     Int.lt_add_one_iff]

theorem termwise_pick {u v : Point ℤ} {r : Nat} (hu : supNorm u ≤ r) (hv : supNorm v ≤ r)
    : welp u v r = trapezoidArea (Int.cast : Int → K) u v
    := by
  unfold welp trapezoidArea

  sorry



-- langfristig überarbeiten: Finsupp-Summe in welp, damit explizites r redundant wird
theorem pick_lemma (P : Polygon ℤ)
    : ∀ r : Nat, r ≥ (PolygonBound P) →
      (polygonArea (Int.cast : ℤ → K) P = ∑ i, welp (P.vertex i) (P.vertex (i+1)) r)
    := by
  intro r hr
  unfold polygonArea
  apply Finset.sum_congr
  · rfl
  · intro i hi
    apply polygon_bounded at hr
    let u := (P.vertex i)
    let v := (P.vertex (i + 1))
    change trapezoidArea Int.cast u v = welp u v r
    have hu : supNorm u ≤ r := by apply hr
    have hv : supNorm v ≤ r := by apply hr
    rw[termwise_pick hu hv]
