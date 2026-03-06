import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Ring.Regular
import Mathlib.Analysis.Normed.Ring.Lemmas
import PicksTheorem2025.Definitions.area
import PicksTheorem2025.Definitions.winding


variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem is_bound_of_ge_bound (P : Polygon ℤ)
    : ∀ r : Nat, r ≥ (getBound P) → isBounded P r := by
  intro r hr
  simpa [getBound, isBounded] using hr

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

abbrev leftBox (r : Nat) (u _v : Point ℤ) :=
  Finset.Icc ((-r : ℤ), (-r : ℤ)) (u.1 - 1, r)

abbrev rightBox (r : Nat) (_u v : Point ℤ) :=
  Finset.Icc (v.1 + 1, (-r : ℤ)) (r, r)

abbrev middleBox (r : Nat) (u v : Point ℤ) :=
  Finset.Icc (u.1, (-r : ℤ)) (v.1, r)

abbrev bottomBox (r : Nat) (u v : Point ℤ) :=
  Finset.Icc (u.1, (-r: ℤ)) (v.1, u.2 + v.2 - r - 1)

abbrev bluebox (r : Nat) (u v : Point ℤ) : Finset (Point ℤ) :=
  Finset.Icc (u.1, u.2 + v.2 - r) (v.1, r)

abbrev bottomBoxSides (r : Nat) (u v : Point ℤ) : Finset (Point ℤ) :=
  {u.1, v.1} ×ˢ (Finset.Icc (-r: ℤ) (u.2 + v.2 - r - 1))

abbrev bottomBoxInner (r : Nat) (u v : Point ℤ) : Finset (Point ℤ) :=
  Finset.Icc (u.1 + 1, (-r: ℤ)) (v.1 - 1, u.2 + v.2 - r - 1)

local macro "magic" : tactic =>
  `(tactic| (simp [Prod.le_def, Finset.disjoint_iff_ne] at *; omega))

theorem BoxPartition
    {r : Nat} (u v : Point ℤ) (hu : u ∈ Box2d r) (hv : v ∈ Box2d r)
    (hx : u.1 < v.1) (hy : u.2 + v.2 ≥ 0)
    : Box2d r =
      ((leftBox r u v).disjUnion (rightBox r u v) (by magic)
        |>.disjUnion (bottomBox r u v) (by magic)
        |>.disjUnion (bluebox r u v) (by magic))
    := by
  ext x
  magic

theorem sum_leftBox_dang_sub_sub --Fall 1
    {r : Nat} {u v : Point ℤ} (huv : u.1 < v.1) :
    ∑ p ∈ leftBox r u v, (dang (u-p) (v-p) : K) = 0
    := by
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_Icc, Prod.le_def] at hp
  rw [dang]
  simp only [Prod.fst_sub, Prod.snd_sub, div_eq_zero_iff, mul_eq_zero, abs_eq_zero,
    OfNat.ofNat_ne_zero, or_false]
  rw [sign_pos (by omega), sign_pos (by omega)]
  simp

theorem sum_rightBox_dang_sub_sub --Fall 2
    {r : Nat} {u v : Point ℤ} (huv : u.1 < v.1) :
    ∑ p ∈ rightBox r u v, (dang (u-p) (v-p) : K) = 0
    := by
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Finset.mem_Icc, Prod.le_def] at hp
  rw [dang]
  simp only [Prod.fst_sub, Prod.snd_sub, div_eq_zero_iff, mul_eq_zero, abs_eq_zero,
    OfNat.ofNat_ne_zero, or_false]
  rw [sign_neg (by omega), sign_neg (by omega)]
  simp

theorem sum_bluebox_dang_sub_sub --Fall 3
    {r : Nat} {u v : Point ℤ} :
    ∑ p ∈ bluebox r u v, (dang (u-p) (v-p) : K) = 0
    := by
  let f (p : Point ℤ) : K := dang (u-p) (v-p)
  let g (p : Point ℤ) : Point ℤ := u + v - p
  have hg₁ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p + f (g p) = 0 := by
    intro p hp
    unfold f g
    have h1 : u - (u + v - p) = - (v - p) := by abel
    have h2 : v - (u + v - p) = - (u - p) := by abel
    rw[h1, h2, dang_neg_neg, ← dang_neg_symm, neg_add_cancel]
  have hg₃ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), f p ≠ 0 → g p ≠ p := by
    intro p hp h2 h3
    have h4 : f p + f (g p) = 0 := hg₁ p hp
    rw [h3] at h4
    have h5 : f p + f p = 2 * f p := by ring
    have h6 : 2 * f p = 2 * 0 := by rw [h5, ← mul_zero (2 : K)] at h4; assumption
    have h7 : f p = 0 := by apply mul_left_cancel₀ two_ne_zero h6
    exact h2 h7
  have g_mem : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g p ∈ bluebox r u v := by
    intro p hp
    simp [bluebox, g, Prod.le_def] at hp ⊢
    magic
  have hg₄ : ∀ (p : Point ℤ) (hp : p ∈ bluebox r u v), g (g p) = p := by
    intro p hp
    unfold g
    simp
  apply Finset.sum_involution (fun a _ => g a) hg₁ hg₃ g_mem hg₄

theorem bottomBoxPartition
    {r : Nat} {u v : Point ℤ} (h : u.1 < v.1) :
    bottomBox r u v =
      (bottomBoxSides r u v).disjUnion (bottomBoxInner r u v) (by magic) := by
  ext ⟨a, b⟩
  magic

theorem sum_bottomBox_dang_sub_sub --Fälle 4 und 5
    {r : Nat} {u v : Point ℤ} (hu : u ∈ Box2d r) (hv : v ∈ Box2d r) (huv : u.1 < v.1)
    (huv2 : 0 ≤ u.2 + v.2) :
    ∑ p ∈ bottomBox r u v, (dang (u-p) (v-p) : K) = trapezoidArea (Int.cast : Int → K) u v
    := by
  rw [bottomBoxPartition huv, Finset.sum_disjUnion]
  have (p : Point ℤ) (hp : p ∈ bottomBoxSides r u v) :
      dang (u - p) (v - p) = (-4⁻¹ : K) := by
    simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hp
    rw [dang]
    simp only [Prod.fst_sub, Prod.snd_sub]
    rcases hp.1 with h | h
    · simp only [h, sub_self, sign_zero, SignType.coe_zero, zero_sub, abs_neg, zero_mul]
      rw [sign_pos (by omega), sign_neg]
      · norm_num
      · simp only [Int.neg_neg_iff_pos]
        apply mul_pos
        · magic
        · simpa
    · simp only [h, sub_self, sign_zero, SignType.coe_zero, sub_zero, mul_zero]
      rw [sign_neg (by omega), sign_neg]
      · norm_num
      · apply mul_neg_of_neg_of_pos
        · simpa
        · magic
  simp +contextual only [this, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_product,
    Finset.mem_singleton, huv.ne, not_false_eq_true, Finset.card_insert_of_notMem,
    Finset.card_singleton, Nat.reduceAdd, Int.card_Icc, sub_add_cancel, sub_neg_eq_add,
    nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
  have (p : Point ℤ) (hp : p ∈ bottomBoxInner r u v) :
      dang (u - p) (v - p) = (-2⁻¹ : K) := by
    simp only [Finset.mem_Icc, Prod.le_def] at hp
    rw [dang]
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [sign_neg (by omega), sign_pos (by omega), sign_neg]
    · norm_num
    · rw [sub_neg]
      trans 0
      · apply mul_neg_of_neg_of_pos
        · omega
        · magic
      · apply mul_pos
        · magic
        · omega
  simp +contextual only [this, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_Icc_prod,
    Int.card_Icc, sub_add_cancel, sub_neg_eq_add, nsmul_eq_mul, Nat.cast_mul]
  rw [trapezoidArea, ← Int.cast_natCast, Int.toNat_of_nonneg huv2,
    ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
  ring

theorem supNorm_le_iff {u : Point ℤ} {r : ℕ} : supNorm u ≤ r ↔ u ∈ Box2d r := by
  simp [supNorm, abs_le, Prod.le_def]
  omega

theorem termwise_pick {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {u v : Point ℤ} {r : Nat} (hu : u ∈ Box2d r) (hv : v ∈ Box2d r)
    : welp u v r = trapezoidArea (Int.cast : Int → K) u v
    := by
  unfold welp trapezoidArea
  wlog huv2 : 0 ≤ u.2 + v.2
  · replace hu : (-u) ∈ Box2d r := by magic
    replace hv : (-v) ∈ Box2d r := by magic
    specialize this (K := K) hu hv (by simp; omega)
    rw [Finset.sum_bij' (t := Box2d r) (g := fun b => dang (u - b) (v - b))
        (fun a _ => -a) (fun a _ => -a)
        (by magic) (by magic) (by simp) (by simp)] at this
    · rw [this]
      simp only [Prod.fst_neg, Int.cast_neg, sub_neg_eq_add, Prod.snd_neg, Int.cast_ofNat]
      rw [← neg_mul_neg]
      grind
    · intro a h
      rw [← dang_neg_neg]
      simp [add_comm]
  wlog huv : u.1 < v.1
  · by_cases huveq : u.1 = v.1
    · simp [huveq, sub_self, zero_mul, Int.cast_ofNat, zero_div, dang]
    · have hvu : v.1 < u.1 := by omega
      specialize this (K := K) hv hu (by magic) hvu
      simp +singlePass only [← dang_neg_symm, Finset.sum_neg_distrib, Int.cast_ofNat]
      rw [this]
      grind
  rw [BoxPartition u v hu hv huv huv2]
  simp only [Finset.sum_disjUnion]
  rw [sum_bluebox_dang_sub_sub]
  rw [sum_bottomBox_dang_sub_sub hu hv huv huv2]
  rw [sum_leftBox_dang_sub_sub huv]
  rw [sum_rightBox_dang_sub_sub huv]
  simp [trapezoidArea]

theorem pick_lemma (P : Polygon ℤ) (r : ℕ) (hr : getBound P ≤ r) :
    polygonArea (Int.cast : ℤ → K) P = ∑ i, welp (P.vertex i) (P.vertex (i+1)) r
    := by
  unfold polygonArea
  apply Finset.sum_congr
  · rfl
  · intro i hi
    apply is_bound_of_ge_bound at hr
    let u := (P.vertex i)
    let v := (P.vertex (i + 1))
    change trapezoidArea Int.cast u v = welp u v r
    have hu : supNorm u ≤ r := by apply hr
    have hv : supNorm v ≤ r := by apply hr
    rw [supNorm_le_iff] at hu hv
    rw [termwise_pick hu hv]

#print axioms pick_lemma
