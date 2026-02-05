import PicksTheorem2025.Theorems.PickLemma
import PicksTheorem2025.Definitions.polygon

class AngleMeasure {K : Type*} (μ : Point K → Point K → K)
    extends Field K, LinearOrder K, IsStrictOrderedRing K where
  scaling (u v : Point K) (a : K) (ha : a > 0) : μ (a • u) v = μ u (a • v)
  antisymm (u v : Point K) : μ u v = - μ v u
  neg_neg (u v : Point K) : μ (-u) (-v) = μ u v
  addition (u v : Point K) (s : K) (hs : s ∈ Set.Icc 0 1) :
      μ u v = μ u (u + s • (v - u)) + μ (u + s • (v - u)) u
  normalisation : μ (1,0) (0,1) = 4⁻¹

variable {K : Type*} (μ : Point K → Point K → K) [AngleMeasure μ]

def windingNumber (P : Polygon K) (q : Point K) : K :=
  ∑ i : Fin P.len, μ (P.vertex i.castSucc - q) (P.vertex i.succ - q)

theorem jordan_1 : True := sorry
theorem jordan_2 : True := sorry
theorem jordan_3 (P : Polygon K) (s : K) (hs : s ∈ Set.Ioo 0 1):
   P.vertex i.castSucc + s • (P.vertex i.succ - P.vertex i.castWSucc) =
    := sorry
theorem jordan_1 : True := sorry

def turningAngle (P : Polygon K) (i : Fin P.len) : K :=
  μ (P.vertex i.succ - P.vertex i.castSucc) (P.vertex i.castSucc - P.vertex (i.castSucc - 1))

theorem umlaufsatz (P : Polygon K) : ∑ i : Fin P.len, turningAngle μ P i = 1
    := sorry

theorem pick_theorem : True := sorry
