import PicksTheorem2025.Theorems.pickLemma

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def openPointInterval (p q : Point K) : Set (Point K) :=
  AffineMap.lineMap p q '' Set.Ioo (0 : K) 1

def closedPointInterval (p q : Point K) : Set (Point K) :=
  AffineMap.lineMap p q '' Set.Icc (0 : K) 1

class AngleMeasure {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (μ : Point K → Point K → K) where
  scaling (u v : Point K) (a : K) (ha : a > 0) : μ (a • u) v = μ u (a • v)
  antisymm (u v : Point K) : μ u v = - μ v u
  neg_neg (u v : Point K) : μ (-u) (-v) = μ u v
  addition (u v r : Point K) (hr : r ∈ closedPointInterval u v) :
      μ u v = μ u r + μ r u
  normalisation : μ (1,0) (0,1) = 4⁻¹

variable (μ : Point K → Point K → K) [AngleMeasure μ] (P : Polygon K)

def windingNumber (q : Point K) : K :=
  ∑ i : Fin P.len, μ (P.vertex i.castSucc - q) (P.vertex i.succ - q)

-- TODO: wie gehe ich mit Polygon ℤ bzw. Polygon K um??
-- TODO: beweisen
theorem doubleSumLemma (P : Polygon ℤ) (r : ℕ) (hr : getBound P ≤ r) :
    (∑ i : Fin (P.len + 1), welp (P.vertex i) (P.vertex (i+1)) r : K) = ∑ q ∈ Box2d r, windingNumber (dang : Point K → Point K → K) P q
    := by sorry

def turningAngle (i : Fin (P.len + 1)) : K :=
  μ (P.vertex (i + 1) - P.vertex i) (P.vertex i - P.vertex (i - 1))

-- TODO: Jordan 1 und 2 aufschreiben
theorem jordan_1 : True := sorry
theorem jordan_2 : True := sorry

theorem jordan_3a (i : Fin (P.len + 1)) (q : Point K)
  (hq : q ∈ openPointInterval (P.vertex (i - 1)) (P.vertex i)) :
    windingNumber μ P q = 2⁻¹
    := sorry

theorem jordan_3b (i : Fin (P.len + 1)) : windingNumber μ P (P.vertex i) = turningAngle μ P i
    := sorry

theorem umlaufsatz : ∑ i : Fin P.len, turningAngle μ P i.succ = 1
    := sorry

-- #check FloorRing.ceil

def linearInterpolation (p q : Point K) (x : K) : Point K :=
  AffineMap.lineMap p q x

-- #eval (Int.floor ((0.8 : ℚ) * 2))

-- TODO: über Mathlib klauen!
def polygonPath (P : Polygon K) (x : AddCircle (1 : K)) : Point K
    := sorry

-- def polygonInterior := {q : Point K | windingNumber μ P q = 1}
-- Definition über Jordan-Theoreme!
def polygonInterior [Field K] (P : Polygon K) : Set (Point K) := sorry
def polygonBorder := (polygonPath P) '' (Set.univ)

theorem borderImage (P : Polygon K)
    : polygonBorder P = ⋃ i : Fin (P.len+1), closedPointInterval (P.vertex i) (P.vertex (i+1))
  := sorry

#synth MeasureTheory.MeasureSpace ℝ
#print MeasureTheory.volume

-- kann man kappa irgendwie loswerden und das auch schön über coersions machen?
-- warum reicht @[coe] nicht?
@[coe]
def IntPolygon.toFieldPolygon {K : Type*} [Field K] : Polygon ℤ → Polygon K :=
  fun P ↦ {len := P.len, vertex := fun i ↦ (κ Int.cast (P.vertex i))}
instance {K : Type*} [Field K] : Coe (Polygon ℤ) (Polygon K)
  := ⟨IntPolygon.toFieldPolygon⟩

-- TODO: def "isSimple"
def isSimple (P : Polygon K) : Prop := sorry

open MeasureTheory

variable (μ : Point ℝ → Point ℝ → ℝ) [AngleMeasure μ] (P : Polygon ℤ)

#print ENNReal

def innerPoints : Set (Point ℤ) :=
  {v : Point ℤ | κ Int.cast v ∈ polygonInterior (P : Polygon ℝ)}
def borderPoints : Set (Point ℤ) :=
  {v : Point ℤ | κ Int.cast v ∈ polygonBorder (P : Polygon ℝ)}

theorem innerPointsFinite : (innerPoints P).Finite := sorry
theorem borderPointsFinite : (borderPoints P).Finite := sorry

-- müssen wir Absolutbetrag nehmen oder wissen wir etwas über das Vorzeichen von polygonArea?
theorem shoelaceFormula : volume (polygonInterior (P : Polygon ℝ))
    = Real.nnabs (polygonArea (Int.cast : ℤ → ℝ) P)
  := by sorry

theorem pick_theorem (hs : isSimple P) :
    volume (polygonInterior (P : Polygon ℝ)) =
    (innerPointsFinite P).toFinset.card + ((borderPointsFinite P).toFinset.card / 2) - 1
  := sorry
