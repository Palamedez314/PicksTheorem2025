import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Data.Sign.Defs
import PicksTheorem2025.Definitions.polygon


variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

open SignType

-- dang = Discrete ANGle measure
def dang (u v : Point R) : K :=
  |((sign u.1 - sign v.1):K)| * sign (u.1 * v.2 - u.2 * v.1) / 4

-- 2d box subset of ℤ^2 with radius r around the origin
abbrev Box2d (r : Nat) := Finset.Icc ((-r : ℤ), (-r : ℤ)) (r, r)

@[norm_cast, simp]
theorem SignType.coe_eq_zero {α : Type*} [AddGroup α] [One α]
    [NeZero (1 : α)] {x : SignType} :
    (x : α) = 0 ↔ x = 0 := by
  cases x <;> simp [NeZero.ne]

-- welp = Weighted sum of Enclosed Lattice Points
def welp (u v : Point ℤ) (r : Nat) /-(h1 : maximum u ≤ r ∧ maximum v ≤ r)-/: K :=
  ∑ b ∈ (Box2d r), dang (u - b) (v - b)
