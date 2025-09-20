import PicksTheorem2025.Definitions.polygon
import Mathlib.Data.Sign.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.Bigoperators.Group.Finset.Sigma

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : R → K}

open SignType

-- Discrete ANGle measure
def dang (u v : R × R) : K :=
  |((sign u.1 - sign v.1):K)| * sign (u.1 * v.2 - u.2 * v.1) / 4


def Box1d (r : Nat) := Finset.image (fun n ↦ Int.ofNat n - Int.ofNat r) (Finset.range (2*r +1))
def Box2d (r : Nat) := Finset.instSProd.sprod (Box1d r) (Box1d r)

#eval (Box2d 5).card



-- Weighted sum of Enclosed Lattice Points
def welp (u v : ℤ × ℤ) (r : Nat) /-(h1 : maximum u ≤ r ∧ maximum v ≤ r)-/: K :=
  ∑ b ∈ (Box2d r), dang (u-b) (v-b)

-- tests
def q0 : Int × Int := ⟨ 1, 2⟩
def q1 : Int × Int := ⟨-1, 1⟩
def q2 : Int × Int := ⟨ 2, 1⟩
def q3 : Int × Int := ⟨ 0, 1⟩

#eval q2-q3
#eval (welp q0 q1 3 : Rat)


#eval q0
#eval (dang q1 q0 : Rat)
