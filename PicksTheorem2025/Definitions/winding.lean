import PicksTheorem2025.Definitions.polygon
import Mathlib.Data.Sign.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Group.Abs

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : R → K}

open SignType

-- discrete angle measure
def discangle (u v : Point R) : K :=
  |((sign u.1 - sign v.1):K)| * sign (u.1 * v.2 - u.2 * v.1) / 4


-- Tests
def q0 : Point Int := ⟨ 1, 2⟩
def q1 : Point Int := ⟨-1, 1⟩
def q2 : Point Int := ⟨ 2, 1⟩
def q3 : Point Int := ⟨ 0, 1⟩

#eval q0
#eval (discangle q1 q0 : Rat)
