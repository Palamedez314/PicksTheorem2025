import PicksTheorem2025.Definitions.polygon
import Mathlib.Data.Sign.Defs

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : R → K}

namespace SignType

-- discrete angle measure
def discangle (u v : Point R) : K :=
  (sign u.1 - sign v.1) * sign (u.1 * v.2 - u.2 * v.1) / 4

def q0 : Point Int := ⟨ 1, 2⟩
def q1 : Point Int := ⟨-1, 1⟩
def q2 : Point Int := ⟨ 2, 1⟩

#eval q0
#eval discangle ℚ ℤ q0 q1
