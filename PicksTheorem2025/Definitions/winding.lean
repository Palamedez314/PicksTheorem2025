import PicksTheorem2025.Definitions.polygon

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

open SignType

-- Discrete ANGle measure
def dang (u v : R × R) : K :=
  |((sign u.1 - sign v.1):K)| * sign (u.1 * v.2 - u.2 * v.1) / 4

def Box1d (r : Nat) := Finset.image (fun n ↦ Int.ofNat n - Int.ofNat r) (Finset.range (2*r +1))
def Box2d (r : Nat) := Finset.instSProd.sprod (Box1d r) (Box1d r)

-- Weighted sum of Enclosed Lattice Points
def welp (u v : ℤ × ℤ) (r : Nat) /-(h1 : maximum u ≤ r ∧ maximum v ≤ r)-/: K :=
  ∑ b ∈ (Box2d r), dang (u-b) (v-b)
