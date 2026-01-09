import PicksTheorem2025.Definitions.polygon

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

open SignType

-- dang = Discrete ANGle measure
def dang (u v : Point R) : K :=
  |((sign u.1 - sign v.1):K)| * sign (u.1 * v.2 - u.2 * v.1) / 4

--not in use right now: def Box1d (r : Nat) := Finset.Icc (-r : ℤ) r

-- 2d box subset of ℤ^2 with radius r around the origin
def Box2d (r : Nat) := Finset.Icc ((-r : ℤ), (-r : ℤ)) (r, r)

-- welp = Weighted sum of Enclosed Lattice Points
def welp (u v : Point ℤ) (r : Nat) /-(h1 : maximum u ≤ r ∧ maximum v ≤ r)-/: K :=
  ∑ b ∈ (Box2d r), dang (u - b) (v - b)
