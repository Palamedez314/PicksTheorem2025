import PicksTheorem2025.Definitions.imports

variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

--abelian group of points later used with ℤ² and K²
def Point (R : Type) := R × R
instance Point_AddCommGroup [inst : AddCommGroup (R × R)] : AddCommGroup (Point R) := inst

def point_Cast : (R × R) → (Point R) := fun ⟨r , s⟩ ↦ ⟨r , s⟩

--definition of a polygon with len sides as a tuple of its corner points
class Polygon (R : Type) (len : Nat) where
  vertex : Fin (len + 1) → Point R

variable {len : Nat}

--additional properties of polygons
def isClosed (P : Polygon R len) := P.vertex 0 = P.vertex (Fin.ofNat (len +1) len)

def supNorm : Point R → R := fun p ↦ max |p.1| |p.2|
def isBounded (P : Polygon R len) (bound : Nat)
    := ∀ i : Fin (len+1), supNorm (P.vertex i) ≤ Nat.cast bound
