import Semileanear2024.pick.polygon

/- ---------------------------------------------------------------------------
Formalizing Pick's Theorem... and learning LEAN along the way.

We formalize Pick's theorem for closed integer polygons.
Here the polygons are not required to be simple.
This is the algebraic half of Pick's theorem,
the umlaufsatz being the geometric other half.
--------------------------------------------------------------------------- -/

#eval square.area  -- 4
#eval square.nelp  -- 4

#eval diamond.area  -- 2
#eval diamond.nelp  -- 2

#eval eight.area  -- 2
#eval eight.nelp  -- 2

-- example : square.area = 4 := by decide  -- currently gets stuck
-- example : square.nelp = 4 := by decide  -- currently gets stuck

------------------------------------------------------------------------------
-- Pick's theorem states (in its algebraic form) that for any lattice polygon
-- the enclosed area equals the number of enclosed lattice points.

theorem area_eq_nelp : ∀ p : Polygon, p.isInteger → p.area = p.nelp := by
  sorry
