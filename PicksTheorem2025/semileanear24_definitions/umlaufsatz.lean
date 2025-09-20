import Semileanear2024.pick.polygon

/- ---------------------------------------------------------------------------
Formalizing Pick's Theorem... and learning LEAN along the way.

We formalize the umlaufsatz for simply closed polygons.
Here the condition of being simple becomes necessary.
This is the geometric half of Pick's theorem,
the area = nelp equation being the other half.
--------------------------------------------------------------------------- -/

#eval square.umlaufzahl   -- 1
#eval diamond.umlaufzahl  -- 1
#eval eight.umlaufzahl    -- 0

-- example : square.umlaufzahl = 1 := by decide  -- currently gets stuck

------------------------------------------------------------------------------
-- A polygon is simple iff ({vertices},open edges) are mutually disjoint

def Polygon.isSimple (p : Polygon) : Bool :=
  sorry

------------------------------------------------------------------------------
-- The umlaufsatz for simply closed polygons -- FIXME orientation?

theorem umlaufsatz : ∀ p : Polygon, p.isSimple → p.umlaufzahl = 1 := by
  sorry
