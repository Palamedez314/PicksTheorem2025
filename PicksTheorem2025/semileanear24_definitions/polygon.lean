import Mathlib open Finset

/- ---------------------------------------------------------------------------
Formalizing Pick's Theorem... and learning LEAN along the way.

In this file we implement polygons with rational vertices and
calculate their area and the number of enclosed lattice points.
--------------------------------------------------------------------------- -/

def Rat.fraction (a b : Int) := (a : ℚ) / (b : ℚ)  -- short hand notation
infixr:70 " // " => Rat.fraction  -- infix, associate right, precedence 70

#eval 20 // 5 -- 4
#eval 30 // 8 -- (15 : Rat)/4
#eval 30 / 8  -- 3, be careful

------------------------------------------------------------------------------
-- Rational points in the plane

structure Point where  -- structure or class? also @[ext]?
  x : Rat              -- Rat or Int?
  y : Rat              -- Rat or Int?
  deriving Repr        -- enables #eval for debugging

#check Point    -- Type
#check Point.x  -- Int
#check Point.y  -- Int

def p0 : Point where
  x := -3
  y :=  2

#check p0  -- Point
#eval p0   -- { x := -3, y := 2 }

def p1 : Point := ⟨ 5, 3 ⟩
def p2 : Point := ⟨ -1, 7 ⟩
def p3 : Point := ⟨ -1, 7//2 ⟩

#eval p1   -- { x := 5, y := 3 }
#eval p2   -- { x := -1, y := 7 }
#eval p3   -- { x := -1, y := (7 : Rat)/2 }

def Point.add (u v : Point) : Point := ⟨ u.x + v.x, u.y + v.y ⟩
def Point.sub (u v : Point) : Point := ⟨ u.x - v.x, u.y - v.y ⟩
def Point.cross (u v : Point) : Rat := u.x * v.y - u.y * v.x
def Point.sprod (u v : Point) : Rat := u.x * v.x + u.y * v.y

#check Point.add p0 p1 -- p.add q : Point
#check p0.add p1       -- p.add q : Point
#check p0.add          -- Point → Point
#eval p0.add p1        -- { x := 2, y := 5 }

infixl:65 " + " => Point.add    -- left associative, precedence 65
infixl:65 " - " => Point.sub    -- left associative, precedence 65
infix:70 " × " => Point.cross   -- precedence 70
infix:70 " ⬝ " => Point.sprod   -- precedence 70

#eval p0       -- { x := -3, y := 2 }
#eval p1       -- { x := 5, y := 3 }
#eval p0 + p1  -- { x := 2, y := 5 }
#eval p0 - p1  -- { x := -8, y := -1 }
#eval p0 × p1  -- -19
#eval p0 ⬝ p1  -- -9

def Point.isInteger (q: Point) : Bool := -- or Prop?
  q.x.den = 1 ∧ q.y.den = 1

#eval p0.isInteger -- true
#eval p1.isInteger -- true
#eval p2.isInteger -- true
#eval p3.isInteger -- false

------------------------------------------------------------------------------
-- A polygon p is a cyclic list of points p_1, ..., p_n = p_0
-- We implement this as Nat → Point with some positive period

class Polygon where
  size : Nat
  ndeg : size > 0
  vert : Nat → Point
  cycl : ∀ i : Nat, vert i = vert (i+size)

-- notation:50 p:50 "[" i:50 "]" => (vert p i)
macro polygon:term "[" index:term "]" : term => `(($polygon).vert ($index))

instance toPolygon (arr : Array Point) (h : arr.size > 0 := by decide) : Polygon where
  size := arr.size
  ndeg := h
  vert (i) := arr[i % arr.size]'(Nat.mod_lt i h)
  cycl := by intro i; simp

def pl := toPolygon #[p0, p1, p2]

#check pl
#check pl.size
#check pl.ndeg
#check pl.vert
#check pl.cycl
#eval pl.size
#eval pl[0] -- p0
#eval pl[1] -- p1
#eval pl[2] -- p2
#eval pl[3] -- p0, repeats periodically

def Polygon.isInteger (p : Polygon) : Bool := -- or Prop?
  ∀ i : Fin p.size, p[i].isInteger -- or ∀ i : Nat, p[i].isInteger
  -- ∀ i : Fin p.size, p[i].x.den = 1 ∧ p[i].y.den = 1
  -- ∀ i : Fin p.size, (p.vert i).isInteger  -- p[i].x.den = 1 ∧ p[i].y.den = 1

#eval pl.isInteger -- true

def pl' := toPolygon #[p0, p1, p2, p3]
#eval pl'.isInteger -- false

------------------------------------------------------------------------------
-- We formalize the necessary properties for measuring areas and angles

class AreaMeasure where
  a : Point → Point → Rat -- Real?
  -- add the necessary properties here

class AngleMeasure where
  a : Point → Point → Rat -- Real?
  -- add the necessary properties here

------------------------------------------------------------------------------
-- calculate the enclosed area

def trapezoidArea (u v : Point) : Rat :=
  (u.x - v.x) * (u.y + v.y) / 2

def Polygon.area (p : Polygon) : Rat :=
  ∑ i ∈ range (p.size), trapezoidArea (p[i]) (p[i+1])

#eval pl.area   -- -19
#eval pl'.area  -- (-31 : Rat)/2

def square := toPolygon #[⟨ 1, 1⟩, ⟨-1, 1⟩, ⟨-1,-1⟩, ⟨ 1,-1⟩]
#eval square.area  -- 4

def diamond := toPolygon #[⟨ 1, 0⟩, ⟨ 0, 1⟩, ⟨-1, 0⟩, ⟨ 0,-1⟩]
#eval diamond.area  -- 2

def eight := toPolygon #[⟨ 1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨ 1,-1⟩, ⟨ -1,-1⟩, ⟨ 1,0⟩]
#eval eight.area  -- 2

------------------------------------------------------------------------------
-- We use axis crossings as our angle measure.
-- This has the advantage of being rational.

def Rat.abs (x : ℚ) : ℚ :=
if x < 0 then -x else x

#eval (42/(5:ℚ)).abs
#eval (-7/(2:ℚ)).abs
#eval (0:ℚ).abs

def Rat.sign (x : ℚ) : ℚ :=
if x < 0 then -1 else
if 0 < x then  1 else
0

#eval (42:ℚ).sign -- 1
#eval (-7:ℚ).sign -- -1
#eval ( 0:ℚ).sign -- 0

def axisCrossing (u v : Point) : ℚ :=
  (u.x.sign - v.x.sign).abs * (u × v).sign / 4

#eval axisCrossing p0 p1 -- -1/2
#eval axisCrossing p1 p2 -- 1/2
#eval axisCrossing p2 p0 -- 0

------------------------------------------------------------------------------
-- The umlaufzahl of a polygon is the sum of all its turning angles.
-- Please do not confuse 'turning number' and 'winding number' below.

def Polygon.umlaufzahl (p : Polygon) : Rat :=
  ∑ i ∈ range (p.size), axisCrossing (p[i+1] - p[i]) (p[i+2] - p[i+1])

#eval square.umlaufzahl   -- 1
#eval diamond.umlaufzahl  -- 1
#eval eight.umlaufzahl    -- 0

-- example : square.umlaufzahl = 1 := by decide  -- currently gets stuck

------------------------------------------------------------------------------
-- We calculate the winding number by counting axis crossings
-- Please do not confuse 'winding number' and 'turning number' above.

def Polygon.wind (p : Polygon) (q : Point := ⟨0,0⟩) : Rat :=
  ∑ i ∈ range (p.size), axisCrossing (p[i] - q) (p[i+1] - q)

#eval pl.wind -- 0

#eval square.wind ⟨0,0⟩ -- 1
#eval square.wind ⟨1,0⟩ -- (1 : Rat)/2
#eval square.wind ⟨1,1⟩ -- (1 : Rat)/4

#eval diamond.wind ⟨0,0⟩ -- 1
#eval diamond.wind ⟨1,0⟩ -- 0
#eval diamond.wind ⟨1,1⟩ -- 0

#eval eight.wind ⟨0,0⟩ -- 1
#eval eight.wind ⟨1,0⟩ -- (1 : Rat)/4
#eval eight.wind ⟨1,1⟩ -- (1 : Rat)/4

------------------------------------------------------------------------------
-- calculate the number of enclosed lattice points, 'nelp' for short

def Polygon.box (p : Polygon): Int :=
  max ⌈ abs (p[0].x) ⌉ ⌈ abs (p[0].y) ⌉ -- FIXME

def Polygon.nelp (p : Polygon): Rat := -- number of enclosed lattice points
    let L := Icc (-100 : ℤ) (100 : ℤ) -- FIXME should be {-box,...,box}
    ∑ i ∈ L, ∑ j ∈ L, p.wind ⟨i,j⟩

#eval square.area  -- 4
#eval square.nelp  -- 4

#eval diamond.area  -- 2
#eval diamond.nelp  -- 2

#eval eight.area  -- 2
#eval eight.nelp  -- 2

-- example : square.area = 4 := by decide  -- currently gets stuck
-- example : square.nelp = 4 := by decide  -- currently gets stuck
