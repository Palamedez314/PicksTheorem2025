import PicksTheorem2025.Definitions.polygon
import PicksTheorem2025.Definitions.winding

--macro polygon:term "[" index:term "]" : term => `(($polygon).vertex ($index))

instance toPolygon {R : Type} (l : List (Point R)) (h : l.length > 0 := by decide)
    : Polygon R (l.length-1) where
  vertex (i) := l[Fin.val i]'(by
    have h1 : l.length - 1 + 1 = l.length := by
      calc
      l.length - 1 + 1 = max l.length 1 := by apply Nat.sub_add_eq_max
      max l.length 1 = l.length := by apply max_eq_left h
    nth_rewrite 2 [← h1]
    apply i.is_lt)

def p1 : Point Int := ⟨1, 1⟩
def p2 : Point Int := ⟨1, 2⟩
def p3 : Point Int := ⟨2, 1⟩
def p4 := p1

def l := [p1,p2,p3,p4]
def h : l.length > 0 := by decide
def P := toPolygon l h

#check p1 + p2


#eval (Box2d 5).card

def q0 : Int × Int := ⟨ 1, 2⟩
def q1 : Int × Int := ⟨-1, 1⟩
def q2 : Int × Int := ⟨ 2, 1⟩
def q3 : Int × Int := ⟨ 0, 1⟩

#eval q2-q3
#eval (welp q0 q1 3 : Rat)


#eval q0
#eval (dang q1 q0 : Rat)
