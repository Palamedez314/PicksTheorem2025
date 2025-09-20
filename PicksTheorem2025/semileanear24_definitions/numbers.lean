import Mathlib

/- ---------------------------------------------------------------------------
This file is just a playgound for testing some ideas
-----------------------------------------------------------------------------/

------------------------------------------------------------------------------
-- The number system, without inclusion, needs cast

#check 0        -- 0 : ℕ
#check (0 : ℕ)  -- 0 : ℕ
#check (0 : ℤ)  -- 0 : ℤ
#check (0 : ℚ)  -- 0 : ℚ
#check (0 : ℝ)  -- 0 : ℝ
#check (0 : ℂ)  -- 0 : ℂ

#check (1 : ℤ) + (2 : ℚ)  -- ℤ
#eval  (1 : ℤ) + (2 : ℚ)  -- 3

------------------------------------------------------------------------------
-- Natural numbers as inductive type

inductive N where
  | zero : N
  | succ : N → N
  deriving Repr  -- enables #eval for debugging

#check N.zero
#check N.succ
#check N.zero.succ
#check N.zero.succ.succ

def fib (n : ℕ) : ℕ :=
match n with
| 0 => 1
| 1 => 1
| n+2 => fib (n+1) + fib n

#check fib
example : fib (n+2) = fib (n+1) + fib n := rfl

#eval fib 7 -- 21
example : fib 7 = 21 := rfl

------------------------------------------------------------------------------
-- Integers as inductive types

inductive Z where
  | ofN : N → Z
  | negSucc : N → Z
  deriving Repr  -- enables #eval for debugging

#check Z.ofN N.zero
#check Z.ofN N.zero.succ
#check Z.ofN N.zero.succ.succ
#check Z.negSucc N.zero
#check Z.negSucc N.zero.succ
#check Z.negSucc N.zero.succ.succ

------------------------------------------------------------------------------
-- Rational numbers ℚ from Mathlib

def x := 4/6 -- that's not a rational!
#check x  -- ℕ
#eval x   -- 0

def y := (1:ℚ)*4/6
#check y     -- ℚ
#eval y      -- (2 : Rat)/3
#eval y.num  -- 2
#eval y.den  -- 3

------------------------------------------------------------------------------
-- Cast ℤ to ℚ, conversely check whether a:ℚ is an integer by a.den = 1

def Rat.fraction (a b : Int) := (a:ℚ)/(b:ℚ)
infixr:70 " ℚ/ " => Rat.fraction

def z := 15 ℚ/ 3
#check z     -- ℚ
#eval z      -- 5
#eval z.num  -- 5
#eval z.den  -- 1

------------------------------------------------------------------------------
-- An array is a list with additional nice features

def l := [7, 8, 9] -- list
#check l      -- List ℕ
#eval l.size  -- invalid field 'size'

def a := #[7, 8, 9] -- array
#check a      -- Array ℕ
#eval a.size  -- 3
#eval a[0]    -- 7
#eval a[1]    -- 8
#eval a[2]    -- 9
#eval a[3]    -- failed to prove that index is valid

#eval a[(2 : Fin 3)] -- 9
#eval a[(3 : Fin 3)] -- 7
#eval a[(4 : Fin 3)] -- 8
