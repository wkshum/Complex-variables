import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

open Complex



/-

Basic operations
1234
-/


-- i times i equals -1
example : I*I =-1 := I_mul_I


-- If x and y are the real and imaginary part of z respectively, then x+i*y=z
example (z:ℂ) (x y : ℝ) (hx : x=z.re) (hy : y = z.im) : x+I*y = z :=
  calc
    x + I*y = x + y*I := by ring
          _ = z.re + (z.im)*I := by rw [hx, hy]
          _ = z := re_add_im z

-- If x and y are the real and imaginary part of z respectively, then z = x+i*y
example (z:ℂ) (x y : ℝ) (hx : x=z.re) (hy : y = z.im) : z = x+I*y :=
  calc
    z = z.re+(z.im)*I := (re_add_im z).symm
    _ = z.re + I*(z.im) := by ring
    _ = x+I*y := by rw [← hx, ← hy]
