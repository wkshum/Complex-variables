import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

open Complex

/-
Exercise 1. Verify that

(a) (√2-i)-i(1-√2i) = -2i

(b) (2,-3)(-2,1)= (-1,8)

(c) (3,1)(3,-1)(1/5,1/10) = (2,1)
-/

theorem Sec2_Ex1a : (Real.sqrt 2 - I) - I*(1- Real.sqrt 2*I) = -2*I := by
  calc
    (Real.sqrt 2 - I) - I*(1- Real.sqrt 2*I)
      = Real.sqrt 2 - 2* I + I*I*Real.sqrt 2 := by ring
    _ = Real.sqrt 2 - 2*I + (-1)*Real.sqrt 2:= by rw [I_mul_I]
    _ = -2 * I := by ring


theorem Sec2_Ex1b : (2-3*I)*(-2+I) = -1+8*I := by
  calc
   (2-3*I)*(-2+I) = -4 +2*I +6*I -3*(I*I) := by ring
   _ = -4 +2*I +6*I - 3*(-1) := by rw [I_mul_I]
   _ = -1+8*I := by ring


theorem Sec2_Ex1c : (3+I)*(3-I)*(1/5+I/10) = 2+I := by
  calc
    (3+I)*(3-I)*(1/5+I/10) = (9-I*I)*(1/5+I/10) := by ring
    _ = (9-(-1))*(1/5+I/10) := by rw [I_mul_I]
    _ = 2+I := by ring



/-

Exercise 2. Show that

(a) Re(iz) = -Im(z)

(b) Im(iz) = Re(z)

-/

theorem Sec2_Ex2a  (z : ℂ) : (I*z).re = -z.im := by
  calc
    (I*z).re = (z*I).re := by ring_nf
    _ = -z.im := mul_I_re z

example  (z : ℂ) : (I*z).re = -z.im := by simp

theorem Sec2_Ex2b  (z : ℂ) : (I*z).im = z.re := by
  calc
    (I*z).im = (z*I).im := by ring_nf
    _ = z.re := mul_I_im z

example  (z : ℂ) : (I*z).im = z.re := by simp




/-

Exercise 3. Show that

-/
