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
Exercise 3. Show that (1+z^2) = 1+2*z+z^2
-/

theorem Sec2_Ex3 (z:ℂ) : (1+z)^2 = 1+2*z+z^2 := by ring

/-
Exercise 4. Verify that each of the two numbers z = 1 ± i
satisfies the equation z^2 − 2*z + 2 = 0.
-/

theorem Sec2_Ex4 (z:ℂ) : z=1+I ∨ z=1-I → z^2-2*z+2=0 := by
  intro h
  obtain h₁ | h₂ := h
  · -- suppose z = 1+I
    calc
      z^2 - 2*z + 2 = (1+I)^2 - 2*(1+I) + 2 := by rw [h₁]
       _ = 1+I*I := by ring
       _ = 1 + (-1) := by rw [I_mul_I]
       _ = 0 := by ring
  · -- suppose z = 1-I
    calc
      z^2 - 2*z + 2 = (1-I)^2 - 2*(1-I) + 2 := by rw [h₂]
       _ = 1+I*I := by ring
       _ = 1 + (-1) := by rw [I_mul_I]
       _ = 0 := by ring

/-
Exercise 5. Prove that multiplication of complex numbers is commutative
-/
theorem Sec2_Ex5 (z w : ℂ) : z*w = w*z := mul_comm z w

/-
Exercrse 6. Verify the associative law and distributive law
-/

theorem Sec2_Ex6a (a b c : ℂ): (a*b)*c = a*(b*c) := mul_assoc a b c

theorem Sec2_Ex6b (a b c : ℂ): a*(b+c) = a*b+a*c := mul_add a b c

/-
Exercrse 7. Use the associative law for addition and the distributive law to show that
  z(z₁ + z₂ + z₃) = z z₁ + z z₂ + z z₃
-/

theorem Sec2_Ex7 (z z₁ z₂ z₃ : ℂ) : z*(z₁ + z₂ + z₃) = z*z₁ + z*z₂ + z*z₃ := by ring
