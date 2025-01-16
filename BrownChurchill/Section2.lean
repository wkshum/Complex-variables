/-
**Exercises from Brown and Churchill
  Section 2, Basic algebraic properties**

Copyright (c) 2025 Kenneth Shum. All rights reserved.
Released under Apache 2.0 license.
Authors: Kenneth Shum
-/


import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Complex

section BrownChurchill2

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
Exercrse 7. Use the associative law for addition and the
distributive law to show that  z(z₁ + z₂ + z₃) = z z₁ + z z₂ + z z₃
-/

theorem Sec2_Ex7 (z z₁ z₂ z₃ : ℂ) : z*(z₁ + z₂ + z₃) = z*z₁ + z*z₂ + z*z₃ := by ring


/-
Exercise 8. Prove uniqueness of additive inverse and uniqueness
        of multiplicative identity
-/

theorem Sec2_Ex8a (z w₁ w₂ : ℂ) (h₁ : z+w₁ = 0) (h₂ : z+ w₂ = 0) : w₁ = w₂ := by
  linear_combination h₁ - h₂

theorem Sec2_Ex8b (w : ℂ):  (∀ z, z*w = z) ↔  w = 1 := by
  constructor
  · -- forward
    intro h  -- assume z*w = z for all z
    have h₁ : 1*w = 1 := by apply h
    calc
      w = 1*w  :=  by ring
      _ = 1 :=  h₁
  · -- backward
    intro h  -- assume w=1
    intro z  -- let z be any complex number
    calc
      z*w = z*1 := by rw [h]
      _ = z := by ring


/-
Exercrse 9. Use −1 = (−1, 0) and z = (x, y) to show that (−1)z = −z
-/

theorem Sec2_Ex9 (z : ℂ) : (-1)*z = -z := by ring

/-
Exercise 10. Thus show that the additive inverse of a complex number z = x+iy
 can be written−z = −x−iy
-/

theorem Sec2_Ex10 {z : ℂ} {x y : ℝ} (hx : x = z.re) (hy : y = z.im) : -z = -x-I*y := by
  calc
    -z = (-1)*z := by ring
     _ = (-1)*(z.re+(z.im)*I) := by rw [re_add_im z]
     _ = (-1)*(x+y*I) := by rw [← hx, ← hy]
     _ = -x -I*y := by ring

/-
Exercise 11.  Solve the equation z^2 + z + 1 = 0 for z = (x, y) by writing
(x, y)(x, y) + (x, y) + (1, 0) = (0, 0)
and then solving a pair of simultaneous equations in x and y.

First show that x^2-y^2+x+1=0 and 2*x*y+y = 0
From the first equation we see that y is not zero.
Then, the value of x is determined from one of the equations
After x is known, then y^2 is determined from the other equation.

The answer is x=-1/2, and y = ± √3/2
-/

theorem Sec2_Ex11 {z: ℂ} {x y : ℝ} (hx : x = z.re) (hy : y = z.im)
 (hz : z^2+z+1=0) :  x=-1/2 ∧ y^2=3/4 := by
  let w : ℂ := z^2+z+1
  let u : ℂ := ⟨ x^2-y^2+x+1, 2*x*y+y ⟩
  -- u is the complex number with real part x^2-y^2+x+1 and imag part 2xy+y                                       -- x^2
  have h₁ : w = 0 := by   -- we have  w=0 from hypothesis
    calc
       w = (z^2+z+1) := by dsimp  -- substitute w by definition
       _ = (0) := by rw [hz]      -- z^2+z+1 = 0 by hypothesis
  have h₂ : u.re = (x^2-y^2+x+1) := by rfl
  have h₃ : u.im = (2*x*y+y)     := by rfl
  have h₄ : w = u := by   -- show that w is equal to u
    calc
      w = z^2+z+1 := by dsimp     -- substitute w by definition
      _ = (z.re+z.im*I)^2 + (z.re+z.im*I) + 1 := by rw [re_add_im z] -- z = z.re+z.im*I
      _ = (x+y*I)^2 + (x+y*I) + 1 := by rw [hx , hy]  -- replace z.re = x, z.im = y
      _ = x^2 + 2*x*y*I + y^2*(I*I) + x+y*I + 1 := by ring  -- expand
      _ = x^2 + 2*x*y*I + y^2*(-1) + x+y*I + 1 := by rw [I_mul_I]  -- I*I=-1
      _ = (x^2-y^2+x+1) + (2*x*y+y)*I := by ring  -- simplify
      _ = ↑((x^2-y^2+x+1):ℝ ) + ↑((2*x*y+y):ℝ )*I := by norm_cast
      _ = u.re + u.im*I := by rw [h₂ , h₃]
      _ = u := re_add_im u
  have h_real : x^2-y^2+x+1 = 0 := by    -- real part of u is 0
    calc
    x^2-y^2+x+1 = u.re := by rw [h₂]
      _ = w.re := (Complex.ext_iff.mp h₄).1.symm
      _ = (0:ℂ ).re := by rw [← h₁]
      _ = 0 := rfl
  have h_imag : (2*x+1)*y = 0 := by         -- imag part of u is 0
    calc
      (2*x+1)*y = 2*x*y+y := by ring
      _ = u.im := by rw [h₃]
      _ = w.im :=  (Complex.ext_iff.mp h₄).2.symm
      _ = (0:ℂ).im := by rw [← h₁]
      _ = 0 := rfl
  have h₅ : x=-1/2 := by       -- derive x = -1/2 from (2x+1)*y=0 and y≠0
    have h : y^2 > 0 := by    -- show that y^2 is positive
      calc
        y^2 = y^2 + 0 := by ring
          _ = y^2 + (x^2-y^2+x+1) := by rw [h_real]
          _ = (x+1/2)^2 + 3/4 := by ring
          _ > 0 := by positivity
    have y_ne_zero : y≠ 0 := by apply (sq_pos_iff).mp h  -- y is nonzero
    calc
        x = -1/2 + (1/2)*(2*x+1) := by ring
        _ = -1/2 + (1/2)*0 := by rw [eq_zero_of_ne_zero_of_mul_right_eq_zero y_ne_zero h_imag]
        _ = -1/2 := by ring

  constructor
  · exact h₅   -- x = -1/2
  · -- derive y^2=3/4 by calculations
    calc
      y^2 = 3/4 +y^2 - (-1/2)^2 - (- 1/2) - 1 := by ring
        _ = 3/4 +y^2 - (x)^2 - (x) - 1 := by rw [← h₅]
        _ = 3/4 - (x^2-y^2+x+1) := by ring
        _ = 3/4 - 0 := by rw [h_real]
        _ = 3/4 := by ring

end BrownChurchill2
