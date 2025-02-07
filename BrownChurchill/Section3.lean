/-
Copyright (c) 2025 Kenneth Shum. All rights reserved.
Released under Apache 2.0 license.
Authors: Kenneth Shum
-/

/-
  Exercises from Brown and Churchill
  "Complex variables and applications, 9th edition"
  Section 3, Further algebraic properties
-/


import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

open Complex

/-
Question 1a
-/

example : (1+2*I)/(3-4*I) + (2-I)/(5*I) = -2/5 := by
-- We first simplify the first fraction to (1+2*I)*(3+4*I)/25
  have h_f1: (1+2*I)/(3-4*I) = (1+2*I)*(3+4*I)/25 := by

    --  Show that 3-4*I is not equal to 0
    have h_ne : (3-4*I) ≠ 0 := by
      intro h
      have h2 : (3:ℝ) = 0 :=
        calc
          3 = (3-4*I).re := by simp
          _ = (0:ℂ).re := by rw [congr_arg (fun a ↦ a.re) h]
          _ = 0 := by rfl
      have h3 : (3:ℝ) ≠ 0 := Ne.symm (NeZero.ne' 3)
      contradiction

    rw [div_eq_mul_inv]
    symm
    rw [eq_mul_inv_iff_mul_eq₀ h_ne]
    rw [mul_div_right_comm]
    calc
      (1 + 2 * I) /25 * (3 + 4 * I) * (3 - 4 * I)
      = (1+2*I)/25*(9-16*(I*I)) := by ring
    _ = (1+2*I)/25*(9 - 16*(-1)) := by rw [I_mul_I]
    _ = (1+2*I) := by ring

  -- Next show that the second fraction equal (-1-2*I)/5
  have h_f2 : (2-I)/(5*I) = (-1-2*I)/5 := by
    rw [← div_div]
    rw [div_eq_mul_inv]
    symm
    rw [eq_mul_inv_iff_mul_eq₀ I_ne_zero]
    rw [← mul_div_right_comm]
    calc
      (-1-2*I) * I / 5 = (-I - 2*(I*I))/5 := by ring
                        _ = (-I - 2*(-1) )/5 := by rw [I_mul_I]
                        _ = (2-I)/5 := by ring

  -- simplify the two fractions
  rw [h_f1, h_f2]

  -- Show tha the sum is -2/5
  field_simp  -- clear the denomiantors
  calc
    ((1 + 2 * I) * (3 + 4 * I) * 5 + (-1 - 2 * I) * 25) * 5
    = ((3+10*I+8*(I*I)) * 5 + (-1 - 2 * I) * 25) * 5 := by ring
  _ =((3+10*I+8*(-1)) * 5 + (-1 - 2 * I) * 25) * 5 := by rw [I_mul_I]
  _ = -(2 * (25 * 5)) := by ring


/-
Question 1b
-/

example : (5*I)/((1-I)*(2-I)*(3-I)) = -1/2 := by
  have h1 : 1-I ≠ 0 :=
    sub_ne_zero.mpr ((congr_arg im).mt zero_ne_one)
  have h2 : 2-I ≠ 0 :=
    sub_ne_zero.mpr ((congr_arg im).mt zero_ne_one)
  have h3 : 3-I ≠ 0 :=
    sub_ne_zero.mpr ((congr_arg im).mt zero_ne_one)
  field_simp
  symm
  calc
      -((1 - I) * (2 - I) * (3 - I))
    = -(6 - 11*I + 6*(I*I) - (I*I)*I) := by ring
  _ = -(6 - 11*I + 6*(-1) - (-1)*I) := by rw [I_mul_I]
  _ = 5*I*2 := by ring

/-
Question 1c
-/

example : (1-I)^4 = -4 := by
  calc
    (1-I)^4 = 1 - 4*I + 6*(I*I) - 4*(I*I)*I + (I*I)*(I*I):= by ring
          _ = 1 - 4*I + 6*(-1) - 4*(-1)*I + (-1)*(-1) := by rw [I_mul_I]
          _ = -4 := by ring




/-
Question 2. Show that 1/ (1/z) = z  for z≠ 0
-/

example (z : Complex) : 1/(1/z) = z := by exact one_div_one_div z


/-
Question 3. Use associative law and communtative law to show
  (z₁z₂)(z₃z₄) = (z₁z₃) (z₂z₄)
-/

-- The associative law is implemented by mul_mul_mul_comm in Mathlib

example (z₁ z₂ z₃ z₄ : Complex) : (z₁*z₂)*(z₃*z₄) = (z₁*z₃) * (z₂*z₄) :=
 by exact mul_mul_mul_comm z₁ z₂ z₃ z₄

/-
Question 4. Prove that if z₁ z₂ z₃  = 0, then at least one of the three factors is zero.
-/

example (z₁ z₂ z₃ : ℂ) (h : z₁ * z₂ * z₃ =0)
     : z₁=0 ∨ z₂ =0 ∨ z₃=0 := by sorry


/-
Question 5
-/

example (x₁ x₂ y₁ y₂  : ℝ) :
  let z₁ := x₁+y₁*I
  let z₂ := x₂+y₂*I
  z₂ ≠ 0 → z₁/z₂ = (x₁*x₂ +y₁*y₂)/(x₂^2+y₂^2) + (y₁*x₂ - x₁*y₂)/(x₂^2+y₂^2)*I
    := by sorry

/-
Question 6
-/

example (z₁ z₂ z₃ z₄ : ℂ) (h3: z₃ ≠ 0) (h4: z₄≠ 0) :
(z₁/z₃)*(z₂/z₄) =(z₁*z₂)/(z₃*z₄) := by sorry


/-
Question 7
-/

example (z₁ z₂ z : ℂ) (h2: z₂ ≠ 0) (h: z ≠ 0) :
  (z₁*z)/(z₂*z) = z₁/z₂ := by sorry

/-
Question 8, binomial theorem
-/

open Finset
open BigOperators
open Nat

def S (n:ℕ) := ∑ x in (range (n)), 2^x

example (z₁ z₂:ℂ) (n:ℕ) :
 (z₁+z₂)^n = ∑ k in range (n+1), (n.choose k)*z₁^(n-k)*z₂^k
:= by sorry
