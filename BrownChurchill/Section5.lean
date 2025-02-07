/-
Copyright (c) 2025 Kenneth Shum All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Shum
-/

/-
  Exercises from Brown and Churchill
  "Complex variables and applications, 9th edition"
  Section 5, Triangle inequality
-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic


open Complex BigOperators


/-
|z| is defined in LEAN as the square root of the `normSq`
 The function `normSq` is defined by x^2+y^2 when z=x+iy
-/

example (z:ℂ) : abs z = Real.sqrt (normSq z) := by rfl

example (z:ℂ) : normSq z = z.re*z.re+z.im*z.im := by rfl


/-
Question 2
Verify Re z ≤ |Re z| ≤ |z| and Im z ≤ |Im z| ≤ |z|
-/


example (z:ℂ) : z.re ≤ abs z:= by exact re_le_abs z

example (a:ℝ ) : a ≤ Complex.abs (a):= by sorry

example (z:ℂ) : Complex.abs (z.re) ≤ abs z := by sorry


/-
Question 3
-/

example (z₁ z₂ z₃ z₄ : ℂ) :
 (z₁+z₂).re /(abs (z₃+z₄)) ≤ (abs z₁ + abs z₂) / (Complex.abs (abs z₃ - abs z₄)) :=
 by sorry


/- Question 4
Verify that √2 |z| ≥ |Re z| + |Im z|
-/

example (z:ℂ) : Real.sqrt 2 * abs z ≥ Complex.abs z.re + Complex.abs z.im := by sorry


/-
Quesion 7 Show that for R sufficiently large, the polynomial P(z) in Example 3, Sec. 5, satisfies
the inequality |P(z)| ≤ 2 |a_n| |z^n| whenever |z| ≥ R
-/

example {n:ℕ} (a : Fin (n+1) → ℂ) : ∃ R:ℝ, ∀ z:ℂ,  abs z ≥ R →
 Complex.abs (∑  k: Fin (n+1), (a k)*(z)^(k:ℕ)) ≤  2 * (Complex.abs (a n)) * (abs z)^n
 := by sorry
