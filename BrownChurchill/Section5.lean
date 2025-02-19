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

section BrownChurchil_Section5

/-
Question 2
Verify Re z ≤ |Re z| ≤ |z| and Im z ≤ |Im z| ≤ |z|
-/

-- Mathlib already has Re z ≤ |z| and Im z ≤ |z|
example (z:ℂ) : z.re ≤ abs z:= by exact re_le_abs z
example (z:ℂ) : z.im ≤ abs z:= by exact im_le_abs z


-- first show that it is true with z.re replaced by any real number a
lemma helper_for_question2 (a:ℝ) : a ≤ Complex.abs a := by
  unfold Complex.abs
  simp
  refine Real.le_sqrt_of_sq_le ?_
  -- the question is reduced to showing a^2 ≤ a*a
  show a^2 ≤ a*a
  calc
    a^2 = a*a := by ring
      _ ≤  a*a := Preorder.le_refl (a * a)


example (z:ℂ) : z.re ≤ Complex.abs (z.re):= by
  exact helper_for_question2 z.re

example (z:ℂ) : z.im ≤ Complex.abs (z.im):= by
  exact helper_for_question2 z.im


example (z:ℂ) : Complex.abs (z.re) ≤ Complex.abs z := by
  unfold Complex.abs
  simp
  gcongr
  -- The question is reduced to showing
  show z.re * z.re ≤ normSq z
  calc
    z.re * z.re = z.re*z.re + 0 := by ring
              _ ≤ z.re*z.re + z.im*z.im := by rel [mul_self_nonneg z.im]
              _ = normSq z := by rfl

example (z:ℂ) : Complex.abs (z.im) ≤ Complex.abs z := by
  unfold Complex.abs
  simp
  gcongr
  -- The question is reduced to showing
  show z.im * z.im ≤ normSq z
  calc
    z.im * z.im = 0 + z.im*z.im  := by ring
              _ ≤ z.re*z.re + z.im*z.im  := by rel [mul_self_nonneg z.re]
              _ = normSq z := by rfl




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

end BrownChurchil_Section5
