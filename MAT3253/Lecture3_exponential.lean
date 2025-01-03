
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential


open Complex
open BigOperators



/-
Proposition 3.1 Triangular inequality |z₁+z₂| ≤ |z₁| + |z₂|
-/

theorem complex_triangle_inequality (z₁ z₂ : ℂ) : abs (z₁+z₂) ≤ abs z₁ + abs z₂ := by
  exact AbsoluteValue.add_le Complex.abs z₁ z₂


/-
Definition 3.16

Complex exponential function is defined as the limit of a power series
-/
-- #print exp     --def Complex.exp : ℂ → ℂ := fun z ↦ z.exp'.lim


/-
Theorem 3.17
Additive property of exponential function exp (x+y) = exp x * exp y

This is proved by using Cauchy product

-/

example (z₁  z₂  : ℂ)  : exp (z₁+z₂) = exp z₁ * exp z₂ := by
  exact exp_add z₁ z₂



/-
Corollary 3.18

Exponential function is nonzero for all inputs
-/

example (z:ℂ) : exp (-z) = (exp z)⁻¹ := by
  exact exp_neg z

example (z : ℂ) : exp z ≠ 0 := by
  exact exp_ne_zero z


/-
Theorem 3.19
-/

example (z : ℂ) : abs (exp z) = exp (z.re) := by sorry

example (y : ℝ) : abs (exp y*I) = 1 := by sorry



/-
Theorem 3.20

Euler's formula
-/

theorem Euler_formula (θ : ℝ) : exp (θ*I) = cos θ +  sin θ * I := by
  exact exp_mul_I (θ:ℂ)

theorem Euler_formula' (θ : ℝ) : exp (θ*I) = cos θ +  I* ( sin θ)  := by
  calc
    exp (θ*I) = cos θ +  (sin θ) * I := by exact Euler_formula θ
            _ = cos θ +  I* (sin θ)  := by ring


/-
The most famous formula:   exp(pi*i) + 1 = 0
-/

example : Complex.exp (Real.pi*I) + 1 = 0 := by
  rw [exp_mul_I Real.pi]
  rw [Complex.cos_pi, Complex.sin_pi]
  ring
