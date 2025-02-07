
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential


open Complex
open BigOperators
open Finset


/-
Proposition 3.1 Triangular inequality |z₁+z₂| ≤ |z₁| + |z₂|
-/

theorem complex_triangle_inequality (z₁ z₂ : ℂ) : abs (z₁+z₂) ≤ abs z₁ + abs z₂ := by
  exact AbsoluteValue.add_le Complex.abs z₁ z₂


/-
Definition 3.2 Open disc
-/

def open_disc (z₀ : ℂ) (r:ℝ) : Set ℂ := {z: ℂ | abs (z - z₀) < r }


/-
Definition 3.3 Convergence of complex sequence

The epsilon-delta definition of the meaning that
 a complex sequence s_n converging to z₀.
-/

def isConvergentTo (s : ℕ → ℂ) (z₀ :ℂ) :=
  ∃ ε > 0, ∃ N : ℕ, ∀ n≥ N, abs (s n - z₀) < ε

def isConvergent (s:ℕ → ℂ) := ∃ z₀ : ℂ , isConvergentTo s z₀



/-
Definition 3.4 Cauchy sequence

The meaning of Cauchy sequence is defined in
Mathlib.Algebra.Order.CauSeq.Basic

-/

example : IsCauSeq Complex.abs (f : ℕ → ℂ) =  ∀ ε > 0, ∃ i, ∀ j ≥ i, abs (f j - f i) < ε
  := rfl


/-
Proposition 3.5

-/


/-
Definition 3.18

Complex exponential function is defined as the limit of a power series
-/

/-
  In Mathlib, exp' z is defined as a pair,
  consists of a power series and a proof that it is a Cauchy sequence
  The first part `fun n => ∑ m ∈ range n, z ^ m / m.factorial` is a formal power series
  The second part `isCauSeq_exp z` is a proof that this series converges at `z`
-/
example : exp' (z:ℂ) =  ⟨fun n => ∑ m ∈ range n, z ^ m / m.factorial, isCauSeq_exp z⟩ := rfl

-- For any complex number z, exp z is defined as the limit of the Cauchy sequence exp'
example : exp (z:ℂ) = CauSeq.lim (exp' z) := by rfl


/-
Theorem 3.19
Additive property of exponential function exp (x+y) = exp x * exp y

-/

example (z₁  z₂  : ℂ)  : exp (z₁+z₂) = exp z₁ * exp z₂ := by
  exact exp_add z₁ z₂



/-
Corollary 3.20

Exponential function is nonzero for all inputs
-/

example (z:ℂ) : exp (-z) = (exp z)⁻¹ := by
  exact exp_neg z

example (z : ℂ) : exp z ≠ 0 := by
  exact exp_ne_zero z




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
