import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

open Complex
open BigOperators


/-
absolute value of complex number is defined as the square root of the norm square
-/

example (z:ℂ) : abs z = Real.sqrt (normSq z) := by rfl

/- Definition 2.3 Principal argument

The principle argument `arg z` is a real number in the range (π,π] that satisfies
cos (arg z) = Re(z)/|z|, and
sin (arg z) = Im(z)/|z|.
-/

example (z:ℂ) (h: z≠ 0):  Real.cos (arg z) = z.re / abs z := by
  exact @cos_arg z h

example (z:ℂ) :  Real.sin (arg z) = z.im / abs z := by
  exact sin_arg z

/-
Definition 2.4 Complex conjugate
The complex conjugate is an endomorphism of ℂ
In LEAN, conj z is computed by `(starRingEnd ℂ) z`
-/

example (x y : ℝ ) :  (starRingEnd ℂ) (Complex.mk x y) = Complex.mk x (-y)  := by
  rfl

/-
Proposition 2.5
(i) conj conj z = z

(ii) z* = z if and only if imag(z) = 0

(iii) |z|^2 = z * conj z

(iv) (z₁+z₂)* = z₁* + z₂* and (z₁z₂)* = z₁* z₂*
-/

example (z : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by
  exact conj_conj z

example (z : ℂ) : (starRingEnd ℂ) z = z ↔ z.im = 0 := by
  exact conj_eq_iff_im



/-
Proposition 2.6

|z₁ z₂| = |z₁| |z₂|
-/



/-
Theorem 2.7 DeMoivre theorem

In the lecture notes the DeMoivre theorem is proved by induction
In LEAN it is a corollar of Euler's formula

-/


theorem DeMoivre (θ : ℝ) (n:ℕ):
 (cos θ +  sin θ * I)^n = (cos (n*θ) +  (sin (n*θ)) * I) := by
  exact cos_add_sin_mul_I_pow n θ


lemma inverse_exp (x:ℝ): 1/(exp (x*I)) = exp (- (x*I)) := by
  have h: exp (x*I) ≠ 0 := by exact exp_ne_zero (x*I)
  field_simp
  symm
  calc
      (-(↑x * I)).exp * (↑x * I).exp
      = (-(↑x * I) + (↑x * I) ).exp := by rw [← exp_add (-(↑ x*I)) (↑ x*I)]
    _ = exp (0) := by rw [← neg_add_self (↑ x*I)]
    _ = 1 := by rw [exp_zero]

theorem DeMoivre_helper  (x:ℝ): 1/(cos (x) + sin (x) *I) = cos (-x) + sin (-x) *I := by
  rw [← exp_mul_I x, inverse_exp, ← exp_mul_I (-x)]
  apply congr_arg exp ?_
  ring

/-
DeMoivre formula for negative exponent
-/

theorem DeMoivre2 (x : ℝ) (n:ℕ):
 1/(cos (x) + sin (x) *I)^n = cos (-n*x) + (sin (-n*x)) * I := by
  have hD : 1/(cos (x) + sin (x) *I)^n = cos (n*(-x)) +  sin (n*(-x)) * I := by
    rw [← one_div_pow (cos (x) + sin (x) *I) n]
    rw [DeMoivre_helper]
    exact cos_add_sin_mul_I_pow n (-x)
  calc
    1/(cos (x) + sin (x) *I)^n = cos (n*(-x)) +  sin (n*(-x)) * I := by rw [hD]
                             _ = cos (-n*x) +  sin (-n*x) * I := by ring_nf

