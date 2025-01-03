
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Exponential


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
Theorem 2.7 DeMoivre formula

In the lecture notes the DeMoivre formula is proved by induction
In LEAN it is a corollary of Euler's formula

-/

theorem DeMoivre (θ : ℝ) (n:ℕ):
 (cos θ +  sin θ * I)^n = (cos (n*θ) +  (sin (n*θ)) * I) := by
  exact cos_add_sin_mul_I_pow n θ


/-
the inverse of e^(x*I) is equal to exp(-x*I)
-/
lemma one_dvd_mul_I (x:ℝ): 1/(exp (x*I)) = exp (- (x*I)) := by
  have h: exp (x*I) ≠ 0 := by exact exp_ne_zero (x*I)
  field_simp
  symm
  calc
      (-(↑x * I)).exp * (↑x * I).exp
      = (-(↑x * I) + (↑x * I) ).exp := by rw [← exp_add (-(↑ x*I)) (↑ x*I)]
    _ = exp (0) := by rw [← neg_add_self (↑ x*I)]
    _ = 1 := by rw [exp_zero]

theorem DeMoivre_helper  (x:ℝ): 1/(cos (x) + sin (x) *I) = cos (-x) + sin (-x) *I := by
  rw [← exp_mul_I x]
  rw [one_dvd_mul_I]
  rw [← exp_mul_I (-x)]
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


/-
  Example 2.3. A long calculation of (-1+I)^20 = -1024
-/

-- cos(3pi/4) = -√2/2
theorem cos_3_pi_div_4 : √2* Real.cos (3*Real.pi/4) = -1 :=
  have h : 0≤ (2:ℝ) := by linarith
  calc
      √2* Real.cos (3*Real.pi/4)
    = √2* (Real.cos (Real.pi-Real.pi/4)) := by
        refine congr_arg (fun x => √2*Real.cos x) ?_
        ring
  _ = √2* (-Real.cos (Real.pi/4)) := by rw [Real.cos_pi_sub (Real.pi/4)]
  _ = √2* -(√2/2) := by rw [Real.cos_pi_div_four]
  _ = - ((Real.sqrt 2)^2)/2 := by ring
  _ = - (2) /2 := by rw [Real.sq_sqrt h]
  _ = -1 := by norm_num


-- sin(3pi/4) = √2/2
theorem sin_3_pi_div_4 : √2*Real.sin (3*Real.pi/4) = 1 :=
  have h : 0≤ (2:ℝ) := by linarith
  calc
      √2*Real.sin (3*Real.pi/4)
    = √2*Real.sin (Real.pi-Real.pi/4) := by
        refine congr_arg (fun x=> √2*Real.sin x) ?_
        ring
  _ = √2*Real.sin (Real.pi/4) := by rw [Real.sin_pi_sub (Real.pi/4)]
  _ = √2*(√2/2) := by rw [Real.sin_pi_div_four]
  _ = ((Real.sqrt 2)^2)/2 := by ring
  _ = (2) /2 := by rw [Real.sq_sqrt h]
  _ = 1 := by norm_num

example :  √2 * Complex.cos (3*Real.pi/4) = -1:= by
  calc
    √2 * Complex.cos (3*Real.pi/4) = ↑ (√2 * Real.cos (3*Real.pi/4)) := by norm_num
                                  _= ↑ (-1:ℝ ) := by rw [cos_3_pi_div_4]
                                  _= -1 := by norm_num


example :  √2 * Complex.sin (3*Real.pi/4) = 1:= by
  calc
    √2 * Complex.sin (3*Real.pi/4) = ↑ (√2 * Real.sin (3*Real.pi/4)) := by norm_num
                                  _= ↑ (1:ℝ ) := by rw [sin_3_pi_div_4]
                                  _= 1 := by norm_num



example : (-1+I)^20 = -1024 := by
  have h1 : √2 * cos (3*Real.pi/4) = -1 := by
    calc
    √2 * Complex.cos (3*Real.pi/4) = ↑ (√2 * Real.cos (3*Real.pi/4)) := by norm_num
                                  _= ↑ (-1:ℝ ) := by rw [cos_3_pi_div_4]
                                  _= -1  := by norm_num
  have h2 : √2 * sin (3*Real.pi/4) = 1:= by
    calc
    √2 * Complex.sin (3*Real.pi/4) = ↑ (√2 * Real.sin (3*Real.pi/4)) := by norm_num
                                  _= ↑ (1:ℝ ) := by rw [sin_3_pi_div_4]
                                  _= 1 := by norm_num
  have h3 : -1+I = ↑ (√2) * (cos (3*Real.pi/4) + sin (3*Real.pi/4) *I) :=
    calc
      -1+I = Real.sqrt 2 * cos (3*Real.pi/4) +I := by rw [← h1]
        _ = Real.sqrt 2 * cos (3*Real.pi/4) + I*(1) := by ring
        _ = Real.sqrt 2 * cos (3*Real.pi/4) + I*(Real.sqrt 2 * sin (3*Real.pi/4)) := by  rw [← h2]
        _ = (Real.sqrt 2) * (cos (3*Real.pi/4) + sin (3*Real.pi/4)*I ) := by ring

  -- magnitude
  have h4 :  (1024:ℂ)  = ↑ (Real.sqrt 2)^20 := by
    have h : (Real.sqrt 2)^2 = 2 := by
      refine Real.sq_sqrt ?_
      linarith
    calc
      (1024:ℂ) = ↑ (1024 : ℝ)  := by rfl
              _= ↑ (2^10 : ℝ)  := by ring_nf
              _= ↑ (((Real.sqrt 2)^2)^10 : ℝ) := by rw [h]
              _= ↑ ((Real.sqrt 2)^20 :ℝ) := by ring_nf
              _= (↑ (Real.sqrt 2))^20 := ofReal_pow (√2) 20

  -- argument
  have h5 : ((cos (3*Real.pi/4) + sin (3*Real.pi/4) *I))^20 = -1 := by
    rw [← exp_mul_I (3*Real.pi/4)]
    rw [← exp_nat_mul (3*Real.pi/4*I) 20]
    have h : (↑20 * (3 * ↑Real.pi / 4 * I)).exp = exp (15*Real.pi*I) := by
      apply congr_arg exp ?_
      field_simp
      ring
    calc
      (↑20 * (3 * ↑Real.pi / 4 * I)).exp
      = exp (15*Real.pi*I) := by rw [h]
    _ = exp ((7:ℕ) *2*Real.pi*I+ Real.pi*I) := by
        apply congr_arg exp ?_
        ring
    _ = exp ((7:ℕ)*2*Real.pi*I) * exp (Real.pi*I) := by rw [exp_add ((7:ℕ)*2*Real.pi*I) (Real.pi*I)]
    _ = exp ((7:ℕ)*2*Real.pi*I) * (-1) := by rw [exp_pi_mul_I]
    _ = -(exp ((7:ℕ)*(2*Real.pi*I))) := by ring_nf
    _ = -(exp (2*Real.pi*I)^7) := by rw [exp_nat_mul (2*Real.pi*I) 7]
    _ = -(1)^7 := by rw [exp_two_pi_mul_I]
    _ = -1 := by ring

  calc
    (-1+I)^20 = (↑√2 * (cos (3*Real.pi/4) + sin (3*Real.pi/4) *I))^20 := by rw [h3]
            _ = (↑√2)^20 * (cos (3*Real.pi/4) + sin (3*Real.pi/4) *I)^20
                   :=  mul_pow (↑√2) (cos (3*Real.pi/4) + sin (3*Real.pi/4) *I) 20
            _ = 1024 * (cos (3*Real.pi/4) + sin (3*Real.pi/4) *I)^20  := by rw [h4]
            _ = 1024 * (-1) := by rw [h5]
            _ = -1024 := by ring
