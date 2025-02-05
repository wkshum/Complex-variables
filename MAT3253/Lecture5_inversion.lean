import Mathlib.Tactic
import Mathlib.Data.Real.Basic

import MyProject.RiemannSphere

open Complex

noncomputable section

/- circles and straight lines are represented by equation
 A(x^2+y^2) + Bx + Cx + D = 0 for some real constants A, B, C, D
 such that A, B, C, and D are not all zero.

 In complex variable, the equation is equivalent to
 Re (a |z|^2 + b*z + c) =0
 for some constant a, b and c, not all zero.
-/



def circleStraightLine (z:ℂ) := ∃ a c : ℝ, ∃ b:ℂ, (a≠0 ∨ b≠0 ∨ c≠0) ∧
  a * (normSq z) + b*z + ((starRingEnd ℂ) z) * ((starRingEnd ℂ) b) + c= 0

/- Theorem 5.1
  The inversion function f(z) = 1/z maps circle and straight line
  to circle to straight line-/

example (z w : ℂ) (hf: f=fun z => 1/z) (hz : circleStraightLine z) :
    circleStraightLine (f z) := by sorry



/- Proposition 5.7 Stereographic projection -/

-- Stereographic projection maps the complex plane to the sphere
-- with equation a^2+b^2+(c-r)^2=r^2

example (x y r a b c:ℝ)  (hrpos: r>0)
 (ha : a = 4*r^2*x/(4*r^2+x^2+y^2))
 (hb : b = 4*r^2*y/(4*r^2+x^2+y^2))
 (hc : c = 2*r*(x^2+y^2)/(4*r^2+x^2+y^2))
 : a^2+b^2+(c-r)^2 = r^2
 := by sorry
