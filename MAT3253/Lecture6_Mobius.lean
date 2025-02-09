/-
Copyright (c) 2025 Kenneth Shum All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Shum
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic

import MyProject.ComplexVariables.MAT3253.EComplex

noncomputable section

open Complex EComplex


section MobiusTransformation


/- a function f(z) is defined as a translation if f(z) = z+b
   for some constant b -/
def isTranslation (f : EComplex → EComplex) := ∃ b:ℂ , ∀ z:EComplex, f z = z+b

/- a function f(z) is defined as an affine function if f(z) = az+b
 for some constants a and b, with a ≠ 0.
-/
def isAffine (f : EComplex → EComplex) :=
   ∃ (a b:ℂ) , a≠ 0 ∧ ∀ z:EComplex, f z = a*z+b

/-
Linear fractional transformation f(z) = (az+b)/(cz+d)
  where ad-bc≠ 0
-/
def isLinearFractionalTransformation (f : EComplex → EComplex) :=
    ∃ (a b c d:ℂ) , (a*d-b*c ≠ 0) ∧ ∀ z:EComplex, f z = (a*z+b)/(c*z+d)



example (hf : isTranslation f) (hg : isTranslation g) :
  isTranslation (f ∘ g) := by sorry

example (hf : isAffine f) (hg : isAffine g) :
  isAffine (f ∘ g) := by sorry

example (hf : isLinearFractionalTransformation f)
 (hg : isLinearFractionalTransformation g) :
  isLinearFractionalTransformation (f ∘ g) := by sorry



/-
 Cross ratio
-/


def cross_ratio (z₀ z₁ z₂ z₃ : EComplex) :=
  (z₀ - z₁)*(z₂ - z₃)/((z₀ - z₃)*(z₂ - z₁))

theorem cross_ratio_invariant (z₀ z₁ z₂ z₃ w₀ w₁ w₂ w₃: EComplex)
 (f : EComplex → EComplex)
 (hf : isLinearFractionalTransformation f)
 (h0 : w₀ = f z₀) (h1 : w₁ = f z₁) (h2 : w₂ = f z₂) (h3 : w₃ = f z₃) :
 cross_ratio z₀ z₁ z₂ z₃ = cross_ratio w₀ w₁ w₂ w₃ := by sorry
