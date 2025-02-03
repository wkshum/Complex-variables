/-

Construct the extended complex number system by
adjoining a point at infinity to the complex number

Define linear fractional transformation

-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

open Complex

noncomputable section

/- Define extended complex number by adding a point to ℂ -/
def EComplex := Option ℂ



deriving instance Nontrivial, Inhabited
  for EComplex

notation "ℂ∞" => EComplex

notation "∞" => (none: EComplex)

namespace EComplex

/- The extra point is printed as ∞ -/
unsafe instance instRepr [Repr ℂ] : Repr (EComplex) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => repr a⟩

@[coe, match_pattern] def some : ℂ  → EComplex :=
  Option.some


-- def a0 : EComplex  := ∞
-- def a1 : EComplex := (5: Real)

-- #eval a0
-- #eval a1

-- instance : AddCommMonoidWithOne EComplex :=
--   inferInstanceAs (AddCommMonoidWithOne (Option ℂ))

-- instance : CharZero EComplex :=
--   inferInstanceAs (CharZero (Option ℂ))

/-- The canonical inclusion from complex to EComplex. -/
@[coe, match_pattern] def Complex.toEComplex : ℂ  → EComplex := some



/- Coecision from type ℂ to type EComplex-/
instance coe : Coe ℂ  EComplex :=
  ⟨some⟩

instance : Inhabited EComplex := ⟨ (0:ℂ) ⟩

@[simp]
theorem coe_zero : ((0 : ℂ) : EComplex) = (0:ℂ) := rfl

@[simp]
theorem coe_one : ((1 : ℂ) : EComplex) = (1:ℂ) := rfl


instance decidableEq : DecidableRel ((· = ·) : EComplex → EComplex → Prop) :=
  Option.instDecidableEq


-- @[simp]
-- protected theorem coe_eq_coe_iff {x y : ℂ}
--   : (x : EComplex) = (y : EComplex) ↔ x = y := sorry
--   --coe_injective.eq_iff

/-- The map from extended complex to complex sending infinity to zero. -/
def toComplex : EComplex → ℂ
  | ∞ => 0
  | (x : ℂ ) => x

@[simp]
theorem toComplex_Inf : toComplex ∞ = 0 :=
  rfl




/- Extend logical quantifiers to EComplex -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def rec {C : EComplex → Sort*} (h_inf : C ∞) (h_complex : ∀ a : ℂ, C a) :
    ∀ a : EComplex, C a
  | ∞ => h_inf
  | (a : ℂ) => h_complex a

protected lemma «forall» {p : EComplex → Prop} : (∀ z, p z) ↔ p ∞ ∧ ∀ z : ℂ , p z where
  mp h := ⟨h _, fun _ ↦ h _⟩
  mpr h := EComplex.rec h.1 h.2

protected lemma «exists» {p : EComplex → Prop} : (∃ r, p r) ↔ p ∞ ∨ ∃ z : ℂ , p z where
  mp := by rintro ⟨r, hr⟩; cases r <;> aesop
  mpr := by rintro (h | h | ⟨r, hr⟩) <;> exact ⟨_, ‹_›⟩

/-- Addition on `EComplex`. -/
-- We adopt the convention that  ∞+∞ = ∞
-- in oder to make addition defined for all inputs
@[simp]
protected def add : EComplex → EComplex → EComplex
  | ∞, ∞ => ∞
  | (z : ℂ), ∞ => ∞
  | ∞, (z : ℂ) => ∞
  | (z : ℂ), (w : ℂ) => (z + w : ℂ)


/-- The multiplication on `EComplex`. -/
-- In practice, 0⬝∞ should be undefined.
-- We adopt the convention 0⬝∞ = ∞⬝0 = ∞ to make multiplication
-- well defined for all inputs.
@[simp]
protected def mul : EComplex → EComplex → EComplex
  | ∞, ∞ => ∞
  | (z : ℂ), ∞ => ∞
  | ∞, (z : ℂ) => ∞
  | (z : ℂ), (w : ℂ) => (z * w : ℂ)


instance : Mul EComplex := ⟨EComplex.mul⟩

instance : Add EComplex := ⟨EComplex.add⟩


@[simp, norm_cast]
theorem coe_mul (x y : ℂ) : (↑(x * y) : EComplex) = x * y :=
  rfl

@[simp, norm_cast]
theorem coe_add (x y : ℂ) : (↑(x + y) : EComplex) = x + y :=
  rfl


/-  Multiplication on EComplex is commutative-/
@[simp]
protected theorem mul_comm (x y : EComplex) : x * y = y * x := by
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_mul, ← coe_mul, mul_comm]

/-  Addition on EComplex is commutative-/
@[simp]
protected theorem add_comm (x y : EComplex) : x + y = y + x := by
  induction x <;> induction y  <;>
    try { rfl }
  rw [← coe_add, ← coe_add, add_comm]

/- Infinity times infinity equals infinity-/
@[simp]
theorem inf_mul_inf : EComplex.mul ∞ ∞ = ∞ := by rfl


/- One multiply infinity equals infinity-/
@[simp]
theorem one_mul_inf:  EComplex.mul (1:ℂ) ∞ = ∞  := by
  simp only [EComplex.mul, zero_ne_one, reduceIte]

/- Infinity multiply one equals infinity-/
@[simp]
theorem inf_mul_one:  EComplex.mul ∞ (1:ℂ) = ∞  := by
  simp only [EComplex.mul, zero_ne_one, reduceIte]


/- EComplex has unit-/
@[simp]
protected theorem one_mul : ∀ z : EComplex, (1:ℂ) * z = z
  | ∞ => one_mul_inf
  | (z : ℂ) => congr_arg Complex.toEComplex (one_mul z)

@[simp]
protected theorem mul_one : ∀ z : EComplex, z*(1:ℂ)  = z
  | ∞ => one_mul_inf
  | (z : ℂ) => congr_arg Complex.toEComplex (mul_one z)

/- Zero add infinity equals infinity-/
@[simp] theorem zero_add_inf:  EComplex.add (0:ℂ) ∞ = ∞  := by
  simp only [EComplex.add,  zero_ne_one, reduceIte]

/- EComplex has additive identity-/
@[simp] protected theorem zero_add : ∀ z : EComplex, (0:ℂ) + z = z
  | ∞ => zero_add_inf
  | (z : ℂ) => congr_arg Complex.toEComplex (zero_add z)

@[simp] protected theorem add_zero : ∀ z : EComplex, z+(0:ℂ) = z
  | ∞ => zero_add_inf
  | (z : ℂ) => congr_arg Complex.toEComplex (add_zero z)


/- Addition in EComplex is associative-/
@[simp]
protected theorem add_assoc : ∀ a b c : EComplex , (a+b)+c = a+(b+c)
 | ∞ , ∞, ∞  => by rfl
 | (a:ℂ), ∞, ∞ => by rfl
 | ∞, (a:ℂ), ∞ => by rfl
 | ∞, ∞, (a:ℂ) => by rfl
 | ∞, (a:ℂ), (b:ℂ)  => by rfl
 | (a:ℂ), ∞, (b:ℂ)  => by rfl
 | (a:ℂ), (b:ℂ), ∞ => by rfl
 | (a:ℂ), (b:ℂ), (c:ℂ) => by
   rw [← coe_add, ← coe_add, ← coe_add, ← coe_add]
   rw [add_assoc]



/- Multiplication in EComplex is associative-/
@[simp]
protected theorem mul_assoc : ∀ a b c : EComplex ,  (a*b)*c = a*(b*c)
 | ∞, ∞, ∞ => by rfl
 | (a:ℂ), ∞, ∞ => by rfl
 | ∞, (a:ℂ), ∞ => by rfl
 | ∞, ∞, (a:ℂ) => by rfl
 | ∞, (a:ℂ), (b:ℂ)  => by rfl
 | (a:ℂ), ∞, (b:ℂ)  => by rfl
 | (a:ℂ), (b:ℂ), ∞ => by rfl
 | (a:ℂ), (b:ℂ), (c:ℂ) => by
   rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul]
   rw [mul_assoc]

/- Left distributive -/
protected theorem left_dist : ∀ a b c: EComplex, a*(b+c) = a*b+a*c
 | ∞, ∞, ∞ => by rfl
 | (a:ℂ), ∞, ∞ => by rfl
 | ∞, (a:ℂ), ∞ => by rfl
 | ∞, ∞, (a:ℂ) => by rfl
 | ∞, (a:ℂ), (b:ℂ)  => by rfl
 | (a:ℂ), ∞, (b:ℂ)  => by rfl
 | (a:ℂ), (b:ℂ), ∞ => by rfl
 | (a:ℂ), (b:ℂ), (c:ℂ) => by
   rw [← coe_mul, ← coe_mul]
   rw [← coe_add, ← coe_add, ← coe_mul]
   rw [LeftDistribClass.left_distrib a b c]

/- Right distributive -/
protected theorem right_dist : ∀ a b c: EComplex, (b+c)*a = b*a+c*a
 | ∞, ∞, ∞ => by rfl
 | (a:ℂ), ∞, ∞ => by rfl
 | ∞, (a:ℂ), ∞ => by rfl
 | ∞, ∞, (a:ℂ) => by rfl
 | ∞, (a:ℂ), (b:ℂ)  => by rfl
 | (a:ℂ), ∞, (b:ℂ)  => by rfl
 | (a:ℂ), (b:ℂ), ∞ => by rfl
 | (a:ℂ), (b:ℂ), (c:ℂ) => by
   rw [← coe_mul, ← coe_mul]
   rw [← coe_add, ← coe_add, ← coe_mul]
   rw [RightDistribClass.right_distrib b c a]

/- Recursor for scalar multiplication by natural number -/
def nsmulRec : ℕ → EComplex → EComplex
  | 0, _ => (0:ℂ)
  | n + 1, a => nsmulRec n a + a

/-
EComplex is an additive commutative monoid
-/
noncomputable instance : AddCommMonoid EComplex where
 add_assoc := EComplex.add_assoc
 zero := (0:ℂ)
 zero_add := EComplex.zero_add
 add_zero := EComplex.add_zero
 nsmul := EComplex.nsmulRec
 add_comm := EComplex.add_comm


/- Multiplicative inverse in EComplex -/
protected def inv : EComplex → EComplex
  | ∞ => (0:ℂ)
  | (z : ℂ) => if z=(0:ℂ) then ∞ else (z⁻¹ : ℂ)

instance : Inv (EComplex) := ⟨EComplex.inv⟩

/- Extended complex numbers form a monoid under multiplication-/
/- Define a/b as a*b⁻¹ -/
noncomputable instance : DivInvMonoid EComplex where
  mul_assoc := EComplex.mul_assoc
  one := (1:ℂ)
  one_mul:= EComplex.one_mul
  mul_one := EComplex.mul_one


/- Negation is the same as multiplied by minus 1-/
instance : Neg EComplex := ⟨fun z ↦ (-1:ℂ)*z⟩

/- define z-w by z+(-1)*w-/
instance : Sub EComplex := ⟨fun z w ↦ z +(-1:ℂ)*w ⟩



section LFT


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

