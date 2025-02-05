/-

Construct the extended complex number system by
adjoining a point at infinity to the complex number


Reference:

one-point compactification
Mathlib/Topology/Compactification/OnePoint.lean

Extended real number
Mathlib/Data/Real/EReal.html

-/

import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

open Complex

noncomputable section

/- Define extended complex number by adding a point to ℂ -/
/-
 We implement it by the class of Option in LEAN,
 and use the term `none` in Option as the point at infinity.
-/
def EComplex := Option ℂ



deriving instance Nontrivial, Inhabited
  for EComplex

notation "ℂ∞" => EComplex

/- Denote the term `none` in Option by symbol `∞` -/
notation "∞" => (none: EComplex)


namespace EComplex

/- The extra point is printed as ∞ -/
unsafe instance instRepr [Repr ℂ] : Repr (EComplex) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => repr a⟩

/- Embedding ℂ in EComplex -/
@[coe, match_pattern] def some : ℂ  → EComplex :=
  Option.some

/-- The canonical inclusion from complex to EComplex. -/
@[coe, match_pattern] def Complex.toEComplex : ℂ  → EComplex := some

/- Coecision from type ℂ to type EComplex-/
instance coe : Coe ℂ  EComplex :=
  ⟨some⟩

-- Auxiliary class implementing `Coe*`.
instance : CoeTC ℂ EComplex := ⟨some⟩

-- def a0 : EComplex  := ∞
-- def a1 : EComplex := (5: Real)

-- #eval a0
-- #eval a1


instance : Inhabited EComplex := ⟨ (0:ℂ) ⟩

@[simp]
theorem coe_zero : ((0 : ℂ) : EComplex) = (0:ℂ) := rfl

@[simp]
theorem coe_one : ((1 : ℂ) : EComplex) = (1:ℂ) := rfl


instance decidableEq : DecidableRel ((· = ·) : EComplex → EComplex → Prop) :=
  Option.instDecidableEq


/-- The map from extended complex to complex sending infinity to zero. -/
def toComplex : EComplex → ℂ
  | ∞ => 0
  | (x : ℂ ) => x

@[simp]
theorem toComplex_Inf : toComplex ∞ = 0 :=
  rfl

@[simp]
lemma some_eq_iff (a b : ℂ) : (Complex.toEComplex a = Complex.toEComplex b) ↔ (a = b) := by
  rw [iff_eq_eq]
  exact Option.some.injEq a b

-- Coecion is injective
theorem coe_injective : Function.Injective Complex.toEComplex := by
  unfold Function.Injective
  intro a b hab
  exact (some_eq_iff a b).mp hab

@[norm_cast]
theorem coe_eq_coe {x y : ℂ} : (x : EComplex) = y ↔ x = y :=
  coe_injective.eq_iff


@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℂ} : (x : EComplex) = (y : EComplex) ↔ x = y :=
  coe_injective.eq_iff

protected theorem coe_ne_coe_iff {x y : ℂ} : (x : EComplex) ≠ (y : EComplex) ↔ x ≠ y :=
  coe_injective.ne_iff



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


/- Subtraction in EComplex -/
protected def sub : EComplex → EComplex → EComplex :=
  fun z w => z + (-1:ℂ)*w


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
EComplex is an additive commutative monoid with one
-/
noncomputable instance instAddCommMonoidWithOneEComplex: AddCommMonoidWithOne EComplex where
 add_assoc := EComplex.add_assoc
 zero := (0:ℂ)
 zero_add := EComplex.zero_add
 add_zero := EComplex.add_zero
 nsmul := EComplex.nsmulRec
 one := (1:ℂ)
 add_comm := EComplex.add_comm



/- Multiplicative inverse in EComplex -/
protected def inv : EComplex → EComplex
  | ∞ => (0:ℂ)
  | (z : ℂ) => if z=(0:ℂ) then ∞ else (z⁻¹ : ℂ)

instance : Inv (EComplex) := ⟨EComplex.inv⟩

/- Division in EComplex -/
protected def div : EComplex → EComplex → EComplex :=
  fun z w => z * (EComplex.inv w)


/- Extended complex numbers form a monoid under multiplication-/
/- Define a/b as a*b⁻¹ -/
noncomputable instance : DivInvMonoid EComplex where
  mul_assoc := EComplex.mul_assoc
  one := (1:ℂ)
  one_mul:= EComplex.one_mul
  mul_one := EComplex.mul_one


/- Negation is the same as multiplied by minus 1-/
instance : Neg EComplex := ⟨fun z ↦ (-1:ℂ)*z⟩

/- define subtraction z-w by z+(-1)*w-/
instance : Sub EComplex := ⟨fun z w ↦ z +(-1:ℂ)*w ⟩



/- A finite complex number is not equal to the point at infinity-/
@[simp]
theorem neq_inf (a:ℂ) : ↑a ≠ ∞ := by
  exact ne_of_beq_false rfl




/-
  The computer now has the vocabulary of infinity
  Some examples of calculations are given below
-/

-- 3+∞ = ∞
example :  (3:EComplex).add ∞ = ∞ := by rfl

-- 2-∞ = ∞
example :  (2:EComplex).sub ∞ = ∞ := by rfl

-- 1/∞ = 0
example : (1:EComplex).div ∞ = 0 := by
   rw [EComplex.div]
   simp only [inv_inf, one_mul]
   rfl

/- a*0 = 0 for any complex number a-/
@[simp]
theorem mul_zero_eq_zero (a:ℂ): (a:EComplex).mul 0 = 0 := by
  calc
    (a:EComplex).mul 0 = ↑(a * 0) := by rfl
                     _ = ↑0 := by exact congr_arg Complex.toEComplex (mul_zero a)

/- 0*a = 0 for any complex number a-/
@[simp]
theorem zero_mul_eq_zero (a:ℂ): (0:EComplex).mul a = 0 := by
  calc
    (0:EComplex).mul a = ↑(0 * a) := by rfl
                     _ = ↑0 := by exact congr_arg Complex.toEComplex (zero_mul a)

/-  a/∞ =0 for all complex number a -/
@[simp]
theorem div_inf_eq_zero (a:ℂ): (a:EComplex).div ∞ = 0 := by
  exact mul_zero_eq_zero a

/- a/0 = ∞ for complex number a -/
@[simp]
theorem div_zero_eq_inf (a:ℂ) :  (a:EComplex).div 0 = ∞ := by
  rw [EComplex.div, EComplex.inv]
  simp only [reduceIte]
  rfl

example : EComplex.div (-431) 0 = ∞ := by
  rw [EComplex.div, EComplex.inv]
  simp only [↓reduceIte]
  rfl



end EComplex   -- end of the EComplex namespace
