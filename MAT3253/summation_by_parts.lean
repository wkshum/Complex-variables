/-
Copyright (c) 2025 Kenneth Shum All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenneth Shum
-/


import Mathlib.Tactic
import Mathlib.Data.Complex.Basic


open Finset BigOperators Complex

/- summation by parts

We are given two sequences a_n and b_n.
Define the partial sum B_N as b_1+b_2+...+b_N
B_0 is defined as 0.

The summation-by-parts formual is the analog of
integration by parts in the discrete case.

a_M*b_M + ... + a_N b_N

=     a_N * (B_N - B_{N-1})
  + a_{N-1} (B_N - B_{N-1})
  + a_{N-2} (B_{N-1} - B_{N-2})
          ...
  + a_M (B_{M}} - B_{M-1})

= a_N*b_N - a_M*B_{M-1}+ (a_N- a_{N-1})*B_{N-1}+ ... + (a_{M+1}}-a_M)*B_{M+1}

-/

theorem summation_by_parts [CommRing R] {M:ℕ} {hM: 1≤ M} (N:ℕ) (hMN : M≤ N) (a b : ℕ → R) :
let B (k:ℕ) := ∑ n ∈ Ico 1 (k+1), b n
  ∑ n ∈ Ico M (N+1), (a n)*(b n)
      = (a N)*(B N)  -  (a M)*(B (M-1)) - ∑ n ∈ Ico M N, ((a (n+1)) - (a n))*(B n)  := by
  intro B

  -- Express b_k in terms of the difference of two partial sums
  have h₁ : ∀ k ≥ 1 , b k = B k - B (k-1) := by
    intro k hk
    simp only [B]
    rw [sum_Ico_succ_top hk (fun m => (b m))]
    symm
    calc
        ∑ k ∈ Ico 1 k, b k + b k - ∑ n ∈ Ico 1 (k - 1 + 1), b n
       = ∑ k ∈ Ico 1 k, b k + b k - ∑ n ∈ Ico 1 k, b n := by rfl
      _= b k := by ring

  have h₂ : ∀ k ≥ 1, (a k) * (b k) =  (a k) * (B k) - (a k) *(B (k-1)) := by
    intro k hk
    rw [h₁ k hk]
    ring

  -- if x is in [M, N+1), then M ≤ x
  have h₃ {x N:ℕ} : x ∈ Ico M (N+1) → 1 ≤ x := by
    intro hx
    have : M≤x := ((Finset.mem_Ico.mp) hx).1
    exact Nat.le_trans hM this    -- 1≤M and M≤ x implies 1≤x

  -- replace b k by B k - B (k-1) in the summation
  rw [sum_congr rfl fun x x_in_Ico => (h₂ x (h₃ x_in_Ico))]

  rw [sum_sub_distrib] -- apply the distributive law for series

  -- separate the top term of a series
  rw [sum_Ico_succ_top hMN (fun m => (a m) *(B m))]

  -- isolate the lowest term in a series
  have : ∑ n ∈ Ico M (N+1), ((a n)*(B (n-1))) = (a M)*(B (M-1)) +  ∑ n ∈ Ico (M+1) (N+1), ((a n)*(B (n-1)))
    := by
    have one_lt_N_plus_1 : M < N+1 :=  Nat.lt_succ_of_le hMN
    exact sum_eq_sum_Ico_succ_bot one_lt_N_plus_1 (fun m ↦ (a m)*(B (m-1)))
  rw [this]

  -- change the indexing set from Ico M+1 N+1 to Ico M N
  have : ∑ n ∈ Ico (M+1) (N+1), ((a n)*(B (n-1))) = ∑ n ∈ Ico M N, ((a (n+1))*(B n)) := by
    calc
        ∑ n ∈ Ico (M+1) (N+1), ((a n)*(B (n-1)))
      = ∑ n ∈ Ico M N, (a (n+1))*(B ((n+1)-1))
         := by exact (sum_Ico_add' (fun m => (a m)*(B (m-1))) M N 1).symm
     _= ∑ n ∈ Ico M N, ((a (n+1))*(B n)) := by rfl
  rw [this]

  have : ∑ n ∈ Ico M N, (a n)*(B n) + (a N)*(B N) - ( (a M)*(B (M-1)) + ∑ n ∈ Ico M N, ((a (n+1))*(B n))) =
    (a N)*(B N) - (a M)*(B (M-1)) - (∑ n ∈ Ico M N, ((a (n+1))*(B n)) - ∑ n ∈ Ico M N, (a n)*(B n))
    := by ring
  rw [this]  -- re-arrange terms according to the above equation

  rw [←sum_sub_distrib]  -- apply the distributive law for series

  -- simplify the terms in the summation
  have :∀ n,  (a (n+1))*(B n) - (a n)*(B n) = (a (n+1) - (a n))*(B n) := by
    intro n ; ring
  rw [sum_congr rfl fun x _a ↦ this x]



-- A special case of the above theorem, with M=1.
-- We prove it just by applying `summation_by_parts`, and check that B_0=0.
theorem summation_by_parts' (N:ℕ) (hN : 1≤ N) (a b : ℕ → ℂ) :
let B (k:ℕ) := ∑ n ∈ Ico 1 (k+1), b n
  ∑ n ∈ Ico 1 (N+1), (a n)*(b n)
      = (a N)*(B N)  - ∑ n ∈ Ico 1 N, ((a (n+1)) - (a n))*(B n)   := by
  rw [summation_by_parts N  hN a b]
  intro B
  simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, zero_add, Ico_eq_empty_of_le, sum_empty,
    mul_zero, sub_zero]

  -- the statement is reduced to `1 ≤ 1`
  exact NeZero.one_le

)
