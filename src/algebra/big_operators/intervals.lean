/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.big_operators.basic
import data.finset.intervals


/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/

universes u v w

open_locale big_operators

namespace finset

variables {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : finset α} {a : α} {g f : α → β} [comm_monoid β]

lemma sum_Ico_add {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (m n k : ℕ) :
  (∑ l in Ico m n, f (k + l)) = (∑ l in Ico (m + k) (n + k), f l) :=
Ico.image_add m n k ▸ eq.symm $ sum_image $ λ x hx y hy h, nat.add_left_cancel h

@[to_additive]
lemma prod_Ico_add (f : ℕ → β) (m n k : ℕ) :
  (∏ l in Ico m n, f (k + l)) = (∏ l in Ico (m + k) (n + k), f l) :=
@sum_Ico_add (additive β) _ f m n k

lemma sum_Ico_succ_top {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a ≤ b) (f : ℕ → δ) : (∑ k in Ico a (b + 1), f k) = (∑ k in Ico a b, f k) + f b :=
by rw [Ico.succ_top hab, sum_insert Ico.not_mem_top, add_comm]

@[to_additive]
lemma prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
  (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b :=
@sum_Ico_succ_top (additive β) _ _ _ hab _

lemma sum_eq_sum_Ico_succ_bot {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a < b) (f : ℕ → δ) : (∑ k in Ico a b, f k) = f a + (∑ k in Ico (a + 1) b, f k) :=
have ha : a ∉ Ico (a + 1) b, by simp,
by rw [← sum_insert ha, Ico.insert_succ_bot hab]

@[to_additive]
lemma prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
  (∏ k in Ico a b, f k) = f a * (∏ k in Ico (a + 1) b, f k) :=
@sum_eq_sum_Ico_succ_bot (additive β) _ _ _ hab _

@[to_additive]
lemma prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
  (∏ i in Ico m n, f i) * (∏ i in Ico n k, f i) = (∏ i in Ico m k, f i) :=
Ico.union_consecutive hmn hnk ▸ eq.symm $ prod_union $ Ico.disjoint_consecutive m n k

@[to_additive]
lemma prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
  (∏ k in range m, f k) * (∏ k in Ico m n, f k) = (∏ k in range n, f k) :=
Ico.zero_bot m ▸ Ico.zero_bot n ▸ prod_Ico_consecutive f (nat.zero_le m) h

@[to_additive]
lemma prod_Ico_eq_mul_inv {δ : Type*} [comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∏ k in Ico m n, f k) = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
eq_mul_inv_iff_mul_eq.2 $ by rw [mul_comm]; exact prod_range_mul_prod_Ico f h

lemma sum_Ico_eq_sub {δ : Type*} [add_comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∑ k in Ico m n, f k) = (∑ k in range n, f k) - (∑ k in range m, f k) :=
sum_Ico_eq_add_neg f h

@[to_additive]
lemma prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
  (∏ k in Ico m n, f k) = (∏ k in range (n - m), f (m + k)) :=
begin
  by_cases h : m ≤ n,
  { rw [← Ico.zero_bot, prod_Ico_add, zero_add, nat.sub_add_cancel h] },
  { replace h : n ≤ m :=  le_of_not_ge h,
     rw [Ico.eq_empty_of_le h, nat.sub_eq_zero_of_le h, range_zero, prod_empty, prod_empty] }
end

lemma prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
  ∏ j in Ico k m, f (n - j) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j :=
begin
  have : ∀ i < m, i ≤ n,
  { intros i hi,
    exact (add_le_add_iff_right 1).1 (le_trans (nat.lt_iff_add_one_le.1 hi) h) },
  cases lt_or_le k m with hkm hkm,
  { rw [← finset.Ico.image_const_sub (this _ hkm)],
    refine (prod_image _).symm,
    simp only [Ico.mem],
    rintros i ⟨ki, im⟩ j ⟨kj, jm⟩ Hij,
    rw [← nat.sub_sub_self (this _ im), Hij, nat.sub_sub_self (this _ jm)] },
  { simp [Ico.eq_empty_of_le, nat.sub_le_sub_left, hkm] }
end

lemma sum_Ico_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
  (h : m ≤ n + 1) :
  ∑ j in Ico k m, f (n - j) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
@prod_Ico_reflect (multiplicative δ) _ f k m n h

lemma prod_range_reflect (f : ℕ → β) (n : ℕ) :
  ∏ j in range n, f (n - 1 - j) = ∏ j in range n, f j :=
begin
  cases n,
  { simp },
  { simp only [range_eq_Ico, nat.succ_sub_succ_eq_sub, nat.sub_zero],
    rw [prod_Ico_reflect _ _ (le_refl _)],
    simp }
end

lemma sum_range_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (n : ℕ) :
  ∑ j in range n, f (n - 1 - j) = ∑ j in range n, f j :=
@prod_range_reflect (multiplicative δ) _ f n

@[simp] lemma prod_Ico_id_eq_fact : ∀ n : ℕ, ∏ x in Ico 1 (n + 1), x = nat.fact n
| 0 := rfl
| (n+1) := by rw [prod_Ico_succ_top $ nat.succ_le_succ $ zero_le n,
  nat.fact_succ, prod_Ico_id_eq_fact n, nat.succ_eq_add_one, mul_comm]

section gauss_sum

/-- Gauss' summation formula -/
lemma sum_range_id_mul_two (n : ℕ) :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
calc (∑ i in range n, i) * 2 = (∑ i in range n, i) + (∑ i in range n, (n - 1 - i)) :
  by rw [sum_range_reflect (λ i, i) n, mul_two]
... = ∑ i in range n, (i + (n - 1 - i)) : sum_add_distrib.symm
... = ∑ i in range n, (n - 1) : sum_congr rfl $ λ i hi, nat.add_sub_cancel' $
  nat.le_pred_of_lt $ mem_range.1 hi
... = n * (n - 1) : by rw [sum_const, card_range, nat.nsmul_eq_mul]

/-- Gauss' summation formula -/
lemma sum_range_id (n : ℕ) : (∑ i in range n, i) = (n * (n - 1)) / 2 :=
by rw [← sum_range_id_mul_two n, nat.mul_div_cancel]; exact dec_trivial

end gauss_sum

end finset
