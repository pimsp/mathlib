/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.degree.basic

/-!
# Theory of univariate polynomials

The main results are `induction_on` and `as_sum`.
-/

noncomputable theory

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z}
  {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : polynomial R}

lemma sum_C_mul_X_eq (p : polynomial R) : p.sum (λn a, C a * X^n) = p :=
eq.trans (sum_congr rfl $ assume n hn, single_eq_C_mul_X.symm) (finsupp.sum_single _)

lemma sum_monomial_eq (p : polynomial R) : p.sum (λn a, monomial n a) = p :=
by simp only [single_eq_C_mul_X, sum_C_mul_X_eq]

@[elab_as_eliminator] protected lemma induction_on {M : polynomial R → Prop} (p : polynomial R)
  (h_C : ∀a, M (C a))
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (C a * X^n) → M (C a * X^(n+1))) :
  M p :=
have ∀{n:ℕ} {a}, M (C a * X^n),
begin
  assume n a,
  induction n with n ih,
  { simp only [pow_zero, mul_one, h_C] },
  { exact h_monomial _ _ ih }
end,
finsupp.induction p
  (suffices M (C 0), by { convert this, exact single_zero.symm, },
    h_C 0)
  (assume n a p _ _ hp, suffices M (C a * X^n + p), by { convert this, exact single_eq_C_mul_X },
    h_add _ _ this hp)

/--
To prove something about polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator] protected lemma induction_on' {M : polynomial R → Prop} (p : polynomial R)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (monomial n a)) :
  M p :=
polynomial.induction_on p (h_monomial 0) h_add
(λ n a h, begin rw ← single_eq_C_mul_X at ⊢, exact h_monomial _ _, end)


section coeff

theorem coeff_mul_monomial (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (p * monomial n r) (d + n) = coeff p d * r :=
by rw [single_eq_C_mul_X, ←X_pow_mul, ←mul_assoc, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : polynomial R) (n d : ℕ) (r : R) :
  coeff (monomial n r * p) (d + n) = r * coeff p d :=
by rw [single_eq_C_mul_X, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : polynomial R) (d : ℕ) (r : R) :
  coeff (p * monomial 0 r) d = coeff p d * r :=
coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : polynomial R) (d : ℕ) (r : R) :
  coeff (monomial 0 r * p) d = r * coeff p d :=
coeff_monomial_mul p 0 d r

end coeff

-- TODO find a home (this file)
@[simp] lemma finset_sum_coeff (s : finset ι) (f : ι → polynomial R) (n : ℕ) :
  coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
(s.sum_hom (λ q : polynomial R, lcoeff R n q)).symm

lemma as_sum (p : polynomial R) :
  p = ∑ i in range (p.nat_degree + 1), C (p.coeff i) * X^i :=
begin
  ext n,
  simp only [add_comm, coeff_X_pow, coeff_C_mul, finset.mem_range,
    finset.sum_mul_boole, finset_sum_coeff, ite_le_nat_degree_coeff],
end

/--
We can reexpress a sum over `p.support` as a sum over `range n`,
for any `n` satisfying `p.nat_degree < n`.
-/
lemma sum_over_range' [add_comm_monoid S] (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
  (n : ℕ) (w : p.nat_degree < n) :
  p.sum f = ∑ (a : ℕ) in range n, f a (coeff p a) :=
begin
  rw finsupp.sum,
  apply finset.sum_bij_ne_zero (λ n _ _, n),
  { intros k h₁ h₂, simp only [mem_range],
    calc k ≤ p.nat_degree : _
       ... < n : w,
    rw finsupp.mem_support_iff at h₁,
    exact le_nat_degree_of_ne_zero h₁, },
  { intros, assumption },
  { intros b hb hb',
    refine ⟨b, _, hb', rfl⟩,
    rw finsupp.mem_support_iff,
    contrapose! hb',
    convert h b, },
  { intros, refl }
end
/--
We can reexpress a sum over `p.support` as a sum over `range (p.nat_degree + 1)`.
-/
-- See also `as_sum`.
lemma sum_over_range [add_comm_monoid S] (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)



end semiring
end polynomial
