/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.algebra_map
import algebra.gcd_domain
import tactic.ring
import tactic.omega

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`monic_mul`, `monic_map`,
and then define `integral_normalization`, which relate arbitrary polynomials to monic ones.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v y
variables {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section semiring
variables [semiring R] {p q r : polynomial R}

lemma monic.as_sum {p : polynomial R} (hp : p.monic) :
  p = X^(p.nat_degree) + (∑ i in finset.range p.nat_degree, C (p.coeff i) * X^i) :=
begin
  conv_lhs { rw [p.as_sum, finset.sum_range_succ] },
  suffices : C (p.coeff p.nat_degree) = 1,
  { rw [this, one_mul] },
  exact congr_arg C hp
end

lemma ne_zero_of_monic_of_zero_ne_one (hp : monic p) (h : (0 : R) ≠ 1) :
  p ≠ 0 := mt (congr_arg leading_coeff) $ by rw [monic.def.1 hp, leading_coeff_zero]; cc

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0 :=
begin
  intro h, rw [h, monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma monic_map [semiring S] (f : R →+* S) (hp : monic p) : monic (p.map f) :=
if h : (0 : S) = 1 then
  by haveI := subsingleton_of_zero_eq_one h;
  exact subsingleton.elim _ _
else
have f (leading_coeff p) ≠ 0,
  by rwa [show _ = _, from hp, is_semiring_hom.map_one f, ne.def, eq_comm],
by
begin
  rw [monic, leading_coeff, coeff_map],
  suffices : p.coeff (map f p).nat_degree = 1, simp [this],
  suffices : (map f p).nat_degree = p.nat_degree, rw this, exact hp,
  rwa nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero _ _),
end
theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, eq_of_zero_eq_one
    (H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n,
    by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem monic_X_add_C (x : R) : monic (X + C x) :=
pow_one (X : polynomial R) ▸ monic_X_pow_add degree_C_le

lemma monic_mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : R) = 1 then by haveI := subsingleton_of_zero_eq_one h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic_pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := monic_mul hp (monic_pow n)

end semiring

section comm_semiring
variables [comm_semiring R] {p : polynomial R}

lemma monic_prod_of_monic (s : finset ι) (f : ι → polynomial R) (hs : ∀ i ∈ s, monic (f i)) :
monic (∏ i in s, f i) :=
prod_induction _ _ (@monic_mul _ _) monic_one hs

lemma is_unit_C {x : R} : is_unit (C x) ↔ is_unit x :=
begin
  rw [is_unit_iff_dvd_one, is_unit_iff_dvd_one],
  split,
  { rintros ⟨g, hg⟩,
    replace hg := congr_arg (eval 0) hg,
    rw [eval_one, eval_mul, eval_C] at hg,
    exact ⟨g.eval 0, hg⟩ },
  { rintros ⟨y, hy⟩,
    exact ⟨C y, by rw [← C_mul, ← hy, C_1]⟩ }
end

lemma eq_one_of_is_unit_of_monic (hm : monic p) (hpu : is_unit p) : p = 1 :=
have degree p ≤ 0,
  from calc degree p ≤ degree (1 : polynomial R) :
    let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu in
    if hu0 : u = 0
    then begin
        rw [hu0, mul_zero] at hu,
        rw [← mul_one p, hu, mul_zero],
        simp
      end
    else have p.leading_coeff * u.leading_coeff ≠ 0,
        by rw [hm.leading_coeff, one_mul, ne.def, leading_coeff_eq_zero];
          exact hu0,
      by rw [hu, degree_mul' this];
        exact le_add_of_nonneg_right (degree_nonneg_iff_ne_zero.2 hu0)
  ... ≤ 0 : degree_one_le,
by rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this,
    ← leading_coeff, hm.leading_coeff, C_1]


end comm_semiring

section comm_ring
variables [comm_ring R]
namespace monic

lemma coeff_nat_degree {p : polynomial R} (hp : p.monic) : p.coeff (p.nat_degree) = 1 := hp

@[simp]
lemma degree_eq_zero_iff_eq_one {p : polynomial R} (hp : p.monic) :
p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have : p = C (p.coeff 0),
  { rw ← polynomial.degree_le_zero_iff,
    rwa polynomial.nat_degree_eq_zero_iff_degree_le_zero at h },
  rw this, convert C_1, rw ← h, apply hp,
end

lemma nat_degree_mul [nontrivial R] {p q : polynomial R} (hp : p.monic) (hq : q.monic) :
(p * q).nat_degree = p.nat_degree + q.nat_degree :=
by { apply nat_degree_mul', rw [hp.leading_coeff, hq.leading_coeff], simp }

lemma next_coeff_mul {p q : polynomial R} (hp : monic p) (hq : monic q) :
next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  classical,
  by_cases h : nontrivial R, swap,
  { rw nontrivial_iff at h, push_neg at h, apply h, },
  haveI := h, clear h,
  have := monic.nat_degree_mul hp hq,
  dsimp [next_coeff], rw this, simp [hp, hq], clear this,
  split_ifs; try { tauto <|> simp [h_1, h_2] },
  rename h_1 hp0, rename h_2 hq0, clear h,
  rw ← degree_eq_zero_iff_eq_one at hp0 hq0, assumption',
  -- we've reduced to the case where the degrees dp and dq are nonzero
  set dp := p.nat_degree, set dq := q.nat_degree,
  rw coeff_mul,
  have : {(dp, dq - 1), (dp - 1, dq)} ⊆ nat.antidiagonal (dp + dq - 1),
  { rw insert_subset, split,
    work_on_goal 0 { rw [nat.mem_antidiagonal, nat.add_sub_assoc] },
    work_on_goal 1 { simp only [singleton_subset_iff, nat.mem_antidiagonal], apply nat.sub_add_eq_add_sub },
    all_goals { apply nat.succ_le_of_lt, apply nat.pos_of_ne_zero, assumption } },
  rw ← sum_subset this,
  { rw [sum_insert, sum_singleton], iterate 2 { rw coeff_nat_degree }, ring, assumption',
    suffices : dp ≠ dp - 1, { rw mem_singleton, simp [this] }, omega }, clear this,
  intros x hx hx1, simp only [nat.mem_antidiagonal] at hx, simp only [mem_insert, mem_singleton] at hx1,
  suffices : p.coeff x.fst = 0 ∨ q.coeff x.snd = 0, cases this; simp [this],
  suffices : dp < x.fst ∨ dq < x.snd, cases this,
  { left,  apply coeff_eq_zero_of_nat_degree_lt, assumption },
  { right, apply coeff_eq_zero_of_nat_degree_lt, assumption },
  by_cases h : dp < x.fst, { tauto }, push_neg at h, right,
  have : x.fst ≠ dp - 1, { contrapose! hx1, right, ext, assumption, dsimp, omega },
  have : x.fst ≠ dp,     { contrapose! hx1, left,  ext, assumption, dsimp, omega },
  omega,
end

lemma next_coeff_prod
  (s : finset ι) (f : ι → polynomial R) (h : ∀ i ∈ s, monic (f i)) :
next_coeff (∏ i in s, f i) = ∑ i in s, next_coeff (f i) :=
begin
  classical,
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
  finset.prod_empty, not_false_iff, forall_true_iff],
  rw ← C_1, rw next_coeff_C_eq_zero },
  { intros a s ha hs monic,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    rw next_coeff_mul (monic a (finset.mem_insert_self a s)), swap,
    { apply monic_prod_of_monic, intros b bs,
      apply monic, apply finset.mem_insert_of_mem bs },
    { refine congr rfl (hs _),
      intros b bs, apply monic, apply finset.mem_insert_of_mem bs }}
end

end monic
end comm_ring

section ring
variables [ring R] {p : polynomial R}

theorem monic_X_sub_C (x : R) : monic (X - C x) :=
by simpa only [C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

section injective
open function
variables [semiring S] {f : R →+* S} (hf : injective f)
include hf


lemma leading_coeff_of_injective (p : polynomial R) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map' hf p]
end

lemma monic_of_injective {p : polynomial R} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, is_semiring_hom.map_one f]
end

end injective
end ring


section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial R) :=
by simpa only [monic, leading_coeff_zero] using (zero_ne_one : (0 : R) ≠ 1)

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 :=
λ h₁, @not_monic_zero R _ _ (h₁ ▸ h)

end nonzero_semiring


section integral_normalization

section semiring
variables [semiring R]

/-- If `f : polynomial R` is a nonzero polynomial with root `z`, `integral_normalization f` is
a monic polynomial with root `leading_coeff f * z`.

Moreover, `integral_normalization 0 = 0`.
-/
noncomputable def integral_normalization (f : polynomial R) : polynomial R :=
on_finset f.support
  (λ i, if f.degree = i then 1 else coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i))
  begin
    intros i h,
    apply mem_support_iff.mpr,
    split_ifs at h with hi,
    { exact coeff_ne_zero_of_eq_degree hi },
    { exact left_ne_zero_of_mul h },
  end

lemma integral_normalization_coeff_degree {f : polynomial R} {i : ℕ} (hi : f.degree = i) :
  (integral_normalization f).coeff i = 1 :=
if_pos hi

lemma integral_normalization_coeff_nat_degree {f : polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).coeff (nat_degree f) = 1 :=
integral_normalization_coeff_degree (degree_eq_nat_degree hf)

lemma integral_normalization_coeff_ne_degree {f : polynomial R} {i : ℕ} (hi : f.degree ≠ i) :
  coeff (integral_normalization f) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
if_neg hi

lemma integral_normalization_coeff_ne_nat_degree {f : polynomial R} {i : ℕ} (hi : i ≠ nat_degree f) :
  coeff (integral_normalization f) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
integral_normalization_coeff_ne_degree (degree_ne_of_nat_degree_ne hi.symm)

lemma monic_integral_normalization {f : polynomial R} (hf : f ≠ 0) :
  monic (integral_normalization f) :=
begin
  apply monic_of_degree_le f.nat_degree,
  { refine finset.sup_le (λ i h, _),
    rw [integral_normalization, mem_support_iff, on_finset_apply] at h,
    split_ifs at h with hi,
    { exact le_trans (le_of_eq hi.symm) degree_le_nat_degree },
    { erw [with_bot.some_le_some],
      apply le_nat_degree_of_ne_zero,
      exact left_ne_zero_of_mul h } },
  { exact integral_normalization_coeff_nat_degree hf }
end

end semiring

section domain
variables [integral_domain R]

@[simp] lemma support_integral_normalization {f : polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).support = f.support :=
begin
  ext i,
  simp only [integral_normalization, on_finset_apply, mem_support_iff],
  split_ifs with hi,
  { simp only [ne.def, not_false_iff, true_iff, one_ne_zero, hi],
    exact coeff_ne_zero_of_eq_degree hi },
  split,
  { intro h,
    exact left_ne_zero_of_mul h },
  { intro h,
    refine mul_ne_zero h (pow_ne_zero _ _),
    exact λ h, hf (leading_coeff_eq_zero.mp h) }
end

variables [comm_ring S]

lemma integral_normalization_eval₂_eq_zero {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  eval₂ f (z * f p.leading_coeff) (integral_normalization p) = 0 :=
calc eval₂ f (z * f p.leading_coeff) (integral_normalization p)
    = p.support.attach.sum
        (λ i, f (coeff (integral_normalization p) i.1 * p.leading_coeff ^ i.1) * z ^ i.1) :
      by { rw [eval₂, finsupp.sum, support_integral_normalization hp],
           simp only [mul_comm z, mul_pow, mul_assoc, ring_hom.map_pow, ring_hom.map_mul],
           exact finset.sum_attach.symm }
... = p.support.attach.sum
        (λ i, f (coeff p i.1 * p.leading_coeff ^ (nat_degree p - 1)) * z ^ i.1) :
      begin
        have one_le_deg : 1 ≤ nat_degree p :=
          nat.succ_le_of_lt (nat_degree_pos_of_eval₂_root hp f hz inj),
        congr,
        ext i,
        congr' 2,
        by_cases hi : i.1 = nat_degree p,
        { rw [hi, integral_normalization_coeff_degree, one_mul, leading_coeff, ←pow_succ,
              nat.sub_add_cancel one_le_deg],
          exact degree_eq_nat_degree hp },
        { have : i.1 ≤ p.nat_degree - 1 := nat.le_pred_of_lt (lt_of_le_of_ne
            (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.mp i.2)) hi),
          rw [integral_normalization_coeff_ne_nat_degree hi, mul_assoc, ←pow_add,
              nat.sub_add_cancel this] }
      end
... = f p.leading_coeff ^ (nat_degree p - 1) * eval₂ f z p :
      by { simp_rw [eval₂, finsupp.sum, λ i, mul_comm (coeff p i), ring_hom.map_mul,
                    ring_hom.map_pow, mul_assoc, ←finset.mul_sum],
           congr' 1,
           exact @finset.sum_attach _ _ p.support _ (λ i, f (p.coeff i) * z ^ i) }
... = 0 : by rw [hz, _root_.mul_zero]

lemma integral_normalization_aeval_eq_zero [algebra R S] {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  aeval (z * algebra_map R S f.leading_coeff) (integral_normalization f) = 0 :=
integral_normalization_eval₂_eq_zero hf (algebra_map R S) hz inj
end domain
end integral_normalization



end polynomial
