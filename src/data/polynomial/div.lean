/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.monic
import ring_theory.euclidean_domain
import ring_theory.multiplicity

/-!
# Division of univariate polynomials

The main defs are `div_by_monic` and `mod_by_monic`.
The compatibility between these is given by `mod_by_monic_add_div`.
We also define `root_multiplicity`.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section semiring
variables [semiring R] {p q : polynomial R}

section
/--
The coercion turning a `polynomial` into the function which reports the coefficient of a given
monomial `X^n`
-/
-- TODO we would like to completely remove this, but this requires fixing some proofs
def coeff_coe_to_fun : has_coe_to_fun (polynomial R) :=
finsupp.has_coe_to_fun

local attribute [instance] coeff_coe_to_fun

lemma apply_eq_coeff : p n = coeff p n := rfl
end

/-- `div_X p` return a polynomial `q` such that `q * X + C (p.coeff 0) = p`.
  It can be used in a semiring where the usual division algorithm is not possible -/
def div_X (p : polynomial R) : polynomial R :=
{ to_fun := λ n, p.coeff (n + 1),
  support := ⟨(p.support.filter (> 0)).1.map (λ n, n - 1),
    multiset.nodup_map_on begin
        simp only [finset.mem_def.symm, finset.mem_erase, finset.mem_filter],
        assume x hx y hy hxy,
        rwa [← @add_right_cancel_iff _ _ 1, nat.sub_add_cancel hx.2,
          nat.sub_add_cancel hy.2] at hxy
      end
      (p.support.filter (> 0)).2⟩,
  mem_support_to_fun := λ n,
    suffices (∃ (a : ℕ), (¬coeff p a = 0 ∧ a > 0) ∧ a - 1 = n) ↔
      ¬coeff p (n + 1) = 0,
    by simpa [finset.mem_def.symm],
    ⟨λ ⟨a, ha⟩, by rw [← ha.2, nat.sub_add_cancel ha.1.2]; exact ha.1.1,
      λ h, ⟨n + 1, ⟨h, nat.succ_pos _⟩, nat.succ_sub_one _⟩⟩ }

lemma div_X_mul_X_add (p : polynomial R) : div_X p * X + C (p.coeff 0) = p :=
ext $ λ n,
  nat.cases_on n
   (by simp)
   (by simp [coeff_C, nat.succ_ne_zero, coeff_mul_X, div_X])

@[simp] lemma div_X_C (a : R) : div_X (C a) = 0 :=
ext $ λ n, by cases n; simp [div_X, coeff_C]; simp [coeff]

lemma div_X_eq_zero_iff : div_X p = 0 ↔ p = C (p.coeff 0) :=
⟨λ h, by simpa [eq_comm, h] using div_X_mul_X_add p,
  λ h, by rw [h, div_X_C]⟩

lemma div_X_add : div_X (p + q) = div_X p + div_X q :=
ext $ by simp [div_X]

lemma degree_div_X_lt (hp0 : p ≠ 0) : (div_X p).degree < p.degree :=
by haveI := nonzero.of_polynomial_ne hp0; exact
calc (div_X p).degree < (div_X p * X + C (p.coeff 0)).degree :
  if h : degree p ≤ 0
  then begin
      have h' : C (p.coeff 0) ≠ 0, by rwa [← eq_C_of_degree_le_zero h],
      rw [eq_C_of_degree_le_zero h, div_X_C, degree_zero, zero_mul, zero_add],
      exact lt_of_le_of_ne bot_le (ne.symm (mt degree_eq_bot.1 $
        by simp [h'])),
    end
  else
    have hXp0 : div_X p ≠ 0,
      by simpa [div_X_eq_zero_iff, -not_le, degree_le_zero_iff] using h,
    have leading_coeff (div_X p) * leading_coeff X ≠ 0, by simpa,
    have degree (C (p.coeff 0)) < degree (div_X p * X),
      from calc degree (C (p.coeff 0)) ≤ 0 : degree_C_le
         ... < 1 : dec_trivial
         ... = degree (X : polynomial R) : degree_X.symm
         ... ≤ degree (div_X p * X) :
          by rw [← zero_add (degree X), degree_mul' this];
            exact add_le_add
              (by rw [zero_le_degree_iff, ne.def, div_X_eq_zero_iff];
                exact λ h0, h (h0.symm ▸ degree_C_le))
              (le_refl _),
    by rw [add_comm, degree_add_eq_of_degree_lt this];
      exact degree_lt_degree_mul_X hXp0
... = p.degree : by rw div_X_mul_X_add
/-- An induction principle for polynomials, valued in Sort* instead of Prop. -/
@[elab_as_eliminator] noncomputable def rec_on_horner
  {M : polynomial R → Sort*} : Π (p : polynomial R),
  M 0 →
  (Π p a, coeff p 0 = 0 → a ≠ 0 → M p → M (p + C a)) →
  (Π p, p ≠ 0 → M p → M (p * X)) →
  M p
| p := λ M0 MC MX,
if hp : p = 0 then eq.rec_on hp.symm M0
else
have wf : degree (div_X p) < degree p,
  from degree_div_X_lt hp,
by rw [← div_X_mul_X_add p] at *;
  exact
  if hcp0 : coeff p 0 = 0
  then by rw [hcp0, C_0, add_zero];
    exact MX _ (λ h : div_X p = 0, by simpa [h, hcp0] using hp)
      (rec_on_horner _ M0 MC MX)
  else MC _ _ (coeff_mul_X_zero _) hcp0 (if hpX0 : div_X p = 0
    then show M (div_X p * X), by rw [hpX0, zero_mul]; exact M0
    else MX (div_X p) hpX0 (rec_on_horner _ M0 MC MX))
using_well_founded {dec_tac := tactic.assumption}

@[elab_as_eliminator] lemma degree_pos_induction_on
  {P : polynomial R → Prop} (p : polynomial R) (h0 : 0 < degree p)
  (hC : ∀ {a}, a ≠ 0 → P (C a * X))
  (hX : ∀ {p}, 0 < degree p → P p → P (p * X))
  (hadd : ∀ {p} {a}, 0 < degree p → P p → P (p + C a)) : P p :=
rec_on_horner p
  (λ h, by rw degree_zero at h; exact absurd h dec_trivial)
  (λ p a _ _ ih h0,
    have 0 < degree p,
      from lt_of_not_ge (λ h, (not_lt_of_ge degree_C_le) $
        by rwa [eq_C_of_degree_le_zero h, ← C_add] at h0),
    hadd this (ih this))
  (λ p _ ih h0',
    if h0 : 0 < degree p
    then hX h0 (ih h0)
    else by rw [eq_C_of_degree_le_zero (le_of_not_gt h0)] at *;
      exact hC (λ h : coeff p 0 = 0,
        by simpa [h, nat.not_lt_zero] using h0'))
  h0

end semiring

section comm_semiring
variables [comm_semiring R]

theorem X_dvd_iff {α : Type u} [comm_semiring α] {f : polynomial α} : X ∣ f ↔ f.coeff 0 = 0 :=
⟨λ ⟨g, hfg⟩, by rw [hfg, mul_comm, coeff_mul_X_zero],
λ hf, ⟨f.div_X, by rw [mul_comm, ← add_zero (f.div_X * X), ← C_0, ← hf, div_X_mul_X_add]⟩⟩

end comm_semiring


section comm_semiring

variables [comm_semiring R] {p q : polynomial R}

lemma multiplicity_finite_of_degree_pos_of_monic (hp : (0 : with_bot ℕ) < degree p)
  (hmp : monic p) (hq : q ≠ 0) : multiplicity.finite p q :=
have zn0 : (0 : R) ≠ 1, from λ h, by haveI := subsingleton_of_zero_eq_one h;
  exact hq (subsingleton.elim _ _),
⟨nat_degree q, λ ⟨r, hr⟩,
  have hp0 : p ≠ 0, from λ hp0, by simp [hp0] at hp; contradiction,
  have hr0 : r ≠ 0, from λ hr0, by simp * at *,
  have hpn1 : leading_coeff p ^ (nat_degree q + 1) = 1,
    by simp [show _ = _, from hmp],
  have hpn0' : leading_coeff p ^ (nat_degree q + 1) ≠ 0,
    from hpn1.symm ▸ zn0.symm,
  have hpnr0 : leading_coeff (p ^ (nat_degree q + 1)) * leading_coeff r ≠ 0,
    by simp only [leading_coeff_pow' hpn0', leading_coeff_eq_zero, hpn1,
      one_pow, one_mul, ne.def, hr0]; simp,
  have hpn0 : p ^ (nat_degree q + 1) ≠ 0,
    from mt leading_coeff_eq_zero.2 $
      by rw [leading_coeff_pow' hpn0', show _ = _, from hmp, one_pow]; exact zn0.symm,
  have hnp : 0 < nat_degree p,
    by rw [← with_bot.coe_lt_coe, ← degree_eq_nat_degree hp0];
    exact hp,
  begin
    have := congr_arg nat_degree hr,
    rw [nat_degree_mul' hpnr0,  nat_degree_pow' hpn0', add_mul, add_assoc] at this,
    exact ne_of_lt (lt_add_of_le_of_pos (le_mul_of_one_le_right' (nat.zero_le _) hnp)
      (add_pos_of_pos_of_nonneg (by rwa one_mul) (nat.zero_le _))) this
  end⟩

end comm_semiring


section ring
variables [ring R] {p q : polynomial R}


lemma div_wf_lemma (h : degree q ≤ degree p ∧ p ≠ 0) (hq : monic q) :
  degree (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) < degree p :=
have hp : leading_coeff p ≠ 0 := mt leading_coeff_eq_zero.1 h.2,
have hpq : leading_coeff (C (leading_coeff p) * X ^ (nat_degree p - nat_degree q)) *
    leading_coeff q ≠ 0,
  by rwa [leading_coeff_monomial, monic.def.1 hq, mul_one],
if h0 : p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q = 0
then h0.symm ▸ (lt_of_not_ge $ mt le_bot_iff.1 (mt degree_eq_bot.1 h.2))
else
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic h.2 hq,
  have hlt : nat_degree q ≤ nat_degree p := with_bot.coe_le_coe.1
    (by rw [← degree_eq_nat_degree h.2, ← degree_eq_nat_degree hq0];
    exact h.1),
  degree_sub_lt
  (by rw [degree_mul' hpq, degree_monomial _ hp, degree_eq_nat_degree h.2,
      degree_eq_nat_degree hq0, ← with_bot.coe_add, nat.sub_add_cancel hlt])
  h.2
  (by rw [leading_coeff_mul' hpq, leading_coeff_monomial, monic.def.1 hq, mul_one])

/-- See `div_by_monic`. -/
noncomputable def div_mod_by_monic_aux : Π (p : polynomial R) {q : polynomial R},
  monic q → polynomial R × polynomial R
| p := λ q hq, if h : degree q ≤ degree p ∧ p ≠ 0 then
  let z := C (leading_coeff p) * X^(nat_degree p - nat_degree q)  in
  have wf : _ := div_wf_lemma h hq,
  let dm := div_mod_by_monic_aux (p - z * q) hq in
  ⟨z + dm.1, dm.2⟩
  else ⟨0, p⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `div_by_monic` gives the quotient of `p` by a monic polynomial `q`. -/
def div_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).1 else 0

/-- `mod_by_monic` gives the remainder of `p` by a monic polynomial `q`. -/
def mod_by_monic (p q : polynomial R) : polynomial R :=
if hq : monic q then (div_mod_by_monic_aux p hq).2 else p

infixl  ` /ₘ ` : 70 := div_by_monic

infixl ` %ₘ ` : 70 := mod_by_monic

lemma degree_mod_by_monic_lt : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hq0 : q ≠ 0), degree (p %ₘ q) < degree q
| p := λ q hq hq0,
if h : degree q ≤ degree p ∧ p ≠ 0 then
  have wf : _ := div_wf_lemma ⟨h.1, h.2⟩ hq,
  have degree ((p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) %ₘ q) < degree q :=
      degree_mod_by_monic_lt (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q)
      hq hq0,
  begin
    unfold mod_by_monic at this ⊢,
    unfold div_mod_by_monic_aux,
    rw dif_pos hq at this ⊢,
    rw if_pos h,
    exact this
  end
else
  or.cases_on (not_and_distrib.1 h) begin
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h],
    exact lt_of_not_ge,
  end
  begin
    assume hp,
    unfold mod_by_monic div_mod_by_monic_aux,
    rw [dif_pos hq, if_neg h, not_not.1 hp],
    exact lt_of_le_of_ne bot_le
      (ne.symm (mt degree_eq_bot.1 hq0)),
  end
using_well_founded {dec_tac := tactic.assumption}

@[simp] lemma zero_mod_by_monic (p : polynomial R) : 0 %ₘ p = 0 :=
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma zero_div_by_monic (p : polynomial R) : 0 /ₘ p = 0 :=
begin
  unfold div_by_monic div_mod_by_monic_aux,
  by_cases hp : monic p,
  { rw [dif_pos hp, if_neg (mt and.right (not_not_intro rfl))] },
  { rw [dif_neg hp] }
end

@[simp] lemma mod_by_monic_zero (p : polynomial R) : p %ₘ 0 = p :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold mod_by_monic div_mod_by_monic_aux; rw dif_neg h

@[simp] lemma div_by_monic_zero (p : polynomial R) : p /ₘ 0 = 0 :=
if h : monic (0 : polynomial R) then (subsingleton_of_monic_zero h).1 _ _ else
by unfold div_by_monic div_mod_by_monic_aux; rw dif_neg h

lemma div_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p /ₘ q = 0 := dif_neg hq

lemma mod_by_monic_eq_of_not_monic (p : polynomial R) (hq : ¬monic q) : p %ₘ q = p := dif_neg hq

lemma mod_by_monic_eq_self_iff (hq : monic q) (hq0 : q ≠ 0) : p %ₘ q = p ↔ degree p < degree q :=
⟨λ h, h ▸ degree_mod_by_monic_lt _ hq hq0,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold mod_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

theorem degree_mod_by_monic_le (p : polynomial R) {q : polynomial R}
  (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
decidable.by_cases
  (assume H : q = 0, by rw [monic, H, leading_coeff_zero] at hq;
    have : (0:polynomial R) = 1 := (by rw [← C_0, ← C_1, hq]);
    exact le_of_eq (congr_arg _ $ eq_of_zero_eq_one this (p %ₘ q) q))
  (assume H : q ≠ 0, le_of_lt $ degree_mod_by_monic_lt _ hq H)

end ring



section comm_ring
variables [comm_ring R] {p q : polynomial R}

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial R) {q : polynomial R} (hq : monic q),
  p %ₘ q = p - q * (p /ₘ q)
| p := λ q hq,
  if h : degree q ≤ degree p ∧ p ≠ 0 then
    have wf : _ := div_wf_lemma h hq,
    have ih : _ := mod_by_monic_eq_sub_mul_div
      (p - C (leading_coeff p) * X ^ (nat_degree p - nat_degree q) * q) hq,
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_pos h],
      rw [mod_by_monic, dif_pos hq] at ih,
      refine ih.trans _,
      unfold div_by_monic,
      rw [dif_pos hq, dif_pos hq, if_pos h, mul_add, sub_add_eq_sub_sub, mul_comm]
    end
  else
    begin
      unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
      rw [dif_pos hq, if_neg h, dif_pos hq, if_neg h, mul_zero, sub_zero]
    end
using_well_founded {dec_tac := tactic.assumption}

lemma mod_by_monic_add_div (p : polynomial R) {q : polynomial R} (hq : monic q) :
  p %ₘ q + q * (p /ₘ q) = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

lemma div_by_monic_eq_zero_iff (hq : monic q) (hq0 : q ≠ 0) : p /ₘ q = 0 ↔ degree p < degree q :=
⟨λ h, by have := mod_by_monic_add_div p hq;
  rwa [h, mul_zero, add_zero, mod_by_monic_eq_self_iff hq hq0] at this,
λ h, have ¬ degree q ≤ degree p := not_le_of_gt h,
  by unfold div_by_monic div_mod_by_monic_aux; rw [dif_pos hq, if_neg (mt and.left this)]⟩

lemma degree_add_div_by_monic (hq : monic q) (h : degree q ≤ degree p) :
  degree q + degree (p /ₘ q) = degree p :=
if hq0 : q = 0 then
  have ∀ (p : polynomial R), p = 0,
    from λ p, (@subsingleton_of_monic_zero R _ (hq0 ▸ hq)).1 _ _,
  by rw [this (p /ₘ q), this p, this q]; refl
else
have hdiv0 : p /ₘ q ≠ 0 := by rwa [(≠), div_by_monic_eq_zero_iff hq hq0, not_lt],
have hlc : leading_coeff q * leading_coeff (p /ₘ q) ≠ 0 :=
  by rwa [monic.def.1 hq, one_mul, (≠), leading_coeff_eq_zero],
have hmod : degree (p %ₘ q) < degree (q * (p /ₘ q)) :=
  calc degree (p %ₘ q) < degree q : degree_mod_by_monic_lt _ hq hq0
  ... ≤ _ : by rw [degree_mul' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree hdiv0, ← with_bot.coe_add, with_bot.coe_le_coe];
    exact nat.le_add_right _ _,
calc degree q + degree (p /ₘ q) = degree (q * (p /ₘ q)) : eq.symm (degree_mul' hlc)
... = degree (p %ₘ q + q * (p /ₘ q)) : (degree_add_eq_of_degree_lt hmod).symm
... = _ : congr_arg _ (mod_by_monic_add_div _ hq)

lemma degree_div_by_monic_le (p q : polynomial R) : degree (p /ₘ q) ≤ degree p :=
if hp0 : p = 0 then by simp only [hp0, zero_div_by_monic, le_refl]
else if hq : monic q then
  have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
  if h : degree q ≤ degree p
  then by rw [← degree_add_div_by_monic hq h, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 (not_lt.2 h))];
    exact with_bot.coe_le_coe.2 (nat.le_add_left _ _)
  else
    by unfold div_by_monic div_mod_by_monic_aux;
      simp only [dif_pos hq, h, false_and, if_false, degree_zero, bot_le]
else (div_by_monic_eq_of_not_monic p hq).symm ▸ bot_le

lemma degree_div_by_monic_lt (p : polynomial R) {q : polynomial R} (hq : monic q)
  (hp0 : p ≠ 0) (h0q : 0 < degree q) : degree (p /ₘ q) < degree p :=
have hq0 : q ≠ 0 := ne_zero_of_ne_zero_of_monic hp0 hq,
if hpq : degree p < degree q
then begin
  rw [(div_by_monic_eq_zero_iff hq hq0).2 hpq, degree_eq_nat_degree hp0],
  exact with_bot.bot_lt_some _
end
else begin
  rw [← degree_add_div_by_monic hq (not_lt.1 hpq), degree_eq_nat_degree hq0,
        degree_eq_nat_degree (mt (div_by_monic_eq_zero_iff hq hq0).1 hpq)],
  exact with_bot.coe_lt_coe.2 (nat.lt_add_of_pos_left
    (with_bot.coe_lt_coe.1 $ (degree_eq_nat_degree hq0) ▸ h0q))
end

theorem nat_degree_div_by_monic {R : Type u} [comm_ring R] (f : polynomial R) {g : polynomial R}
  (hg : g.monic) : nat_degree (f /ₘ g) = nat_degree f - nat_degree g :=
begin
  by_cases h01 : (0 : R) = 1,
  { haveI := subsingleton_of_zero_eq_one h01,
    rw [subsingleton.elim (f /ₘ g) 0, subsingleton.elim f 0, subsingleton.elim g 0,
        nat_degree_zero] },
  haveI : nontrivial R := ⟨⟨0, 1, h01⟩⟩,
  by_cases hfg : f /ₘ g = 0,
  { rw [hfg, nat_degree_zero], rw div_by_monic_eq_zero_iff hg hg.ne_zero at hfg,
    rw nat.sub_eq_zero_of_le (nat_degree_le_nat_degree $ le_of_lt hfg) },
  have hgf := hfg, rw div_by_monic_eq_zero_iff hg hg.ne_zero at hgf, push_neg at hgf,
  have := degree_add_div_by_monic hg hgf,
  have hf : f ≠ 0, { intro hf, apply hfg, rw [hf, zero_div_by_monic] },
  rw [degree_eq_nat_degree hf, degree_eq_nat_degree hg.ne_zero, degree_eq_nat_degree hfg,
      ← with_bot.coe_add, with_bot.coe_eq_coe] at this,
  rw [← this, nat.add_sub_cancel_left]
end

lemma div_mod_by_monic_unique {f g} (q r : polynomial R) (hg : monic g)
  (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ g = r :=
if hg0 : g = 0 then by split; exact (subsingleton_of_monic_zero
  (hg0 ▸ hg : monic (0 : polynomial R))).1 _ _
else
  have h₁ : r - f %ₘ g = -g * (q - f /ₘ g),
    from eq_of_sub_eq_zero
      (by rw [← sub_eq_zero_of_eq (h.1.trans (mod_by_monic_add_div f hg).symm)];
        simp [mul_add, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]),
  have h₂ : degree (r - f %ₘ g) = degree (g * (q - f /ₘ g)),
    by simp [h₁],
  have h₄ : degree (r - f %ₘ g) < degree g,
    from calc degree (r - f %ₘ g) ≤ max (degree r) (degree (-(f %ₘ g))) :
      degree_add_le _ _
    ... < degree g : max_lt_iff.2 ⟨h.2, by rw degree_neg; exact degree_mod_by_monic_lt _ hg hg0⟩,
  have h₅ : q - (f /ₘ g) = 0,
    from by_contradiction
      (λ hqf, not_le_of_gt h₄ $
        calc degree g ≤ degree g + degree (q - f /ₘ g) :
          by erw [degree_eq_nat_degree hg0, degree_eq_nat_degree hqf,
              with_bot.coe_le_coe];
            exact nat.le_add_right _ _
        ... = degree (r - f %ₘ g) :
          by rw [h₂, degree_mul']; simpa [monic.def.1 hg]),
  ⟨eq.symm $ eq_of_sub_eq_zero h₅,
    eq.symm $ eq_of_sub_eq_zero $ by simpa [h₅] using h₁⟩

lemma map_mod_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f ∧ (p %ₘ q).map f = p.map f %ₘ q.map f :=
if h01 : (0 : S) = 1 then by haveI := subsingleton_of_zero_eq_one h01;
  exact ⟨subsingleton.elim _ _, subsingleton.elim _ _⟩
else
have h01R : (0 : R) ≠ 1, from mt (congr_arg f)
  (by rwa [is_semiring_hom.map_one f, is_semiring_hom.map_zero f]),
have map f p /ₘ map f q = map f (p /ₘ q) ∧ map f p %ₘ map f q = map f (p %ₘ q),
  from (div_mod_by_monic_unique ((p /ₘ q).map f) _ (monic_map f hq)
    ⟨eq.symm $ by rw [← map_mul, ← map_add, mod_by_monic_add_div _ hq],
    calc _ ≤ degree (p %ₘ q) : degree_map_le _
    ... < degree q : degree_mod_by_monic_lt _ hq
      $ (ne_zero_of_monic_of_zero_ne_one hq h01R)
    ... = _ : eq.symm $ degree_map_eq_of_leading_coeff_ne_zero _
      (by rw [monic.def.1 hq, is_semiring_hom.map_one f]; exact ne.symm h01)⟩),
⟨this.1.symm, this.2.symm⟩

lemma map_div_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p /ₘ q).map f = p.map f /ₘ q.map f :=
(map_mod_div_by_monic f hq).1

lemma map_mod_by_monic [comm_ring S] (f : R →+* S) (hq : monic q) :
  (p %ₘ q).map f = p.map f %ₘ q.map f :=
(map_mod_div_by_monic f hq).2

lemma dvd_iff_mod_by_monic_eq_zero (hq : monic q) : p %ₘ q = 0 ↔ q ∣ p :=
⟨λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _,
λ h, if hq0 : q = 0 then by rw hq0 at hq;
  exact (subsingleton_of_monic_zero hq).1 _ _
  else
  let ⟨r, hr⟩ := exists_eq_mul_right_of_dvd h in
  by_contradiction (λ hpq0,
  have hmod : p %ₘ q = q * (r - p /ₘ q) :=
    by rw [mod_by_monic_eq_sub_mul_div _ hq, mul_sub, ← hr],
  have degree (q * (r - p /ₘ q)) < degree q :=
    hmod ▸ degree_mod_by_monic_lt _ hq hq0,
  have hrpq0 : leading_coeff (r - p /ₘ q) ≠ 0 :=
    λ h, hpq0 $ leading_coeff_eq_zero.1
      (by rw [hmod, leading_coeff_eq_zero.1 h, mul_zero, leading_coeff_zero]),
  have hlc : leading_coeff q * leading_coeff (r - p /ₘ q) ≠ 0 :=
    by rwa [monic.def.1 hq, one_mul],
  by rw [degree_mul' hlc, degree_eq_nat_degree hq0,
      degree_eq_nat_degree (mt leading_coeff_eq_zero.2 hrpq0)] at this;
    exact not_lt_of_ge (nat.le_add_right _ _) (with_bot.some_lt_some.1 this))⟩

@[simp] lemma mod_by_monic_one (p : polynomial R) : p %ₘ 1 = 0 :=
(dvd_iff_mod_by_monic_eq_zero (by convert monic_one)).2 (one_dvd _)

@[simp] lemma div_by_monic_one (p : polynomial R) : p /ₘ 1 = p :=
by conv_rhs { rw [← mod_by_monic_add_div p monic_one] }; simp


@[simp] lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial R) (a : R) :
  p %ₘ (X - C a) = C (p.eval a) :=
if h0 : (0 : R) = 1 then by letI := subsingleton_of_zero_eq_one h0; exact subsingleton.elim _ _
else
by haveI : nontrivial R := nontrivial_of_ne 0 1 h0; exact
have h : (p %ₘ (X - C a)).eval a = p.eval a :=
  by rw [mod_by_monic_eq_sub_mul_div _ (monic_X_sub_C a), eval_sub, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero],
have degree (p %ₘ (X - C a)) < 1 :=
  degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a) ((degree_X_sub_C a).symm ▸
    ne_zero_of_monic (monic_X_sub_C _)),
have degree (p %ₘ (X - C a)) ≤ 0 :=
  begin
    cases (degree (p %ₘ (X - C a))),
    { exact bot_le },
    { exact with_bot.some_le_some.2 (nat.le_of_lt_succ (with_bot.some_lt_some.1 this)) }
  end,
begin
  rw [eq_C_of_degree_le_zero this, eval_C] at h,
  rw [eq_C_of_degree_le_zero this, h]
end

lemma mul_div_by_monic_eq_iff_is_root : (X - C a) * (p /ₘ (X - C a)) = p ↔ is_root p a :=
⟨λ h, by rw [← h, is_root.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0,
  by conv {to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

lemma dvd_iff_is_root : (X - C a) ∣ p ↔ is_root p a :=
⟨λ h, by rwa [← dvd_iff_mod_by_monic_eq_zero (monic_X_sub_C _),
    mod_by_monic_X_sub_C_eq_C_eval, ← C_0, C_inj] at h,
  λ h, ⟨(p /ₘ (X - C a)), by rw mul_div_by_monic_eq_iff_is_root.2 h⟩⟩

lemma mod_by_monic_X (p : polynomial R) : p %ₘ X = C (p.eval 0) :=
by rw [← mod_by_monic_X_sub_C_eq_C_eval, C_0, sub_zero]

section multiplicity
/-- An algorithm for deciding polynomial divisibility.
The algorithm is "compute `p %ₘ q` and compare to `0`". `
See `polynomial.mod_by_monic` for the algorithm that computes `%ₘ`.
 -/
def decidable_dvd_monic (p : polynomial R) (hq : monic q) : decidable (q ∣ p) :=
decidable_of_iff (p %ₘ q = 0) (dvd_iff_mod_by_monic_eq_zero hq)

open_locale classical

lemma multiplicity_X_sub_C_finite (a : R) (h0 : p ≠ 0) :
  multiplicity.finite (X - C a) p :=
multiplicity_finite_of_degree_pos_of_monic
  (have (0 : R) ≠ 1, from (λ h, by haveI := subsingleton_of_zero_eq_one h;
      exact h0 (subsingleton.elim _ _)),
    by haveI : nontrivial R := ⟨⟨0, 1, this⟩⟩; rw degree_X_sub_C; exact dec_trivial)
    (monic_X_sub_C _) h0
/-- The largest power of `X - C a` which divides `p`.
This is computable via the divisibility algorithm `decidable_dvd_monic`. -/
def root_multiplicity (a : R) (p : polynomial R) : ℕ :=
if h0 : p = 0 then 0
else let I : decidable_pred (λ n : ℕ, ¬(X - C a) ^ (n + 1) ∣ p) :=
  λ n, @not.decidable _ (decidable_dvd_monic p (monic_pow (monic_X_sub_C a) (n + 1))) in
by exactI nat.find (multiplicity_X_sub_C_finite a h0)

lemma root_multiplicity_eq_multiplicity (p : polynomial R) (a : R) :
  root_multiplicity a p = if h0 : p = 0 then 0 else
  (multiplicity (X - C a) p).get (multiplicity_X_sub_C_finite a h0) :=
by simp [multiplicity, root_multiplicity, roption.dom];
  congr; funext; congr

lemma pow_root_multiplicity_dvd (p : polynomial R) (a : R) :
  (X - C a) ^ root_multiplicity a p ∣ p :=
if h : p = 0 then by simp [h]
else by rw [root_multiplicity_eq_multiplicity, dif_neg h];
  exact multiplicity.pow_multiplicity_dvd _

lemma div_by_monic_mul_pow_root_multiplicity_eq
  (p : polynomial R) (a : R) :
  p /ₘ ((X - C a) ^ root_multiplicity a p) *
  (X - C a) ^ root_multiplicity a p = p :=
have monic ((X - C a) ^ root_multiplicity a p),
  from monic_pow (monic_X_sub_C _) _,
by conv_rhs { rw [← mod_by_monic_add_div p this,
    (dvd_iff_mod_by_monic_eq_zero this).2 (pow_root_multiplicity_dvd _ _)] };
  simp [mul_comm]

lemma eval_div_by_monic_pow_root_multiplicity_ne_zero
  {p : polynomial R} (a : R) (hp : p ≠ 0) :
  (p /ₘ ((X - C a) ^ root_multiplicity a p)).eval a ≠ 0 :=
begin
  haveI : nontrivial R := nonzero.of_polynomial_ne hp,
  rw [ne.def, ← is_root.def, ← dvd_iff_is_root],
  rintros ⟨q, hq⟩,
  have := div_by_monic_mul_pow_root_multiplicity_eq p a,
  rw [mul_comm, hq, ← mul_assoc, ← pow_succ',
    root_multiplicity_eq_multiplicity, dif_neg hp] at this,
  exact multiplicity.is_greatest'
    (multiplicity_finite_of_degree_pos_of_monic
    (show (0 : with_bot ℕ) < degree (X - C a),
      by rw degree_X_sub_C; exact dec_trivial) (monic_X_sub_C _) hp)
    (nat.lt_succ_self _) (dvd_of_mul_right_eq _ this)
end

end multiplicity
end comm_ring

end polynomial
