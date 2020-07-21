import linear_algebra.finite_dimensional
import order.zorn
import ring_theory.algebraic
import ring_theory.fractional_ideal
import ring_theory.coprime
import ring_theory.integral_closure
import ring_theory.localization
import ring_theory.noetherian
import set_theory.cardinal
import tactic

lemma mul_mem_non_zero_divisors {R} [comm_ring R] {a b : R} :
  a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
begin
  split,
  { intro h,
    split; intros x h'; apply h,
    { rw [←mul_assoc, h', zero_mul] },
    { rw [mul_comm a b, ←mul_assoc, h', zero_mul] } },
  { rintros ⟨ha, hb⟩ x hx,
    apply ha,
    apply hb,
    rw [mul_assoc, hx] },
end

/-- A ring `R` is (at most) one-dimensional if all nonzero prime ideals are maximal. -/
def ring.is_one_dimensional (R : Type*) [comm_ring R] :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ring

lemma principal_ideal_ring.is_one_dimensional (R : Type*) [integral_domain R]
  [is_principal_ideal_ring R] :
  ring.is_one_dimensional R :=
λ p nonzero prime, by { haveI := prime, exact ideal.is_prime.to_maximal_ideal nonzero }

variables {R K : Type*}

-- TODO: `class is_dedekind_domain`?
structure is_dedekind_domain [comm_ring R] [comm_ring K] (f : fraction_map R K) :=
(is_one_dimensional : is_one_dimensional R)
(is_noetherian_ring : is_noetherian_ring R)
(is_integrally_closed : integral_closure R f.codomain = ⊥)

lemma integrally_closed_iff_integral_implies_integer
  [comm_ring R] [comm_ring K] {f : fraction_map R K} :
  integral_closure R f.codomain = ⊥ ↔ ∀ x : f.codomain, is_integral R x → f.is_integer x :=
subalgebra.ext_iff.trans
  ⟨ λ h x hx, algebra.mem_bot.mp ((h x).mp hx),
    λ h x, iff.trans
      ⟨λ hx, h x hx, λ ⟨y, hy⟩, hy ▸ is_integral_algebra_map⟩
      (@algebra.mem_bot R f.codomain _ _ _ _).symm⟩

section scale_roots

open finsupp polynomial

variables [comm_ring R]

lemma coeff_nat_degree_eq_zero_iff {f : polynomial R} : f.coeff f.nat_degree = 0 ↔ f = 0 :=
begin
  split; intro hf,
  { refine polynomial.degree_eq_bot.mp _,
    rw [polynomial.nat_degree] at hf,
    cases i_def : f.degree with i,
    { exact rfl },
    rw [polynomial.degree, ←finset.max_eq_sup_with_bot] at i_def hf,
    have := finsupp.mem_support_iff.mp (finset.mem_of_max i_def),
    rw [i_def, option.get_or_else_some] at hf,
    contradiction },
  { rw [hf, polynomial.coeff_zero] }
end

lemma nat_degree_mem_support {f : polynomial R} (hf : f ≠ 0) : f.nat_degree ∈ f.support :=
finsupp.mem_support_iff.mpr (mt coeff_nat_degree_eq_zero_iff.mp hf)

/-- If `f : polynomial R` has a root `r`, then `scale_roots f s` is a polynomial with root `r * s`. -/
noncomputable def scale_roots (p : polynomial R) (s : R) : polynomial R :=
on_finset p.support
  (λ i, coeff p i * s ^ (p.nat_degree - i))
  (λ i h, mem_support_iff.mpr (ne_zero_of_mul_ne_zero_right h))

@[simp] lemma coeff_scale_roots (p : polynomial R) (s : R) (i : ℕ) :
  (scale_roots p s).coeff i = coeff p i * s ^ (p.nat_degree - i) :=
rfl

lemma coeff_scale_roots_nat_degree (p : polynomial R) (s : R) :
  (scale_roots p s).coeff p.nat_degree = p.leading_coeff :=
by rw [leading_coeff, coeff_scale_roots, nat.sub_self, pow_zero, mul_one]

@[simp] lemma zero_scale_roots (s : R) : scale_roots 0 s = 0 := by { ext, simp }

lemma scale_roots_ne_zero {p : polynomial R} (hp : p ≠ 0) (s : R) :
  scale_roots p s ≠ 0 :=
begin
  intro h,
  have : p.coeff p.nat_degree ≠ 0 := mt coeff_nat_degree_eq_zero_iff.mp hp,
  have : (scale_roots p s).coeff p.nat_degree = 0 :=
    congr_fun (congr_arg (coeff : polynomial R → ℕ → R) h) p.nat_degree,
  rw [coeff_scale_roots_nat_degree] at this,
  contradiction
end

lemma support_scale_roots_le (p : polynomial R) (s : R) :
(scale_roots p s).support ≤ p.support :=
begin
  intros i,
  simp only [mem_support_iff, scale_roots, on_finset_apply],
  exact ne_zero_of_mul_ne_zero_right
end

lemma support_scale_roots_eq (p : polynomial R) {s : R} (hs : s ∈ non_zero_divisors R) :
  (scale_roots p s).support = p.support :=
le_antisymm (support_scale_roots_le p s)
  begin
    intro i,
    simp only [mem_support_iff, scale_roots, on_finset_apply],
    intros p_ne_zero ps_zero,
    have := ((non_zero_divisors R).pow_mem hs (p.nat_degree - i)) _ ps_zero,
    contradiction
  end

@[simp] lemma degree_scale_roots (p : polynomial R) {s : R} :
  degree (scale_roots p s) = degree p :=
begin
  haveI := classical.prop_decidable,
  by_cases hp : p = 0,
  { rw [hp, zero_scale_roots] },
  have := scale_roots_ne_zero hp s,
  refine le_antisymm (finset.sup_mono (support_scale_roots_le p s)) (degree_le_degree _),
  rw coeff_scale_roots_nat_degree,
  intro h,
  have := leading_coeff_eq_zero.mp h,
  contradiction,
end

@[simp] lemma nat_degree_scale_roots (p : polynomial R) {s : R} :
  nat_degree (scale_roots p s) = nat_degree p :=
by simp only [nat_degree, degree_scale_roots]

lemma monic_scale_roots_iff {p : polynomial R} {s : R} :
  monic (scale_roots p s) ↔ monic p :=
by simp [monic, leading_coeff]

variables {S : Type*} [comm_ring S]

lemma scale_roots_eval₂_eq_zero {p : polynomial S} (f : S →+* R)
  {r : R} {s : S} (hr : eval₂ f r p = 0) (hs : s ∈ non_zero_divisors S) :
  eval₂ f (f s * r) (scale_roots p s) = 0 :=
calc (scale_roots p s).support.sum (λ i, f (coeff p i * s ^ (p.nat_degree - i)) * (f s * r) ^ i)
    = p.support.sum (λ (i : ℕ), f (p.coeff i) * f s ^ (p.nat_degree - i + i) * r ^ i) :
  finset.sum_congr (support_scale_roots_eq p hs)
    (λ i hi, by simp_rw [f.map_mul, f.map_pow, pow_add, mul_pow, mul_assoc])
... = p.support.sum (λ (i : ℕ), f s ^ p.nat_degree * (f (p.coeff i) * r ^ i)) :
  finset.sum_congr rfl
  (λ i hi, by { rw [mul_assoc, mul_left_comm, nat.sub_add_cancel],
                exact le_nat_degree_of_ne_zero (mem_support_iff.mp hi) })
... = f s ^ p.nat_degree * eval₂ f r p : finset.mul_sum.symm
... = 0 : by rw [hr, _root_.mul_zero]

lemma scale_roots_aeval_eq_zero [algebra S R] {p : polynomial S}
  {r : R} {s : S} (hr : aeval S R r p = 0) (hs : s ∈ non_zero_divisors S) :
  aeval S R (algebra_map S R s * r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero (algebra_map S R) hr hs

lemma scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero {R} [integral_domain R] [field K]
  {p : polynomial R} {f : R →+* K} (hf : function.injective f)
  {r s : R} (hr : eval₂ f (f r / f s) p = 0) (hs : s ∈ non_zero_divisors R) :
  eval₂ f (f r) (scale_roots p s) = 0 :=
begin
  convert scale_roots_eval₂_eq_zero f hr hs,
  rw [←mul_div_assoc, mul_comm, mul_div_cancel],
  exact @map_ne_zero_of_mem_non_zero_divisors _ _ _ _ _ hf ⟨s, hs⟩
end

lemma scale_roots_aeval_eq_zero_of_aeval_div_eq_zero {R} [integral_domain R] [field K] [algebra R K]
  (inj : function.injective (algebra_map R K)) {p : polynomial R} {r s : R}
  (hr : aeval R K (algebra_map R K r / algebra_map R K s) p = 0) (hs : s ∈ non_zero_divisors R) :
  aeval R K (algebra_map R K r) (scale_roots p s) = 0 :=
scale_roots_eval₂_eq_zero_of_eval₂_div_eq_zero inj hr hs

lemma is_root_of_eval₂_map_eq_zero [comm_ring S] {p : polynomial R} {f : R →+* S}
  (hf : function.injective f) {r : R} : eval₂ f (f r) p = 0 → p.is_root r :=
show eval₂ (f ∘ ring_hom.id R) (f r) p = 0 → eval₂ id r p = 0, begin
  intro h,
  rw [←hom_eval₂, ←f.map_zero] at h,
  exact hf h
end

lemma is_root_of_aeval_algebra_map_eq_zero [algebra R S] {p : polynomial R}
  (inj : function.injective (algebra_map R S))
  {r : R} (hr : polynomial.aeval R S (algebra_map R S r) p = 0) : p.is_root r :=
is_root_of_eval₂_map_eq_zero inj hr

end scale_roots

lemma prime.dvd_of_dvd_pow {a p : R} [comm_semiring R] (hp : prime p) {n : ℕ} (h : p ∣ a^n) : p ∣ a :=
begin
  induction n with n ih,
  { rw pow_zero at h,
    have := is_unit_of_dvd_one _ h,
    have := hp.not_unit,
    contradiction },
  { rw pow_succ at h,
    cases hp.div_or_div h,
    { assumption },
    { apply ih,
      assumption } }
end

namespace unique_factorization_domain

variables [integral_domain R] [unique_factorization_domain R] [field K] {f : fraction_map R K}

lemma is_unit.mul_right_dvd_of_dvd {a b c : R} (hb : is_unit b) (h : a ∣ c) : a * b ∣ c :=
begin
  rcases hb with ⟨b, rfl⟩,
  rcases h with ⟨c', rfl⟩,
  use (b⁻¹ : units R) * c',
  rw [mul_assoc, units.mul_inv_cancel_left]
end

lemma is_unit.mul_left_dvd_of_dvd {a b c : R} (hb : is_unit b) (h : a ∣ c) : b * a ∣ c :=
begin
  rcases hb with ⟨b, rfl⟩,
  rcases h with ⟨c', rfl⟩,
  use (b⁻¹ : units R) * c',
  rw [mul_comm (b : R) a, mul_assoc, units.mul_inv_cancel_left]
end

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
lemma irreducible.dvd_symm {p q : R} (hp : irreducible p) (hq : irreducible q) :
  p ∣ q → q ∣ p :=
begin
  tactic.unfreeze_local_instances,
  rintros ⟨q', rfl⟩,
  cases of_irreducible_mul hq with h h,
  { have := hp.not_unit,
    contradiction },
  { exact is_unit.mul_right_dvd_of_dvd h (dvd_refl p) }
end

lemma left_dvd_or_dvd_right_of_dvd_prime_mul {a : R} :
  ∀ {b p : R}, prime p → (a ∣ p * b) → p ∣ a ∨ a ∣ b :=
begin
  refine induction_on_prime a _ _ _,
  { intros b p _ ha,
    refine (eq_zero_or_eq_zero_of_mul_eq_zero (zero_dvd_iff.mp ha)).imp _ _;
      rintro ⟨rfl⟩; refl },
  { intros x x_is_unit b _ _ _,
    exact or.inr (is_unit_iff_forall_dvd.mp x_is_unit b) },
  { intros a q a_ne_zero hq ih b p hp qa_dvd,
    cases (hq.div_or_div (dvd_of_mul_right_dvd qa_dvd)) with q_dvd_p q_dvd_b,
    { left,
      apply dvd_mul_of_dvd_left,
      refine irreducible.dvd_symm (irreducible_of_prime _) (irreducible_of_prime _) _;
        assumption },
    { rcases q_dvd_b with ⟨b', rfl⟩,
      rw mul_left_comm at qa_dvd,
      refine (ih hp ((mul_dvd_mul_iff_left hq.ne_zero).mp qa_dvd)).imp _ _,
      { exact λ h, dvd_mul_of_dvd_right h _ },
      { exact mul_dvd_mul_left q } } }
end

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {p}, p ∣ a' → p ∣ b' → is_unit p) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases left_dvd_or_dvd_right_of_dvd_prime_mul p_prime q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (dvd_trans p_dvd_q q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b'  } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {p}, p ∣ a' → p ∣ b' → is_unit p) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

lemma mul_mem_non_zero_divisors {a b : R} :
  a * b ∈ non_zero_divisors R ↔ a ∈ non_zero_divisors R ∧ b ∈ non_zero_divisors R :=
begin
split,
intro h, split,
      intros x ha,
      have hab : x*(a*b)=0,
        calc x*(a*b) = (x*a)*b : by ring
         ... = 0*b : by rw ha
        ...  = 0 : by ring,
apply h, exact hab,
      intros x hb,
      have hab : x*(a*b)=0,
        calc x*(a*b) = (x*b)*a : by ring
         ... = 0*a : by rw hb
        ...  = 0 : by ring,
apply h, exact hab,
intro h,cases h with ha hb, intros x hx,
have hab: a*b*x=0, rw [mul_comm], exact hx,
apply ha,
have hba: b*x*a=0, rw [mul_comm,← mul_assoc], exact hab,
apply hb, rw [mul_assoc,hx],
end

lemma exists_reduced_fraction (x : f.codomain) :
  ∃ (a : R) (b : non_zero_divisors R),
  (∀ {p}, p ∣ a → p ∣ b → is_unit p) ∧
  f.to_map a / f.to_map b = x :=
begin
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := f.exists_integer_multiple x,
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ := exists_reduced_factors' a b
    (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero),
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  refine ⟨a', ⟨b', b'_nonzero⟩, @no_factor, eq.symm ((eq_div_iff _).mpr _)⟩,
  { exact f.map_ne_zero_of_mem_non_zero_divisors ⟨b', b'_nonzero⟩ },
  { rw mul_comm x,
    apply mul_left_cancel' (f.map_ne_zero_of_mem_non_zero_divisors ⟨c', c'_nonzero⟩),
    simp only [subtype.coe_mk, f.to_map.map_mul] at *,
    rw [←mul_assoc, hab] },
end

lemma dvd_term_of_is_root_of_dvd_coeff {r p : R} {f : polynomial R} (i : ℕ)
  (hf : f ≠ 0) (hr : f.is_root r) (h : ∀ (j ≠ i), p ∣ f.coeff j) : p ∣ f.coeff i * r ^ i :=
begin
  by_cases hi : i ∈ f.support,
  { unfold polynomial.is_root at hr,
    have : p ∣ f.eval r := hr.symm ▸ dvd_zero p,
    unfold polynomial.eval polynomial.eval₂ finsupp.sum id at this,
    rw [←finset.insert_erase hi, finset.sum_insert (finset.not_mem_erase _ _)] at this,
    refine (dvd_add_left (finset.dvd_sum _)).mp this,
    intros j hj,
    exact dvd_mul_of_dvd_left (h j (finset.ne_of_mem_erase hj)) _ },
  { convert dvd_zero p,
    convert _root_.zero_mul _,
    exact finsupp.not_mem_support_iff.mp hi }
end

lemma prime_dvd_root_of_monic_of_dvd_coeff {r p : R} (hp : prime p) {f : polynomial R}
  (hf : f.monic) (hr : f.is_root r) (h : ∀ i ≠ f.nat_degree, p ∣ f.coeff i) : p ∣ r :=
begin
  have := dvd_term_of_is_root_of_dvd_coeff f.nat_degree hf.ne_zero hr h,
  rw [←polynomial.leading_coeff, hf.leading_coeff, one_mul] at this,
  exact hp.dvd_of_dvd_pow this
end

lemma integrally_closed : integral_closure R f.codomain = ⊥ :=
begin
  apply integrally_closed_iff_integral_implies_integer.mpr,
  rintros x ⟨p, hp, px⟩,
  obtain ⟨a, ⟨b, b_nonzero⟩, no_factors, rfl⟩ := exists_reduced_fraction x,
  simp only [subtype.coe_mk] at *,
  suffices : is_unit b,
  { obtain ⟨⟨b, c, hbc, hcb⟩, rfl⟩ := this,
    simp only [units.coe_mk] at *,
    use c * a,
    refine (eq_div_iff _).mpr _,
    { exact f.map_ne_zero_of_mem_non_zero_divisors ⟨b, b_nonzero⟩ },
    rw [←f.to_map.map_mul, mul_assoc, mul_left_comm, hcb, mul_one] },
  apply is_unit_of_no_prime_factor,
  { exact mem_non_zero_divisors_iff_ne_zero.mp b_nonzero },
  intros q q_prime q_dvd_b,
  refine q_prime.not_unit (no_factors _ q_dvd_b),
  have alg_inj : function.injective (algebra_map R f.codomain) := f.injective,
  apply prime_dvd_root_of_monic_of_dvd_coeff q_prime (monic_scale_roots_iff.mpr hp),
  { apply is_root_of_aeval_algebra_map_eq_zero alg_inj,
    apply scale_roots_aeval_eq_zero_of_aeval_div_eq_zero; assumption },
  { intros i hi,
    rw nat_degree_scale_roots at hi,
    rw coeff_scale_roots,
    by_cases h : p.nat_degree < i,
    { rw [polynomial.coeff_eq_zero_of_nat_degree_lt h, _root_.zero_mul],
      exact dvd_zero q },
    { refine dvd_mul_of_dvd_right (dvd_trans q_dvd_b _) _,
      convert pow_dvd_pow b _,
      { exact (pow_one b).symm },
      { refine nat.succ_le_of_lt (nat.lt_sub_left_of_add_lt _),
        rw add_zero,
        exact lt_of_le_of_ne (le_of_not_gt h) hi } } },
end

end unique_factorization_domain

-- TODO: instance instead of def?
def principal_ideal_ring.to_dedekind_domain [integral_domain R] [is_principal_ideal_ring R]
  [field K] (f : fraction_map R K) :
  is_dedekind_domain f :=
{ is_one_dimensional := principal_ideal_ring.is_one_dimensional R,
  is_noetherian_ring := principal_ideal_ring.is_noetherian_ring,
  is_integrally_closed := @unique_factorization_domain.integrally_closed R _ _
    (principal_ideal_ring.to_unique_factorization_domain) _ _}

namespace dedekind_domain

variables {S : Type*} [integral_domain R] [integral_domain S] [algebra R S]
variables {L : Type*} [field K] [field L] {f : fraction_map R K}

open finsupp polynomial

instance : integral_domain (integral_closure R S) :=
{ zero_ne_one := mt subtype.ext.mp zero_ne_one,
  eq_zero_or_eq_zero_of_mul_eq_zero := λ ⟨a, ha⟩ ⟨b, hb⟩ h,
    or.imp subtype.ext.mpr subtype.ext.mpr (eq_zero_or_eq_zero_of_mul_eq_zero (subtype.ext.mp h)),
  ..(integral_closure R S).comm_ring R S }

lemma maximal_ideal_invertible_of_dedekind (h : is_dedekind_domain f) {M : ideal R}
(hM : ideal.is_maximal M) : is_unit (M : fractional_ideal f) :=
sorry

lemma fractional_ideal_invertible_of_dedekind (h : is_dedekind_domain f) (I : fractional_ideal f) :
I * I⁻¹ = 1 :=
begin
sorry
end

/-- If `f : polynomial R` is a polynomial with root `z`, `to_monic f` is
a monic polynomial with root `leading_coeff f * z` -/
noncomputable def to_monic {f : polynomial R} (hf : f ≠ 0) : polynomial R :=
on_finset f.support
  (λ i, if i = f.nat_degree then 1 else coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i))
  begin
    intros i h,
    apply mem_support_iff.mpr,
    split_ifs at h with hi,
    { rw hi,
      exact mt polynomial.leading_coeff_eq_zero.mp hf },
    { exact ne_zero_of_mul_ne_zero_right h },
  end

@[simp] lemma to_monic_coeff_degree {f : polynomial R} (hf : f ≠ 0) :
  (to_monic hf).coeff f.nat_degree = 1 :=
if_pos rfl

@[simp] lemma to_monic_coeff_ne_degree {f : polynomial R} (hf : f ≠ 0)
  {i : ℕ} (hi : i ≠ f.nat_degree) :
  coeff (to_monic hf) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
if_neg hi

lemma monic_to_monic {f : polynomial R} (hf : f ≠ 0) : monic (to_monic hf) :=
begin
  apply monic_of_degree_le f.nat_degree,
  { refine finset.sup_le (λ i h, _),
    rw [to_monic, mem_support_iff, on_finset_apply] at h,
    split_ifs at h with hi,
    { rw hi,
      exact le_refl _ },
    { erw [with_bot.some_le_some],
      apply le_nat_degree_of_ne_zero,
      exact ne_zero_of_mul_ne_zero_right h } },
  { exact to_monic_coeff_degree hf }
end

@[simp] lemma support_to_monic {f : polynomial R} (hf : f ≠ 0) : (to_monic hf).support = f.support :=
begin
  ext i,
  simp only [to_monic, on_finset_apply, mem_support_iff],
  split_ifs with hi,
  { simp only [ne.def, not_false_iff, true_iff, one_ne_zero, hi],
    exact λ h, hf (leading_coeff_eq_zero.mp h) },
  split,
  { intro h,
    exact ne_zero_of_mul_ne_zero_right h },
  { intro h,
    refine mul_ne_zero h (pow_ne_zero _ _),
    exact λ h, hf (leading_coeff_eq_zero.mp h) }
end

lemma eq_C_of_nat_degree_le_zero {p : polynomial R} (h : nat_degree p ≤ 0) : p = C (coeff p 0) :=
begin
  refine polynomial.ext (λ n, _),
  cases n,
  { simp },
  { have : nat_degree p < nat.succ n := lt_of_le_of_lt h (nat.succ_pos _),
    rw [coeff_C, if_neg (nat.succ_ne_zero _), coeff_eq_zero_of_nat_degree_lt this] }
end

lemma nat_degree_pos_of_aeval_root {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval R S z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < f.nat_degree :=
lt_of_not_ge $ λ hlt, begin
  have := eq_C_of_nat_degree_le_zero hlt,
  rw [this, aeval_C] at hz,
  have : ∀ n, coeff f n = 0 := λ n, nat.cases_on n (inj _ hz)
    (λ _, coeff_eq_zero_of_nat_degree_lt (lt_of_le_of_lt hlt (nat.succ_pos _))),
  exact hf (finsupp.ext this),
end

lemma to_monic_aeval_eq_zero {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval R S z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  aeval R S (z * algebra_map R S f.leading_coeff) (to_monic hf) = 0 :=
calc aeval R S (z * algebra_map R S f.leading_coeff) (to_monic hf)
    = f.support.attach.sum
        (λ i, algebra_map R S (coeff (to_monic hf) i.1 * f.leading_coeff ^ i.1) * z ^ i.1) :
      by { rw [aeval_def, eval₂, finsupp.sum, support_to_monic],
           simp only [mul_comm z, mul_pow, mul_assoc, ring_hom.map_pow, ring_hom.map_mul],
           exact finset.sum_attach.symm }
... = f.support.attach.sum
        (λ i, algebra_map R S (coeff f i.1 * f.leading_coeff ^ (f.nat_degree - 1)) * z ^ i.1) :
      begin
        have one_le_deg : 1 ≤ f.nat_degree :=
          nat.succ_le_of_lt (nat_degree_pos_of_aeval_root hf hz inj),
        congr,
        ext i,
        congr' 2,
        by_cases hi : i.1 = f.nat_degree,
        { rw [hi, to_monic_coeff_degree, one_mul, leading_coeff, ←pow_succ,
              nat.sub_add_cancel one_le_deg] },
        { have : i.1 ≤ f.nat_degree - 1 := nat.le_pred_of_lt (lt_of_le_of_ne
            (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.mp i.2)) hi),
          rw [to_monic_coeff_ne_degree hf hi, mul_assoc, ←pow_add, nat.sub_add_cancel this] }
      end
... = algebra_map R S f.leading_coeff ^ (f.nat_degree - 1) * aeval R S z f :
      by { simp_rw [aeval_def, eval₂, finsupp.sum, λ i, mul_comm (coeff f i), ring_hom.map_mul,
                    ring_hom.map_pow, mul_assoc, ←finset.mul_sum],
           congr' 1,
           exact @finset.sum_attach _ _ f.support _ (λ i, algebra_map R S (f.coeff i) * z ^ i) }
... = 0 : by rw [hz, _root_.mul_zero]

lemma exists_integral_multiple (S_alg : algebra.is_algebraic R S) (z : S)
  (inj : ∀ x, algebra_map R S x = 0 → x = 0) :
  ∃ x : integral_closure R S × non_zero_divisors (integral_closure R S),
    z * x.2 = x.1 :=
begin
  obtain ⟨p, p_nonzero, px⟩ := S_alg z,
  set n := p.nat_degree with n_def,
  set a := p.leading_coeff with a_def,
  have a_nonzero : a ≠ 0 := mt polynomial.leading_coeff_eq_zero.mp p_nonzero,
  have y_integral : is_integral R (algebra_map R S a) := is_integral_algebra_map,
  have x_integral : is_integral R (z * algebra_map R S a) :=
  ⟨ to_monic p_nonzero, monic_to_monic p_nonzero, to_monic_aeval_eq_zero p_nonzero px inj ⟩,
  refine ⟨⟨⟨_, x_integral⟩, ⟨⟨_, y_integral⟩, _⟩⟩, rfl⟩,
  exact mem_non_zero_divisors_iff_ne_zero.mpr (λ h, a_nonzero (inj _ (subtype.ext.mp h)))
end

/-- If the field `L` is an algebraic extension of `R`,
  the integral closure of `R` in `L` has fraction field `L`. -/
def integral_closure.fraction_map [algebra R L] (L_alg : algebra.is_algebraic R L)
  (inj : ∀ x, algebra_map R L x = 0 → x = 0) :
  fraction_map (integral_closure R L) L :=
(algebra_map (integral_closure R L) L).to_localization_map
  (λ ⟨⟨y, integral⟩, nonzero⟩,
    have y ≠ 0 := λ h, mem_non_zero_divisors_iff_ne_zero.mp nonzero (subtype.ext.mpr h),
    show is_unit y, from ⟨⟨y, y⁻¹, mul_inv_cancel this, inv_mul_cancel this⟩, rfl⟩)
  (λ z, exists_integral_multiple L_alg _ inj)
  (λ x y, ⟨ λ (h : x.1 = y.1), ⟨1, by simpa using subtype.ext.mpr h⟩,
  λ ⟨c, hc⟩, congr_arg (algebra_map _ L)
    (eq_of_mul_eq_mul_right_of_ne_zero (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc) ⟩)

lemma extension_is_algebraic_of_finite [algebra K L] (finite : finite_dimensional K L) :
  algebra.is_algebraic K L :=
λ x, (is_algebraic_iff_is_integral _).mpr (is_integral_of_noetherian ⊤
  (is_noetherian_of_submodule_of_noetherian _ _ _ finite) x algebra.mem_top)

open_locale classical

/-- `coeff_to_base_ring p` gives the coefficients of the polynomial `to_base_ring p` -/
noncomputable def coeff_to_base_ring (p : polynomial f.codomain) (i : ℕ) : R :=
if hi : i ∈ p.support
then classical.some (classical.some_spec
      (f.exist_integer_multiples_of_finset (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩))
else 0

lemma coeff_to_base_ring_mem_support (p : polynomial f.codomain) (i : ℕ)
  (h : coeff_to_base_ring p i ≠ 0) : i ∈ p.support :=
begin
  contrapose h,
  rw [ne.def, not_not, coeff_to_base_ring, dif_neg h]
end

/-- `to_base_ring g` clears the denominators of the given polynomial -/
noncomputable def to_base_ring : polynomial f.codomain → polynomial R :=
λ p, on_finset p.support (coeff_to_base_ring p) (coeff_to_base_ring_mem_support p)

@[simp]
lemma to_base_ring_coeff (p : polynomial f.codomain) (i : ℕ) :
  (to_base_ring p).coeff i = coeff_to_base_ring p i := rfl

lemma to_base_ring_spec (p : polynomial f.codomain) :
  ∃ (b : non_zero_divisors R), ∀ i, f.to_map ((to_base_ring p).coeff i) = f.to_map b * p.coeff i :=
begin
  use classical.some (f.exist_integer_multiples_of_finset (p.support.image p.coeff)),
  intro i,
  rw [to_base_ring_coeff, coeff_to_base_ring],
  split_ifs with hi,
  { exact classical.some_spec (classical.some_spec
      (f.exist_integer_multiples_of_finset (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩)) },
  { convert (_root_.mul_zero (f.to_map _)).symm,
    { exact f.to_ring_hom.map_zero },
    { exact finsupp.not_mem_support_iff.mp hi } }
end

lemma to_base_ring_map_to_map (p : polynomial f.codomain) : ∃ (b : non_zero_divisors R),
  (to_base_ring p).map f.to_map = f.to_map b • p :=
let ⟨b, hb⟩ := to_base_ring_spec p in ⟨b, polynomial.ext (λ i, by { rw coeff_map, exact hb i })⟩

lemma to_base_ring_eq_zero_iff {p : polynomial f.codomain} : to_base_ring p = 0 ↔ p = 0 :=
begin
  refine (polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm),
  obtain ⟨⟨b, nonzero⟩, hb⟩ := to_base_ring_spec p,
  split; intros h i,
  { apply f.to_map_eq_zero_iff.mpr,
    rw [hb i, h i],
    exact _root_.mul_zero _ },
  { have hi := h i,
    rw [coeff_zero, f.to_map_eq_zero_iff, hb i] at hi,
    apply or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi),
    intro h,
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero,
    exact f.to_map_eq_zero_iff.mpr h }
end

lemma eval₂_smul {S : Type*} [comm_ring S] (g : R →+* S) (p : polynomial R) (x : S) {s : R} :
  eval₂ g x (s • p) = g s * eval₂ g x p :=
begin
  by_cases s = 0,
  { simp [h] },
  simp_rw [eval₂, finsupp.sum, finset.mul_sum],
  apply finset.sum_congr,
  { ext i,
    simp [mem_support_iff, h] },
  intros i hi,
  simp [mul_assoc]
end

lemma to_base_ring_eval₂_eq_zero {S : Type*} [comm_ring S] (g : f.codomain →+* S) (p : polynomial f.codomain) {x : S}
  (hx : eval₂ g x p = 0) : eval₂ (g ∘ f.to_map) x (to_base_ring p) = 0 :=
let ⟨b, hb⟩ := to_base_ring_map_to_map p in
trans (eval₂_map _ _ _).symm (by rw [hb, eval₂_smul, hx, _root_.mul_zero])

lemma to_base_ring_aeval_root {S : Type*} [comm_ring S] [algebra f.codomain S] (p : polynomial f.codomain) {x : S}
  (hx : aeval _ _ x p = 0) : aeval _ (algebra.comap R f.codomain S) x (to_base_ring p) = 0 :=
to_base_ring_eval₂_eq_zero (algebra_map f.codomain S) p hx

lemma comap_is_algebraic_iff [algebra f.codomain L] :
  algebra.is_algebraic R (algebra.comap R f.codomain L) ↔ algebra.is_algebraic f.codomain L :=
begin
  split; intros h x; obtain ⟨p, hp, px⟩ := h x,
  { refine ⟨p.map f.to_map, λ h, hp (polynomial.ext (λ i, _)), _⟩,
    { have : f.to_map (p.coeff i) = 0 := by { rw [←coeff_map], simp [h] },
      exact f.to_map_eq_zero_iff.mpr this },
    { exact trans (eval₂_map _ _ _) px } },
  { use [to_base_ring p, mt to_base_ring_eq_zero_iff.mp hp],
    convert to_base_ring_aeval_root p px },
end

lemma fraction_map.extension_is_algebraic_of_finite [algebra f.codomain L]
  (finite : finite_dimensional f.codomain L) : algebra.is_algebraic R (algebra.comap R f.codomain L) :=
comap_is_algebraic_iff.mpr (extension_is_algebraic_of_finite finite)

/-- The fraction field of the integral closure in a finite extension is that extension. -/
def integral_closure.fraction_map_of_finite_extension [algebra f.codomain L]
  (finite : finite_dimensional f.codomain L) :
  fraction_map (integral_closure R (algebra.comap R f.codomain L)) (algebra.comap R f.codomain L) :=
integral_closure.fraction_map
  (fraction_map.extension_is_algebraic_of_finite finite)
  (λ x hx, f.to_map_eq_zero_iff.mpr ((algebra_map f.codomain L).map_eq_zero.mp hx))

/- If L is a finite extension of K, the integral closure of R in L is a Dedekind domain. -/
def closure_in_field_extension [algebra f.codomain L] (finite : finite_dimensional f.codomain L)
  (h : is_dedekind_domain f) : is_dedekind_domain (integral_closure.fraction_map_of_finite_extension finite) :=
{ is_noetherian_ring := sorry,
  is_one_dimensional := sorry,
  is_integrally_closed := sorry }

end dedekind_domain
