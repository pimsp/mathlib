/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure_space
import measure_theory.borel_space
import topology.opens
/-!
# Haar measure
-/
universe variables u v w
noncomputable theory

open topological_space set measurable_space has_inv

namespace nat

@[simp] lemma find_eq_zero {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  nat.find h = 0 ↔ p 0 :=
begin
  split,
  { intro h0, rw [← h0], apply nat.find_spec },
  { intro hp, apply nat.eq_zero_of_le_zero, exact nat.find_min' _ hp }
end

@[simp] lemma find_pos {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  0 < nat.find h ↔ ¬ p 0 :=
by rw [nat.pos_iff_ne_zero, not_iff_not, nat.find_eq_zero]

open_locale classical

/- redefine `Inf_nat_def` -/
protected lemma Inf_def {s : set ℕ} (h : s.nonempty) : Inf s = nat.find h :=
Inf_nat_def _

@[simp] lemma Inf_eq_zero {s : set ℕ} : Inf s = 0 ↔ 0 ∈ s ∨ s = ∅ :=
begin
  cases eq_empty_or_nonempty s,
  { subst h, simp only [or_true, eq_self_iff_true, iff_true, Inf, has_Inf.Inf,
      mem_empty_eq, exists_false, dif_neg, not_false_iff] },
  { have := ne_empty_iff_nonempty.mpr h,
    simp only [this, or_false, nat.Inf_def, h, nat.find_eq_zero] }
end

lemma Inf_spec {s : set ℕ} (h : s.nonempty) : Inf s ∈ s :=
by { rw [nat.Inf_def h], exact nat.find_spec h }

lemma not_mem_of_lt_Inf {s : set ℕ} {m : ℕ} (hm : m < Inf s) : m ∉ s :=
begin
  cases eq_empty_or_nonempty s,
  { subst h, apply not_mem_empty },
  { rw [nat.Inf_def h] at hm, exact nat.find_min h hm }
end

protected lemma Inf_le {s : set ℕ} {m : ℕ} (hm : m ∈ s) : Inf s ≤ m :=
by { rw [nat.Inf_def ⟨m, hm⟩], exact nat.find_min' ⟨m, hm⟩ hm }

end nat

@[simp] lemma bUnion_finset_image {α β γ} [decidable_eq α] {s : finset γ} {f : γ → α}
  {g : α → set β} : (⋃x ∈ s.image f, g x) = (⋃y ∈ s, g (f y)) :=
begin
  convert @bUnion_image _ _ _ (↑s) _ _, ext x y,
  simp only [mem_Union, exists_prop, ← finset.mem_coe, finset.coe_image]
end

@[simp] lemma bInter_finset_image {α β γ} [decidable_eq α] {s : finset γ} {f : γ → α}
  {g : α → set β} : (⋂ x ∈ s.image f, g x) = (⋂ y ∈ s, g (f y)) :=
begin
  convert @bInter_image _ _ _ (↑s) _ _, ext x y,
  simp only [mem_Inter, exists_prop, ← finset.mem_coe, finset.coe_image]
end

lemma mem_prop {α} {p : α → Prop} {x : α} : @has_mem.mem α (set α) _ x p ↔ p x := iff.rfl

lemma disjoint.preimage {α β} (f : α → β) {s t : set β} (h : disjoint s t) :
  disjoint (f ⁻¹' s) (f ⁻¹' t) :=
λ x hx, h hx

namespace set
variable {α : Type*}

/-- The pointwise product of two sets `s` and `t`:
  `st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }. -/
@[to_additive "The pointwise sum of two sets `s` and `t`: `s + t = { x + y | x ∈ s, y ∈ t }."]
protected def mul [has_mul α] (s t : set α) : set α :=
(λ p : α × α, p.1 * p.2) '' s.prod t

@[simp] lemma mem_mul [has_mul α] {s t : set α} {x : α} :
  x ∈ s.mul t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [set.mul, and.assoc, mem_image, mem_prod, prod.exists] }

/-- The pointwise inverse of a set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }. -/
@[to_additive "The pointwise additive inverse of a set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }"]
protected def inv [has_inv α] (s : set α) : set α :=
has_inv.inv '' s

@[simp] lemma mem_inv [has_inv α] {s : set α} {x : α} : x ∈ s.inv ↔ ∃ y, y ∈ s ∧ y⁻¹ = x :=
by { simp only [set.inv, mem_image] }

theorem disjoint_iff_inter_eq_empty {s t : set α} : disjoint s t ↔ s ∩ t = ∅ :=
disjoint_iff

end set

namespace finset
variables {α : Type*} [decidable_eq α]

/-- The pointwise product of two finite sets `s` and `t`:
  `st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[to_additive "The pointwise sum of two finite sets `s` and `t`:
  `s + t = { x + y | x ∈ s, y ∈ t }`."]
protected def mul  [has_mul α](s t : finset α) : finset α :=
(s.product t).image (λ p : α × α, p.1 * p.2)

@[simp] lemma mem_mul [has_mul α] {s t : finset α} {x : α} :
  x ∈ s.mul t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [finset.mul, and.assoc, mem_image, exists_prop, prod.exists, mem_product] }

/-- The pointwise inverse of a finite set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }. -/
@[to_additive "The pointwise additive inverse of a finite set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }"]
protected def inv [has_inv α] (s : finset α) : finset α :=
s.image has_inv.inv

@[simp] lemma mem_inv [has_inv α] {s : finset α} {x : α} :
  x ∈ s.inv ↔ ∃ y, y ∈ s ∧ y⁻¹ = x :=
by { simp only [finset.inv, mem_image, exists_prop] }

lemma card_union_eq {s t : finset α} (h : disjoint s t) : (s ∪ t).card = s.card + t.card :=
begin
  rw [← card_union_add_card_inter],
  convert (add_zero _).symm, rwa [card_eq_zero, ← disjoint_iff_inter_eq_empty]
end

lemma card_filter_add_card_filter_le {s : finset α} {p q : α → Prop} [decidable_pred p]
  [decidable_pred q] (h : ∀ x, x ∈ s → p x → ¬ q x) :
  (s.filter p).card + (s.filter q).card ≤ s.card :=
by { rw [← card_union_eq (disjoint_filter.mpr h), filter_union_right],
    exact card_le_of_subset (filter_subset _) }

end finset


namespace function

lemma injective.surjective_preimage {α β : Type*} {f : α → β} (hf : injective f) :
  surjective (preimage f) :=
by { intro s, use f '' s, rw preimage_image_eq _ hf }

lemma surjective.surjective_image {α β : Type*} {f : α → β} (hf : surjective f) :
  surjective (image f) :=
by { intro s, use f ⁻¹' s, rw image_preimage_eq hf }

lemma injective.injective_image {α β : Type*} {f : α → β} (hf : injective f) :
  injective (image f) :=
by { intros s t h, rw [←preimage_image_eq s hf, ←preimage_image_eq t hf, h] }

lemma injective.ne_iff {α β : Type*} {f : α → β} (hf : injective f) {x y : α} :
  f x ≠ f y ↔ x ≠ y :=
⟨mt $ congr_arg f, hf.ne⟩

lemma injective.nonempty {α β : Type*} {f : set α → set β} (hf : injective f)
  (h2 : f ∅ = ∅) {s : set α} : (f s).nonempty ↔ s.nonempty :=
by rw [← ne_empty_iff_nonempty, ← h2, ← ne_empty_iff_nonempty, hf.ne_iff]

end function
open function

lemma infi_congr {α β γ : Type*} {f : α → γ} {g : β → γ} [complete_lattice γ] (h : α → β)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y  :=
by { unfold infi, congr, convert h1.range_comp g, ext, rw ←h2 }

lemma supr_congr {α β γ : Type*} {f : α → γ} {g : β → γ} [complete_lattice γ] (h : α → β)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y  :=
by { unfold supr, congr, convert h1.range_comp g, ext, rw ←h2 }


@[simp]
lemma injective_preimage {α β : Type*} {f : α → β} : injective (preimage f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.injective_preimage⟩,
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).nonempty,
  { rw [h.nonempty preimage_empty], apply singleton_nonempty },
  exact ⟨x, hx⟩
end

@[simp]
lemma surjective_preimage {α β : Type*} {f : α → β} : surjective (preimage f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.surjective_preimage⟩,
  cases h {x} with s hs, have := mem_singleton x,
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
end

@[simp] lemma surjective_image {α β : Type*} {f : α → β} : surjective (image f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.surjective_image⟩,
  cases h {y} with s hs,
  have := mem_singleton y, rw [← hs] at this, rcases this with ⟨x, h1x, h2x⟩,
  exact ⟨x, h2x⟩
end

@[simp] lemma injective_image {α β : Type*} {f : α → β} : injective (image f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.injective_image⟩,
  rw [← singleton_eq_singleton_iff], apply h,
  rw [image_singleton, image_singleton, hx]
end


namespace homeomorph
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]
@[simp]
lemma is_open_preimage (f : α ≃ₜ β) {s : set β} : is_open (f ⁻¹' s) ↔ is_open s :=
begin
  refine ⟨λ h, _, f.continuous_to_fun s⟩,
  rw [← (image_preimage_eq f.to_equiv.surjective : _ = s)], exact f.is_open_map _ h
end

end homeomorph

section
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]


lemma is_closed_preimage {f : α → β} (hf : continuous f) {s : set β} (h : is_closed s) :
  is_closed (f ⁻¹' s) :=
by exact continuous_iff_is_closed.mp hf s h

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts (α : Type*) [topological_space α] : set (set α) := { s : set α | compact s }

instance compacts.has_sup (α : Type*) [topological_space α] : has_sup (compacts α) :=
⟨λ K₁ K₂, ⟨K₁.1 ∪ K₂.1, K₁.2.union K₂.2⟩⟩

@[simp] lemma compacts.sup_fst {α : Type*} [topological_space α] {K₁ K₂ : compacts α} :
  (K₁ ⊔ K₂).1 = K₁.1 ∪ K₂.1 :=
rfl

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
  `nonempty_compacts`. -/
def positive_compacts (α : Type*) [topological_space α] : set (set α) :=
{ s : set α | compact s ∧ (interior s).nonempty  }

/-- The open neighborhoods of a point. See also `opens`. -/
def open_nhds_of {α : Type*} [topological_space α] (x : α) : set (set α) :=
{ s : set α | is_open s ∧ x ∈ s }

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
lemma separate_one_open_mul [group α] [topological_group α] {U : set α}
  (h1U : (1 : α) ∈ U) (h2U : is_open U) : ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ V.mul V ⊆ U :=
begin
  sorry
end

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
lemma separate_compact_open_mul [group α] [topological_group α] {K U : set α} (hK : compact K)
  (hU : is_open U) (hKU : K ⊆ U) : ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ K.mul V ⊆ U :=
begin
  sorry
end

variables {ι : Type*} {π : ι → Type*} [∀i, topological_space (π i)]

/-- A version of Tychonoff's theorem that uses `set.pi`. -/
lemma compact_univ_pi {s : Πi:ι, set (π i)} (h : ∀i, compact (s i)) : compact (set.pi set.univ s) :=
by { convert compact_pi_infinite h, simp only [pi, forall_prop_of_true, mem_univ] }

end

variables {α : Type u} [measurable_space α]
          {β : Type v} [measurable_space β]

section
variables [topological_space α]  [borel_space α]
lemma compact.is_measurable [t2_space α] {s : set α} (h : compact s) : is_measurable s :=
(closed_of_compact _ h).is_measurable
end



namespace measure_theory

/-- A measure is nonzero if it is not 0 on the whole space. -/
def measure.nonzero (μ : measure α) : Prop :=
μ set.univ > 0

variable [topological_space α]

/-- A regular borel measure. -/
structure measure.regular (μ : measure α) : Prop :=
  (le_top_of_compact : ∀ {{K : set α}}, compact K → μ K < ⊤)
  (outer_regular : ∀ {{A : set α}}, is_measurable A →
    μ A = ⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U)
  (inner_regular : ∀ {{U : set α}}, is_open U →
    μ U = ⨆ (K : set α) (h : compact K) (h2 : K ⊆ U), μ K)


variables {G : Type w} [measurable_space G] [group G] [topological_space G] [topological_group G]
  [borel_space G]

lemma measurable_inv : measurable (inv : G → G) :=
continuous.measurable continuous_inv

lemma measurable_mul [second_countable_topology G] : measurable (λ p : G × G, p.1 * p.2) :=
continuous.measurable continuous_mul

lemma measurable_mul_left (g : G) : measurable (λ h : G, g * h) :=
continuous.measurable $ continuous_const.mul continuous_id

lemma measurable_mul_right (g : G) : measurable (λ h : G, h * g) :=
continuous.measurable $ continuous_id.mul continuous_const

def is_left_invariant (μ : measure G) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, g * h) ⁻¹' A) = μ A

def is_right_invariant (μ : measure G) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, h * g) ⁻¹' A) = μ A

-- /-- A left Haar measure. -/
-- structure is_left_haar_measure (μ : measure G) : Prop :=
--   (measure_univ_pos : μ.nonzero)
--   (is_regular : μ.regular)
--   (left_invariant : is_left_invariant μ)

-- /-- A right Haar measure. -/
-- structure is_right_haar_measure (μ : measure G) : Prop :=
--   (measure_univ_pos : μ.nonzero)
--   (is_regular : μ.regular)
--   (right_invariant : is_right_invariant μ)

namespace measure

/-- The conjugate of a measure on a topological group. -/
@[nolint unused_arguments]
protected def conj (μ : measure G) : measure G :=
μ.map inv

lemma conj_apply (μ : measure G) {s : set G} (hs : is_measurable s) :
  μ.conj s = μ (inv ⁻¹' s) :=
by { unfold measure.conj, rw [measure.map_apply measurable_inv hs] }

@[simp] lemma conj_conj (μ : measure G) : μ.conj.conj = μ :=
begin
  ext1 s hs,
  rw [μ.conj.conj_apply hs, μ.conj_apply (measurable_inv.preimage hs), ←preimage_comp],
  congr, ext g, rw [function.comp_app, inv_inv],
end

variables {μ : measure G}

lemma nonzero.conj (h : μ.nonzero) : μ.conj.nonzero :=
by { dsimp [nonzero], rwa [μ.conj_apply is_measurable.univ, preimage_univ] }

lemma regular.conj [t2_space G] (h : μ.regular) : μ.conj.regular :=
begin
  split,
  { intros K hK, rw [μ.conj_apply hK.is_measurable], apply h.le_top_of_compact,
    exact (homeomorph.inv G).compact_preimage.mpr hK },
  { intros A hA, rw [μ.conj_apply hA, h.outer_regular (measurable_inv.preimage hA)],
    symmetry, apply infi_congr (preimage inv) (equiv.inv G).injective.surjective_preimage,
    intro U, apply infi_congr_Prop (homeomorph.inv G).is_open_preimage, intro hU,
    apply infi_congr_Prop,
    { apply preimage_subset_preimage_iff, rw [surjective.range_eq], apply subset_univ,
      exact (equiv.inv G).surjective },
    intro h2U, rw [μ.conj_apply hU.is_measurable] },
  { intros U hU, rw [μ.conj_apply hU.is_measurable, h.inner_regular (continuous_inv U hU)],
    symmetry,
    apply supr_congr (preimage inv) (equiv.inv G).injective.surjective_preimage,
    intro K, apply supr_congr_Prop (homeomorph.inv G).compact_preimage, intro hK,
    apply supr_congr_Prop,
    { apply preimage_subset_preimage_iff, rw [surjective.range_eq], apply subset_univ,
      exact (equiv.inv G).surjective },
    intro h2U, rw [μ.conj_apply hK.is_measurable] },
end

end measure

variables [t2_space G] {μ : measure G}

@[simp] lemma regular_conj_iff : μ.conj.regular ↔ μ.regular :=
by { refine ⟨λ h, _, measure.regular.conj⟩, rw ←μ.conj_conj, exact measure.regular.conj h }

lemma is_right_invariant_conj' (h : is_left_invariant μ) :
  is_right_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_right g A hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv A hA) using 2,
  simp only [←preimage_comp], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv]
end

lemma is_left_invariant_conj' (h : is_right_invariant μ) : is_left_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_left g A hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv A hA) using 2,
  simp only [←preimage_comp], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv]
end

@[simp] lemma is_right_invariant_conj : is_right_invariant μ.conj ↔ is_left_invariant μ :=
by { refine ⟨λ h, _, is_right_invariant_conj'⟩, rw ←μ.conj_conj, exact is_left_invariant_conj' h }

@[simp] lemma is_left_invariant_conj : is_left_invariant μ.conj ↔ is_right_invariant μ :=
by { refine ⟨λ h, _, is_left_invariant_conj'⟩, rw ←μ.conj_conj, exact is_right_invariant_conj' h }

/- we put the construction of the Haar measure in a namespace to partially hide it -/
namespace haar
/-- (K : V) -/
def index (K V : set G) : ℕ :=
Inf $ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V }

/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
lemma index_defined {K V : set G} (hK : compact K) (hV : (interior V).nonempty) :
  ∃ n : ℕ, n ∈ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V } :=
begin
  cases hV with g₀ hg₀,
  rcases compact.elim_finite_subcover hK (λ g : G, interior $ (λ h, g * h) ⁻¹' V) _ _ with ⟨t, ht⟩,
  { refine ⟨t.card, t, subset.trans ht _, rfl⟩,
    apply Union_subset_Union, intro g, apply Union_subset_Union, intro hg, apply interior_subset },
  { intro g, apply is_open_interior },
  { intros g hg, rw [mem_Union], use g₀ * g⁻¹,
    apply preimage_interior_subset_interior_preimage, exact continuous_const.mul continuous_id,
    rwa [mem_preimage, inv_mul_cancel_right] }
end

lemma index_elim {K V : set G} (hK : compact K) (hV : (interior V).nonempty) :
  ∃ (t : finset G), K ⊆ (⋃ g ∈ t, (λ h, g * h) ⁻¹' V) ∧ finset.card t = index K V :=
by { have := nat.Inf_spec (index_defined hK hV), rwa [mem_image] at this }


lemma index_empty {V : set G} : index ∅ V = 0 :=
begin
  simp only [index, nat.Inf_eq_zero], left, use ∅,
  simp only [finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_self],
end

lemma le_index_mul (K₀ : positive_compacts G) (K : compacts G) {V : set G}
  (hV : (interior V).nonempty) : index K.1 V ≤ index K.1 K₀.1 * index K₀.1 V :=
begin
  classical,
  rcases index_elim K.2 K₀.2.2 with ⟨s, h1s, h2s⟩,
  rcases index_elim K₀.2.1 hV with ⟨t, h1t, h2t⟩,
  rw [← h2s, ← h2t],
  transitivity (t.mul s).card,
  { apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq], refine subset.trans h1s _,
    apply bUnion_subset, intros g₁ hg₁, rw preimage_subset_iff, intros g₂ hg₂,
    have := h1t hg₂,
    rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, hV⟩, rw [mem_preimage] at hV,
    fapply mem_bUnion, exact g₃ * g₁,
    simp only [multiset.mem_erase_dup, finset.product_val, multiset.mem_product, multiset.mem_map,
      finset.image_val, prod.exists, mem_def, finset.mul],
    refine ⟨g₃, g₁, ⟨hg₃, hg₁⟩, rfl⟩, rw [mem_preimage], convert hV using 1, rw [mul_assoc] },
  { convert finset.card_image_le, rw [finset.card_product, mul_comm] },
end

lemma index_pos (K : positive_compacts G) {V : set G} (hV : (interior V).nonempty) : 0 < index K.1 V :=
begin
  unfold index, rw [Inf_nat_def, nat.find_pos, mem_image],
  { rintro ⟨t, h1t, h2t⟩, rw [finset.card_eq_zero] at h2t, subst h2t,
    cases K.2.2 with g hg,
    show g ∈ (∅ : set G), convert h1t (interior_subset hg), symmetry, apply bUnion_empty },
  { exact index_defined K.2.1 hV }
end

lemma index_mono {K K' V : set G} (hK' : compact K') (h : K ⊆ K')
  (hV : (interior V).nonempty) : index K V ≤ index K' V :=
begin
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩,
  apply nat.Inf_le, rw [mem_image], refine ⟨s, subset.trans h h1s, h2s⟩
end

def index_union_le (K₁ K₂ : compacts G) {V : set G} (hV : (interior V).nonempty) :
  index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V :=
begin
  classical,
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩,
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩,
  rw [← h2s, ← h2t],
  refine le_trans _ (finset.card_union_le _ _),
  apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq],
  apply union_subset; refine subset.trans (by assumption) _; apply bUnion_subset_bUnion_left;
    intros g hg; simp [mem_def] at hg;
    simp only [mem_def, multiset.mem_union, finset.union_val, hg, or_true, true_or]
end

def index_union_eq (K₁ K₂ : compacts G) {V : set G} (hV : (interior V).nonempty)
  (h : disjoint (K₁.1.mul V.inv) (K₂.1.mul V.inv)) :
  index (K₁.1 ∪ K₂.1) V = index K₁.1 V + index K₂.1 V :=
begin
  classical,
  apply le_antisymm (index_union_le K₁ K₂ hV),
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩, rw [← h2s],
  have : ∀(K : set G) , K ⊆ (⋃ g ∈ s, (λ h, g * h) ⁻¹' V) →
    index K V ≤ (s.filter (λ g, ((λ (h : G), g * h) ⁻¹' V ∩ K).nonempty)).card,
  { intros K hK, apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq],
    intros g hg, rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩,
    simp only [mem_preimage] at h2g₀,
    rw mem_Union, use g₀, rw mem_Union, split,
    { simp only [finset.mem_filter, h1g₀, true_and], use g,
      simp only [hg, h2g₀, mem_inter_eq, mem_preimage, and_self] },
    exact h2g₀ },
  refine le_trans (add_le_add (this K₁ $ subset.trans (subset_union_left _ _) h1s)
    (this K₂ $ subset.trans (subset_union_right _ _) h1s)) _,
  rw [← finset.card_union_eq, finset.filter_union_right],
  { apply finset.card_le_of_subset, apply finset.filter_subset },
  apply finset.disjoint_filter.mpr,
  rintro g₁ h1g₁ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩,
  simp only [mem_preimage] at h1g₃ h1g₂,
  apply @h g₁⁻¹,
  split; simp only [set.mem_inv, set.mem_mul, exists_exists_and_eq_and, exists_and_distrib_left],
  { refine ⟨_, h2g₂, _, h1g₂, _⟩, simp only [mul_inv_rev, mul_inv_cancel_left] },
  { refine ⟨_, h2g₃, _, h1g₃, _⟩, simp only [mul_inv_rev, mul_inv_cancel_left] }
end

/-- prehaar -/
-- in notes: K₀ compact with non-empty interior, U open containing 1, K compact
def prehaar (K₀ U : set G) (K : compacts G) : ℝ := (index K.1 U : ℝ) / index K₀ U

lemma prehaar_nonneg (K₀ : positive_compacts G) {U : set G} (K : compacts G)
  (hU : (interior U).nonempty) : 0 ≤ prehaar K₀.1 U K :=
by { apply div_nonneg; norm_cast, apply zero_le, exact index_pos K₀ hU }

lemma prehaar_le_index (K₀ : positive_compacts G) {U : set G} (K : compacts G)
  (hU : (interior U).nonempty) : prehaar K₀.1 U K ≤ index K.1 K₀.1 :=
begin
  unfold prehaar, rw [div_le_iff]; norm_cast,
  { apply le_index_mul K₀ K hU },
  { exact index_pos K₀ hU }
end

-- lemma prehaar_pos (K₀ : positive_compacts G) {U : set G} (hU : (interior U).nonempty)
--   {K : set G} (h1K : compact K) (h2K : (interior K).nonempty) : 0 < prehaar K₀.1 U ⟨K, h1K⟩ :=
-- by { apply div_pos; norm_cast, apply index_pos ⟨K, h1K, h2K⟩ hU, exact index_pos K₀ hU }

def prehaar_mono {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty)
  {K₁ K₂ : compacts G} (h : K₁.1 ⊆ K₂.1) : prehaar K₀.1 U K₁ ≤ prehaar K₀.1 U K₂ :=
begin
  simp only [prehaar], rw [div_le_div_right], exact_mod_cast index_mono K₂.2 h hU,
  exact_mod_cast index_pos K₀ hU
end

def prehaar_self {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty) :
  prehaar K₀.1 U ⟨K₀.1, K₀.2.1⟩ = 1 :=
by { simp only [prehaar], rw [div_self], apply ne_of_gt, exact_mod_cast index_pos K₀ hU }

def prehaar_sup_le {K₀ : positive_compacts G} {U : set G} (K₁ K₂ : compacts G)
  (hU : (interior U).nonempty) : prehaar K₀.1 U (K₁ ⊔ K₂) ≤ prehaar K₀.1 U K₁ + prehaar K₀.1 U K₂ :=
begin
  simp only [prehaar], rw [div_add_div_same, div_le_div_right],
  exact_mod_cast index_union_le K₁ K₂ hU, exact_mod_cast index_pos K₀ hU
end

def prehaar_sup_eq {K₀ : positive_compacts G} {U : set G} {K₁ K₂ : compacts G}
  (hU : (interior U).nonempty) (h : disjoint (K₁.1.mul U.inv) (K₂.1.mul U.inv)) :
  prehaar K₀.1 U (K₁ ⊔ K₂) = prehaar K₀.1 U K₁ + prehaar K₀.1 U K₂ :=
by { simp only [prehaar], rw [div_add_div_same], congr' 1, exact_mod_cast index_union_eq K₁ K₂ hU h }

/-- haar_product X -/
def haar_product (K₀ : set G) : set (compacts G → ℝ) :=
set.pi set.univ (λ K, Icc 0 $ index K.1 K₀)

lemma prehaar_mem_haar_product (K₀ : positive_compacts G) {U : set G}
  (hU : (interior U).nonempty) : prehaar K₀.1 U ∈ haar_product K₀.1 :=
by { rintro ⟨K, hK⟩ h2K, rw [mem_Icc],
     exact ⟨prehaar_nonneg K₀ _ hU, prehaar_le_index K₀ _ hU⟩ }

/-- C -/
def CC (K₀ : set G) (V : open_nhds_of (1 : G)) : set (compacts G → ℝ) :=
closure $ prehaar K₀ '' { U : set G | U ⊆ V ∧ is_open U ∧ (1 : G) ∈ U }

lemma nonempty_Inter_CC (K₀ : positive_compacts G) :
  (haar_product K₀.1 ∩ ⋂ (V : open_nhds_of (1 : G)), CC K₀.1 V).nonempty :=
begin
  have : compact (haar_product K₀.1), { apply compact_univ_pi, intro K, apply compact_Icc },
  rw [← ne_empty_iff_nonempty],
  have := compact.elim_finite_subfamily_closed this (CC K₀) (λ s, is_closed_closure), apply mt this,
  rintro ⟨t, h1t⟩, rw [← not_nonempty_iff_eq_empty] at h1t, apply h1t,
  let V₀ := ⋂ (V ∈ t), (V : open_nhds_of 1).1,
  have h1V₀ : is_open V₀,
  { apply is_open_bInter, apply finite_mem_finset, rintro ⟨V, hV⟩ h2V, exact hV.1 },
  have h2V₀ : (1 : G) ∈ V₀, { rw mem_Inter, rintro ⟨V, hV⟩, rw mem_Inter, intro h2V, exact hV.2 },
  refine ⟨prehaar K₀ V₀, _⟩,
  split,
  { apply prehaar_mem_haar_product K₀, use 1, rwa interior_eq_of_open h1V₀ },
  { rw mem_Inter, rintro ⟨V, hV⟩, rw mem_Inter, intro h2V, apply subset_closure,
    apply mem_image_of_mem, rw [mem_set_of_eq],
    exact ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩ },
end

/-- the Haar measure on compact sets -/
def chaar (K₀ : positive_compacts G) (K : compacts G) : ℝ :=
classical.some (nonempty_Inter_CC K₀) K

lemma chaar_mem_haar_product (K₀ : positive_compacts G) : chaar K₀ ∈ haar_product K₀.1 :=
(classical.some_spec (nonempty_Inter_CC K₀)).1

lemma chaar_mem_CC (K₀ : positive_compacts G) (V : open_nhds_of (1 : G)) : chaar K₀ ∈ CC K₀.1 V :=
by { have := (classical.some_spec (nonempty_Inter_CC K₀)).2, rw [mem_Inter] at this, exact this V }

lemma chaar_nonneg (K₀ : positive_compacts G) (K : compacts G) : chaar K₀ K ≥ 0 :=
by { have := chaar_mem_haar_product K₀ K (mem_univ _), rw mem_Icc at this, exact this.1 }

lemma chaar_mono {K₀ : positive_compacts G} {K₁ K₂ : compacts G} (h : K₁.1 ⊆ K₂.1) :
  chaar K₀ K₁ ≤ chaar K₀ K₂ :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₂ - f K₁,
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_apply K₂) (@continuous_apply _ (λ _, ℝ) _ K₁)),
  rw [← sub_nonneg], show chaar K₀ ∈ eval ⁻¹' (Ici (0 : ℝ)),
  apply mem_of_subset_of_mem _ (chaar_mem_CC K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold CC, rw closure_subset_iff_subset_of_is_closed,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, simp only [mem_preimage, mem_Ici, eval, sub_nonneg],
    apply prehaar_mono _ h, rw interior_eq_of_open h2U, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_Ici },
end

def chaar_sup_le {K₀ : positive_compacts G} (K₁ K₂ : compacts G) :
  chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₁ + f K₂ - f (K₁ ⊔ K₂),
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_add.comp
      (continuous.prod_mk (continuous_apply K₁) (@continuous_apply _ (λ _, ℝ) _ K₂)))
      (@continuous_apply _ (λ _, ℝ) _(K₁ ⊔ K₂))),
  rw [← sub_nonneg], show chaar K₀ ∈ eval ⁻¹' (Ici (0 : ℝ)),
  apply mem_of_subset_of_mem _ (chaar_mem_CC K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold CC, rw closure_subset_iff_subset_of_is_closed,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, simp only [mem_preimage, mem_Ici, eval, sub_nonneg],
    apply prehaar_sup_le, rw interior_eq_of_open h2U, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_Ici },
end

lemma chaar_sup_eq {K₀ : positive_compacts G} {K₁ K₂ : compacts G} (h : disjoint K₁.1 K₂.1) :
  chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ :=
begin
  rcases compact_compact_separated K₁.2 K₂.2 (disjoint_iff.mp h) with
    ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩,

end

/-- the value of the Haar measure on `G` on all open sets -/
def ohaar (K₀ : positive_compacts G) (U : opens G) : ennreal :=
⨆ (K : compacts G) (h : K.1 ⊆ U.1), show nnreal, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩

lemma ohaar_eq_chaar (K₀ : positive_compacts G) {K : set G} (oK : is_open K) (cK : compact K) :
  ohaar K₀ ⟨K, oK⟩ = show nnreal, from ⟨chaar K₀ ⟨K, cK⟩, chaar_nonneg K₀ ⟨K, cK⟩⟩ :=
sorry

/-- the value of the Haar measure on `G` on any set -/
def haar (K₀ : positive_compacts G) (A : set G) : ennreal :=
⨅ (U : opens G) (h : A ⊆ U), ohaar K₀ U

lemma haar_eq_ohaar (K₀ : positive_compacts G) (K : opens G) : haar K₀ K.1 = ohaar K₀ K :=
sorry

end haar
open haar

/-- the Haar measure on `G` -/
def haar_measure (K₀ : positive_compacts G) : measure G :=
{ measure_of := haar K₀,
  empty := sorry,
  mono := sorry,
  Union_nat := sorry,
  m_Union := sorry,
  trimmed := sorry }

lemma is_left_invariant_haar_measure (K₀ : positive_compacts G) (K : compacts G) :
  is_left_invariant (haar_measure K₀) :=
sorry

lemma nonzero_haar_measure (K₀ : positive_compacts G) (K : compacts G) :
  (haar_measure K₀).nonzero :=
sorry

lemma regular_haar_measure (K₀ : positive_compacts G) (K : compacts G) :
  (haar_measure K₀).regular :=
sorry



end measure_theory
-- #lint
