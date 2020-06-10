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

namespace function

@[simp] lemma nat.find_pos {p : ℕ → Prop} [decidable_pred p] (h : ∃ (n : ℕ), p n) :
  0 < nat.find h ↔ ¬ p 0 :=
begin
  rw [nat.pos_iff_ne_zero, not_iff_not],
  split,
  { intro h0, rw [← h0], apply nat.find_spec },
  { intro hp, apply nat.eq_zero_of_le_zero, exact nat.find_min' _ hp }
end

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

variables {α : Type u} [measurable_space α]
          {β : Type v} [measurable_space β]

lemma disjoint.preimage {α β} (f : α → β) {s t : set β} (h : disjoint s t) :
  disjoint (f ⁻¹' s) (f ⁻¹' t) :=
λ x hx, h hx

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

/-- A left Haar measure. -/
structure is_left_haar_measure (μ : measure G) : Prop :=
  (measure_univ_pos : μ.nonzero)
  (is_regular : μ.regular)
  (left_invariant : ∀ (g : G) {A : set G} (h : is_measurable A),
    μ ((λ h, g * h) ⁻¹' A) = μ A)

/-- A right Haar measure. -/
structure is_right_haar_measure (μ : measure G) : Prop :=
  (measure_univ_pos : μ.nonzero)
  (is_regular : μ.regular)
  (right_invariant : ∀ (g : G) {A : set G} (h : is_measurable A),
    μ ((λ h, h * g) ⁻¹' A) = μ A)

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

lemma is_right_haar_measure_conj' (h : is_left_haar_measure μ) :
  is_right_haar_measure μ.conj :=
begin
  split,
  { exact h.1.conj },
  { exact h.2.conj },
  { intros g A hA, rw [μ.conj_apply (measurable_mul_right g A hA), μ.conj_apply hA],
    convert h.3 g⁻¹ (measurable_inv A hA) using 2,
    simp only [←preimage_comp], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv] },
end

lemma is_left_haar_measure_conj' (h : is_right_haar_measure μ) :
  is_left_haar_measure μ.conj :=
begin
  split,
  { exact h.1.conj },
  { exact h.2.conj },
  { intros g A hA, rw [μ.conj_apply (measurable_mul_left g A hA), μ.conj_apply hA],
    convert h.3 g⁻¹ (measurable_inv A hA) using 2,
    simp only [←preimage_comp], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv] },
end

@[simp] lemma is_right_haar_measure_conj : is_right_haar_measure μ.conj ↔ is_left_haar_measure μ :=
by { refine ⟨λ h, _, is_right_haar_measure_conj'⟩, rw ←μ.conj_conj,
     exact is_left_haar_measure_conj' h }

@[simp] lemma is_left_haar_measure_conj : is_left_haar_measure μ.conj ↔ is_right_haar_measure μ :=
by { refine ⟨λ h, _, is_left_haar_measure_conj'⟩, rw ←μ.conj_conj,
     exact is_right_haar_measure_conj' h }

/-- (K : V) -/
def rank (K V : set G) : ℕ :=
Inf {n | ∃ (t : finset G), finset.card t = n ∧ K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V }

lemma rank_empty {V : set G} : rank ∅ V = 0 :=
sorry

lemma le_rank_mul {K₀ K U : set G} : rank K U ≤ rank K K₀ * rank K₀ U :=
sorry

lemma rank_defined {K V : set G} (hK : compact K) (hV : (interior V).nonempty) :
  ∃ n : ℕ, ∃ (t : finset G), finset.card t = n ∧ K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V :=
begin
  cases hV with g₀ hg₀,
  rcases compact.elim_finite_subcover hK (λ g : G, interior $ (λ h, g * h) ⁻¹' V) _ _ with ⟨t, ht⟩,
  { refine ⟨t.card, t, rfl, subset.trans ht _⟩,
    apply Union_subset_Union, intro g, apply Union_subset_Union, intro hg, apply interior_subset },
  { intro g, apply is_open_interior },
  { intros g hg, rw [mem_Union], use g₀ * g⁻¹,
    apply preimage_interior_subset_interior_preimage, exact continuous_const.mul continuous_id,
    rwa [mem_preimage, inv_mul_cancel_right] }
end

lemma rank_pos {K V : set G} (hK : compact K) (hV : (interior V).nonempty)
  (h2K : (interior K).nonempty) : 0 < rank K V :=
begin
  unfold rank, rw [Inf_nat_def, nat.find_pos, mem_set_of_eq],
  { rintro ⟨t, h1t, h2t⟩, rw [finset.card_eq_zero] at h1t, subst h1t,
    cases h2K with g hg,
    show g ∈ (∅ : set G), convert h2t (interior_subset hg), symmetry, apply bUnion_empty },
  { exact rank_defined hK hV }
end

/-- mu -/
def mu (K₀ U K : set G) : ℝ := (rank K U : ℝ) / rank K₀ U

lemma mu_nonneg {K₀ U K : set G} : 0 ≤ mu K₀ U K :=
sorry

lemma mu_le_rank {K₀ U K : set G} : mu K₀ U K ≤ rank K K₀ :=
sorry

/-- XX -/
def XX (K₀ : set G) : set (set G → ℝ) :=
set.pi set.univ /- or compacts -/ (λ K, Icc 0 $ rank K K₀)

def mu_mem_XX {K₀ U : set G}: mu K₀ U ∈ XX K₀ :=
by { intros K hK, rw [mem_Icc], exact ⟨mu_nonneg, mu_le_rank⟩ }




def haar_measure' (K₀ V : set G) : ℝ := sorry

theorem exists_left_haar_measure [locally_compact_space G] :
  ∃ (μ : measure G), is_left_haar_measure μ :=
begin
  sorry
end

end measure_theory
