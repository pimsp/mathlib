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


## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
-/
universe variables u v w
noncomputable theory

open set measurable_space has_inv

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

namespace set
variables {α : Type*} {β : Type*}

/-- The pointwise product of two sets `s` and `t`:
  `st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }. -/
@[to_additive "The pointwise sum of two sets `s` and `t`: `s + t = { x + y | x ∈ s, y ∈ t }."]
protected def mul [has_mul α] (s t : set α) : set α :=
(λ p : α × α, p.1 * p.2) '' s.prod t

@[simp, to_additive] lemma mem_mul [has_mul α] {s t : set α} {x : α} :
  x ∈ s.mul t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [set.mul, and.assoc, mem_image, mem_prod, prod.exists] }

@[to_additive] lemma mul_mem_mul [has_mul α] {s t : set α} {x y : α} (hx : x ∈ s) (hy : y ∈ t) :
  x * y ∈ s.mul t :=
by { simp only [mem_mul], exact ⟨x, y, hx, hy, rfl⟩ }

@[simp, to_additive add_image_prod]
lemma mul_image_prod [has_mul α] (s t : set α) : (λ p : α × α, p.1 * p.2) '' s.prod t = s.mul t :=
rfl

@[to_additive]
lemma mul_subset_mul [has_mul α] {s t u v : set α} (h1 : u ⊆ s) (h2 : v ⊆ t) :
  u.mul v ⊆ s.mul t :=
by { apply image_subset, simp only [prod_subset_prod_iff, h1, h2, true_or, and_self], }

/-- The pointwise inverse of a set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }. -/
@[to_additive "The pointwise additive inverse of a set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }"]
protected def inv [has_inv α] (s : set α) : set α :=
has_inv.inv ⁻¹' s

@[to_additive, simp] lemma mem_inv [has_inv α] {s : set α} {x : α} :
  x ∈ s.inv ↔ x⁻¹ ∈ s :=
by { simp only [set.inv, mem_preimage] }

@[to_additive] lemma inv_mem_inv [group α] {s : set α} {x : α} : x⁻¹ ∈ s.inv ↔ x ∈ s :=
by simp only [mem_inv, inv_inv]

@[simp, to_additive]
lemma inv_preimage [has_inv α] (s : set α) : has_inv.inv ⁻¹' s = s.inv :=
rfl

@[simp, to_additive]
lemma inv_image [group α] (s : set α) : has_inv.inv '' s = s.inv :=
by refine congr_fun (image_eq_preimage_of_inverse _ _) s; intro; simp only [inv_inv]

@[to_additive, simp] protected lemma inv_inv [group α] {s : set α} : s.inv.inv = s :=
by { simp only [set.inv, ← preimage_comp], convert preimage_id, ext x, apply inv_inv }

@[to_additive, simp] protected lemma univ_inv [group α] : (univ : set α).inv = univ :=
preimage_univ

@[simp, to_additive]
lemma inv_subset_inv [group α] {s t : set α} : s.inv ⊆ t.inv ↔ s ⊆ t :=
by { apply preimage_subset_preimage_iff, rw surjective.range_eq, apply subset_univ,
     exact (equiv.inv α).surjective }

@[to_additive] lemma inv_subset [group α] {s t : set α} : s.inv ⊆ t ↔ s ⊆ t.inv :=
by { rw [← inv_subset_inv, set.inv_inv] }

theorem disjoint_iff_inter_eq_empty {s t : set α} : disjoint s t ↔ s ∩ t = ∅ :=
disjoint_iff

theorem disjoint_of_subset_left {s t u : set α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
disjoint_left.2 (λ x m₁, (disjoint_left.1 d) (h m₁))

theorem disjoint_of_subset_right {s t u : set α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
disjoint_right.2 (λ x m₁, (disjoint_right.1 d) (h m₁))

theorem disjoint_of_subset {s t u v : set α} (h1 : s ⊆ u) (h2 : t ⊆ v) (d : disjoint u v) :
  disjoint s t :=
disjoint_of_subset_left h1 $ disjoint_of_subset_right h2 d

theorem subset.rfl {s : set α} : s ⊆ s := subset.refl s

lemma diff_inter_diff {s t u : set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
by { ext x, simp only [mem_inter_eq, mem_union_eq, mem_diff], tauto }

@[simp] lemma Union_fin_zero {α} {f : fin 0 → set α} : (⋃ i : fin 0, f i) = ∅ :=
by { rw [← subset_empty_iff], rintro x ⟨_, ⟨⟨⟨_, ⟨⟩⟩⟩⟩⟩ }

lemma bUnion_empty' (s : α → set β) : (⋃ x ∈ (∅ : set α), s x) = ∅ :=
supr_emptyset

lemma subset_diff {s t u : set α} : s ⊆ t \ u ↔ s ⊆ t ∧ disjoint s u :=
⟨λ h, ⟨λ x hxs, (h hxs).1, λ x ⟨hxs, hxu⟩, (h hxs).2 hxu⟩,
λ ⟨h1, h2⟩ x hxs, ⟨h1 hxs, λ hxu, h2 ⟨hxs, hxu⟩⟩⟩

end set
open set

namespace finset
variables {α : Type*} {β : Type*} {γ : Type*}



variables

/-- The pointwise product of two finite sets `s` and `t`:
  `st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[to_additive "The pointwise sum of two finite sets `s` and `t`:
  `s + t = { x + y | x ∈ s, y ∈ t }`."]
protected def mul [decidable_eq α] [has_mul α](s t : finset α) : finset α :=
(s.product t).image (λ p : α × α, p.1 * p.2)

@[simp] lemma mem_mul [decidable_eq α] [has_mul α] {s t : finset α} {x : α} :
  x ∈ s.mul t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [finset.mul, and.assoc, mem_image, exists_prop, prod.exists, mem_product] }

-- /-- The pointwise inverse of a finite set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }. -/
-- @[to_additive "The pointwise additive inverse of a finite set `s`: `s⁻¹ = { x⁻¹ | x ∈ s }"]
-- protected def inv [has_inv α] (s : finset α) : finset α :=
-- s.preimage has_inv.inv

-- @[simp] lemma mem_inv [has_inv α] {s : finset α} {x : α} :
--   x ∈ s.inv ↔ ∃ y, y ∈ s ∧ y⁻¹ = x :=
-- by { simp only [finset.inv, mem_image, exists_prop] }

lemma card_union_eq [decidable_eq α] {s t : finset α} (h : disjoint s t) : (s ∪ t).card = s.card + t.card :=
begin
  rw [← card_union_add_card_inter],
  convert (add_zero _).symm, rwa [card_eq_zero, ← disjoint_iff_inter_eq_empty]
end

lemma card_filter_add_card_filter_le {s : finset α} {p q : α → Prop} [decidable_pred p]
  [decidable_pred q] (h : ∀ x, x ∈ s → p x → ¬ q x) :
  (s.filter p).card + (s.filter q).card ≤ s.card :=
begin
  haveI : decidable_eq α := λ x y, classical.dec _,
  rw [← card_union_eq (disjoint_filter.mpr h), filter_union_right],
  exact card_le_of_subset (filter_subset _)
end

lemma comp_sup_eq_sup_comp' [semilattice_sup_bot α] [semilattice_sup_bot γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) :
  g (s.sup f) = s.sup (g ∘ f) :=
by letI := classical.dec_eq β; from
finset.induction_on s (by simp [bot]) (by simp [g_sup] {contextual := tt})

end finset


section
variables {α : Type*} {β : Type*}
/-- A subtype forms a `⊔`-`⊥`-semilattice if the property respects `⊥` and `⊔`. -/
def subtype.semilattice_sup_bot [semilattice_sup_bot α] {P : α → Prop}
  (Pbot : P ⊥) (Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)) : semilattice_sup_bot {x : α // P x} :=
{ bot := ⟨⊥, Pbot⟩,
  le := λ x y, x ≤ y,
  lt := λ x y, x < y,
  le_refl := λ x, le_refl _,
  le_trans := λ x y z, le_trans,
  lt_iff_le_not_le := λ x y, lt_iff_le_not_le,
  le_antisymm := λ x y h₁ h₂, subtype.eq $ le_antisymm h₁ h₂,
  bot_le := λ x, bot_le,
  sup := λ x y, ⟨x ⊔ y, Psup x.2 y.2⟩,
  le_sup_left := λ x y, @le_sup_left _ _ (x : α) y,
  le_sup_right := λ x y, @le_sup_right _ _ (x : α) y,
  sup_le := λ x y z h1 h2, @sup_le α _ _ _ _ h1 h2 }

lemma subtype.sup_val [semilattice_sup_bot α] {P : α → Prop}
  {Pbot : P ⊥} {Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@finset.sup _ _ (subtype.semilattice_sup_bot Pbot Psup) t f).1 = t.sup (λ x, (f x).1) :=
by { classical, rw [finset.comp_sup_eq_sup_comp' subtype.val]; intros; refl }

end

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

namespace topological_space
variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

lemma is_closed_preimage {f : α → β} (hf : continuous f) {s : set β} (h : is_closed s) :
  is_closed (f ⁻¹' s) :=
by exact continuous_iff_is_closed.mp hf s h

-- protected def int (s : set α) : opens α := ⟨interior s, is_open_interior⟩
-- localized "postfix `ᵒ`:(max+1) := topological_space.int" in topology

/-- The compact sets of a topological space. See also `nonempty_compacts`. -/
def compacts (α : Type*) [topological_space α] : Type* := { s : set α // compact s }

instance : semilattice_sup_bot (compacts α) :=
subtype.semilattice_sup_bot compact_empty (λ K₁ K₂, compact.union)

@[simp] lemma compacts.bot_val : (⊥ : compacts α).1 = ∅ := rfl

@[simp] lemma compacts.sup_val {K₁ K₂ : compacts α} : (K₁ ⊔ K₂).1 = K₁.1 ∪ K₂.1 := rfl

@[ext] lemma compacts.ext {K₁ K₂ : compacts α} (h : K₁.1 = K₂.1) : K₁ = K₂ :=
subtype.eq h

@[simp] lemma compacts.finset_sup_val {β} {K : β → compacts α} {s : finset β} :
  (s.sup K).1 = s.sup (λ x, (K x).1) :=
subtype.sup_val _ _

instance compacts.inhabited : inhabited (compacts α) := ⟨⊥⟩

/-- The compact sets with nonempty interior of a topological space. See also `compacts` and
  `nonempty_compacts`. -/
@[nolint has_inhabited_instance]
def positive_compacts (α : Type*) [topological_space α] : Type* :=
{ s : set α // compact s ∧ (interior s).nonempty  }

/-- The open neighborhoods of a point. See also `opens`. -/
def open_nhds_of {α : Type*} [topological_space α] (x : α) : Type* :=
{ s : set α // is_open s ∧ x ∈ s }

instance open_nhds_of.inhabited {α : Type*} [topological_space α] (x : α) :
  inhabited (open_nhds_of x) := ⟨⟨set.univ, is_open_univ, mem_univ _⟩⟩

/-- Given an open neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
lemma exists_nhds_square {s : set (α × α)} (hs : is_open s) {x : α} (hx : (x, x) ∈ s) :
  ∃U, is_open U ∧ x ∈ U ∧ set.prod U U ⊆ s :=
begin
  rcases is_open_prod_iff.mp hs x x hx with ⟨u, v, hu, hv, h1x, h2x, h2s⟩,
  refine ⟨u ∩ v, is_open_inter hu hv, ⟨h1x, h2x⟩, subset.trans _ h2s⟩,
  simp only [prod_subset_prod_iff, inter_subset_left, true_or, inter_subset_right, and_self],
end

/-- Given a open neighborhood `U` of `1` there is a open neighborhood `V` of `1`
  such that `VV ⊆ U`. -/
lemma one_open_separated_mul [group α] [topological_group α] {U : set α}
  (h1U : is_open U) (h2U : (1 : α) ∈ U) : ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ V.mul V ⊆ U :=
begin
  rcases exists_nhds_square (continuous_mul U h1U) (by simp only [mem_preimage, one_mul, h2U] :
    ((1 : α), (1 : α)) ∈ (λ p : α × α, p.1 * p.2) ⁻¹' U) with ⟨V, h1V, h2V, h3V⟩,
  refine ⟨V, h1V, h2V, _⟩,
  rwa [← image_subset_iff, mul_image_prod] at h3V
end

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
lemma compact_open_separated_mul [group α] [topological_group α] {K U : set α} (hK : compact K)
  (hU : is_open U) (hKU : K ⊆ U) : ∃ V : set α, is_open V ∧ (1 : α) ∈ V ∧ K.mul V ⊆ U :=
begin
  let W : α → set α := λ x, (λ y, x * y) ⁻¹' U,
  have h1W : ∀ x, is_open (W x) := λ x, continuous_mul_left x U hU,
  have h2W : ∀ x ∈ K, (1 : α) ∈ W x := λ x hx, by simp only [mem_preimage, mul_one, hKU hx],
  choose V hV using λ x : K, one_open_separated_mul (h1W x) (h2W x.1 x.2),
  let X : K → set α := λ x, (λ y, x.1⁻¹ * y) ⁻¹' (V x),
  cases hK.elim_finite_subcover X (λ x, continuous_mul_left x⁻¹ (V x) (hV x).1) _ with t ht, swap,
  { intros x hx, rw [mem_Union], use ⟨x, hx⟩, rw [mem_preimage], convert (hV _).2.1,
    simp only [mul_left_inv] },
  refine ⟨⋂ x ∈ t, V x, is_open_bInter (finite_mem_finset _) (λ x hx, (hV x).1), _, _⟩,
  { simp only [mem_Inter], intros x hx, exact (hV x).2.1 },
  rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩, simp only [mem_Inter] at hy,
  have := ht hx, simp only [mem_Union, mem_preimage] at this, rcases this with ⟨z, h1z, h2z⟩,
  have : (z : α)⁻¹ * x * y ∈ W z := (hV z).2.2 (mul_mem_mul h2z (hy z h1z)),
  rw [mem_preimage] at this, convert this, simp only [mul_assoc, mul_inv_cancel_left]
end

/-- In a locally compact space, every point has an open neighborhood with compact closure -/
lemma exists_open_with_compact_closure [locally_compact_space α] [t2_space α] (x : α) :
  ∃ (U : set α), is_open U ∧ x ∈ U ∧ compact (closure U) :=
begin
  rcases locally_compact_space.local_compact_nhds x set.univ filter.univ_mem_sets with
    ⟨K, h1K, _, h2K⟩,
  rw [mem_nhds_sets_iff] at h1K, rcases h1K with ⟨t, h1t, h2t, h3t⟩,
  exact ⟨t, h2t, h3t, compact_of_is_closed_subset h2K is_closed_closure $
    closure_minimal h1t $ closed_of_compact K h2K⟩,
end

/-- In a locally compact space, every compact set is contained in the interior of a compact set. -/
lemma exists_compact_superset [locally_compact_space α] [t2_space α] {K : set α}
  (hK : compact K) : ∃ (K' : set α), compact K' ∧ K ⊆ interior K' :=
begin
  choose U hU using λ x : K, exists_open_with_compact_closure (x : α),
  rcases hK.elim_finite_subcover U (λ x, (hU x).1) (λ x hx, ⟨_, ⟨⟨x, hx⟩, rfl⟩, (hU ⟨x, hx⟩).2.1⟩) with
    ⟨s, hs⟩,
  refine ⟨⋃ (i : K) (H : i ∈ s), closure (U i), _, _⟩,
  exact (finite_mem_finset s).compact_bUnion (λ x hx, (hU x).2.2),
  refine subset.trans hs _, rw subset_interior_iff_subset_of_open,
  exact bUnion_subset_bUnion_right (λ x hx, subset_closure),
  exact is_open_bUnion (λ x hx, (hU x).1)
end



end topological_space

section compact
variables {α : Type*} [topological_space α]


/-- If a compact set is covered by two open sets, then we can cover it by two compact subsets. -/
lemma compact.binary_compact_cover [t2_space α] {K U V : set α} (hK : compact K)
  (hU : is_open U) (hV : is_open V) (h2K : K ⊆ U ∪ V) :
  ∃ K₁ K₂ : set α, compact K₁ ∧ compact K₂ ∧ K₁ ⊆ U ∧ K₂ ⊆ V ∧ K = K₁ ∪ K₂ :=
begin
  rcases compact_compact_separated (compact_diff hK hU) (compact_diff hK hV)
    (by rwa [diff_inter_diff, diff_eq_empty]) with ⟨O₁, O₂, h1O₁, h1O₂, h2O₁, h2O₂, hO⟩,
  refine ⟨_, _, compact_diff hK h1O₁, compact_diff hK h1O₂,
    by rwa [diff_subset_comm], by rwa [diff_subset_comm], by rw [← diff_inter, hO, diff_empty]⟩
end

-- /-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
-- lemma compact.finite_compact_cover {s : set α} {ι : Type v} [fintype ι] (hs : compact s)
--   (U : ι → set α) (hUo : ∀i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) :
--   ∃ K : ι → set α, (∀ i, K i ⊆ U i ∧ compact (K i)) ∧ s = ⋃ i, K i :=
-- begin

-- end

lemma compact.inter [t2_space α] {s t : set α} (hs : compact s) (ht : compact t) :
  compact (s ∩ t) :=
hs.inter_right $ closed_of_compact t ht

end compact

namespace topological_space

variables {α : Type*} [topological_space α]
variables {ι : Type*} {π : ι → Type*} [∀i, topological_space (π i)]


/-- A version of Tychonoff's theorem that uses `set.pi`. -/
lemma compact_univ_pi {s : Πi:ι, set (π i)} (h : ∀i, compact (s i)) : compact (set.pi set.univ s) :=
by { convert compact_pi_infinite h, simp only [pi, forall_prop_of_true, mem_univ] }

lemma bUnion_finset_empty {α β} {g : α → set β} : (⋃x ∈ (∅ : finset α), g x) = ∅ :=
by simp

/-- For every finite open cover `Uᵢ` of a compact set, there exists a compact cover `Kᵢ ⊆ Uᵢ`. -/
lemma compact.finite_compact_cover [t2_space α] {s : set α} (hs : compact s) {ι} (t : finset ι)
  (U : ι → opens α) (hsC : s ⊆ ⋃ i ∈ t, (U i).1) :
  ∃ K : ι → compacts α, (∀ i ∈ t, (K i).1 ⊆ (U i).1) ∧ s = ⋃ i ∈ t, (K i).1 :=
begin
  classical, revert U s hs hsC,
  refine finset.induction _ _ t,
  { intros, refine ⟨λ _, ⊥, λ i _, empty_subset _, _⟩, simpa only [subset_empty_iff,
      finset.not_mem_empty, Union_neg, Union_empty, not_false_iff] using hsC },
  intros x t hx ih U s hs hsC, simp only [finset.bUnion_insert] at hsC,
  rcases hs.binary_compact_cover (U x).2 (is_open_bUnion $ λ i ∈ t, (U i).2) hsC
    with ⟨K₁, K₂, h1K₁, h1K₂, h2K₁, h2K₂, hK⟩,
  rcases ih U h1K₂ h2K₂ with ⟨K, h1K, h2K⟩,
  refine ⟨update K x ⟨K₁, h1K₁⟩, _, _⟩,
  { intros i hi, simp only [finset.mem_insert] at hi, rcases hi with rfl|hi,
    simpa only [update_same] using h2K₁,
    rw [update_noteq], exact h1K i hi, rintro rfl, exact hx hi },
  { ext y, simp only [exists_prop, mem_Union, mem_union_eq, finset.bUnion_insert, update_same, hK],
    split,
    { rintro (hy|hy), exact or.inl hy,
      simp only [h2K, mem_Union, subtype.exists] at hy, rcases hy with ⟨i, h1i, h2i⟩,
      refine or.inr ⟨i, h1i, _⟩, rw [update_noteq], exact h2i, rintro rfl, exact hx h1i },
    { rintro (hy|⟨i, h1i, h2i⟩), exact or.inl hy,
      rw [h2K], simp only [exists_prop, mem_Union], rw [update_noteq] at h2i,
      exact or.inr ⟨i, h1i, h2i⟩, rintro rfl, exact hx h1i }}
end

namespace opens

lemma supr_def {ι} (s : ι → opens α) : (⨆ i, s i) = ⟨⋃ i, s i, is_open_Union $ λ i, (s i).2⟩ :=
by { ext1, simp only [supr, Sup_s, sUnion_image, bUnion_range], refl }

end opens

end topological_space
open topological_space
-- open_locale topology


section
-- lemma generate_from_compacts {α : Type u} [topological_space α] :
--   measurable_space.generate_from {K : set α | compact K} = borel α :=
-- begin
--   ext, split; refine generate_from_le _ s,
--   { intros K hK, sorry },
--   { intros U hU, sorry }
-- end

variables {α : Type u} [measurable_space α]
          {β : Type v} [measurable_space β]

variables [topological_space α] [borel_space α]
lemma compact.is_measurable [t2_space α] {s : set α} (h : compact s) : is_measurable s :=
(closed_of_compact _ h).is_measurable
end

namespace ennreal

variable {α : Type*}
protected lemma sum_le_tsum {f : α → ennreal} (s : finset α) : s.sum f ≤ tsum f :=
sum_le_tsum s (λ x hx, zero_le _) ennreal.summable


-- lemma add_supr_le {ι} [nonempty ι] {s : ι → ennreal} {x y : ennreal} (h : ∀i, x + s i ≤ y) :
--   x + supr s ≤ y :=
-- begin
--   rw [add_supr], refine supr_le h
-- end

end ennreal

namespace measure_theory

variables {α : Type u} [measurable_space α]

/-- A measure is nonzero if it is not 0 on the whole space. -/
def measure.nonzero (μ : measure α) : Prop :=
μ set.univ > 0

variable [topological_space α]

/-- A regular borel measure. -/
structure measure.regular (μ : measure α) : Prop :=
  (le_top_of_compact : ∀ {{K : set α}}, compact K → μ K < ⊤)
  (outer_regular : ∀ {{A : set α}}, is_measurable A →
    (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) ≤ μ A)
  (inner_regular : ∀ {{U : set α}}, is_open U →
    μ U ≤ ⨆ (K : set α) (h : compact K) (h2 : K ⊆ U), μ K)

lemma measure.regular.outer_regular_eq {μ : measure α} (hμ : μ.regular) {{A : set α}}
  (hA : is_measurable A) : (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) = μ A :=
le_antisymm (hμ.outer_regular hA) $ le_infi $ λ s, le_infi $ λ hs, le_infi $ λ h2s, μ.mono h2s

lemma measure.regular.inner_regular_eq {μ : measure α} (hμ : μ.regular) {{U : set α}}
  (hU : is_open U) : (⨆ (K : set α) (h : compact K) (h2 : K ⊆ U), μ K) = μ U :=
le_antisymm (supr_le $ λ s, supr_le $ λ hs, supr_le $ λ h2s, μ.mono h2s) (hμ.inner_regular hU)

variables {G : Type w}

section

variables [measurable_space G] [group G]

/-- A measure `μ` on a topological group is left invariant if
  for all measurable sets `s` and all `g`, we have `μ (gs) = μ s`,
  where `gs` denotes the translate of `s` by left multiplication with `g`. -/
def is_left_invariant (μ : measure G) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, g * h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant if
  for all measurable sets `s` and all `g`, we have `μ (sg) = μ s`,
  where `sg` denotes the translate of `s` by right multiplication with `g`. -/
def is_right_invariant (μ : measure G) : Prop :=
∀ (g : G) {A : set G} (h : is_measurable A), μ ((λ h, h * g) ⁻¹' A) = μ A

end

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

namespace outer_measure

lemma le_inter_add_diff {α} {m : outer_measure α} {t : set α} (s : set α) :
  m t ≤ m (t ∩ s) + m (t \ s) :=
by { convert m.union _ _, rw inter_union_diff t s }

section extend
variables [topological_space G]

/-! In this section we work with *contents*. A content is a function from a certain class of subsets
  to `ennreal` (or `nnreal`) that is additive, subadditive and monotone.
  In this section, we show:
  * Given a content `λ` on compact sets, we get a countably subadditive map that vanishes at `∅`.
    In Halmos (1950) this is called the *inner content* `λ*` of `λ`.
  * Given an inner content, we get an outer measure
-/

/-- Constructing the inner content of a content. -/
def inner_content (μ : compacts G → ennreal) (U : opens G) : ennreal :=
⨆ (K : compacts G) (h : K.1 ⊆ U.1), μ K

lemma le_inner_content {μ : compacts G → ennreal} (K : compacts G) (U : opens G)
  (h2 : K.1 ⊆ U.1) : μ K ≤ inner_content μ U :=
le_supr_of_le K $ le_supr _ h2

lemma inner_content_le {μ : compacts G → ennreal}
  (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (U : opens G) (K : compacts G)
  (h2 : U.1 ⊆ K.1) : inner_content μ U ≤ μ K :=
supr_le $ λ K', supr_le $ λ hK', h _ _ (subset.trans hK' h2)

lemma inner_content_of_compact {μ : compacts G → ennreal}
  (h : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂) {K : set G} (h1K : compact K)
  (h2K : is_open K) : inner_content μ ⟨K, h2K⟩ = μ ⟨K, h1K⟩ :=
le_antisymm (supr_le $ λ K', supr_le $ λ hK', h _ ⟨K, h1K⟩ hK')
            (le_inner_content _ _ subset.rfl)

lemma inner_content_empty {μ : compacts G → ennreal} (h : μ ⊥ = 0) :
  inner_content μ ∅ = 0 :=
begin
  refine le_antisymm _ (zero_le _), rw ←h,
  refine supr_le (λ K, supr_le (λ hK, _)),
  have : K = ⊥, { ext1, rw [subset_empty_iff.mp hK, compacts.bot_val] }, rw this, refl'
end

lemma inner_content_mono {μ : compacts G → ennreal} {{U V : opens G}} (h2 : U.1 ⊆ V.1) :
  inner_content μ U ≤ inner_content μ V :=
supr_le_supr $ λ K, supr_le_supr_const $ λ hK, subset.trans hK h2

lemma inner_content_exists_compact {μ : compacts G → ennreal} {U : opens G}
  (hU : inner_content μ U < ⊤) {ε : nnreal} (hε : ε > 0) :
  ∃ K : compacts G, K.1 ⊆ U.1 ∧ inner_content μ U ≤ μ K + ε :=
begin
  have h'ε := ennreal.zero_lt_coe_iff.2 hε,
  cases le_or_lt (inner_content μ U) ε,
  { exact ⟨⊥, empty_subset _, le_trans h (le_add_of_nonneg_left' (zero_le _))⟩ },
  have := ennreal.sub_lt_sub_self (ne_of_lt hU) (ne_of_gt $ lt_trans h'ε h) h'ε,
  conv at this {to_rhs, rw inner_content }, simp only [lt_supr_iff] at this,
  rcases this with ⟨U, h1U, h2U⟩, refine ⟨U, h1U, _⟩,
  rw [← ennreal.sub_le_iff_le_add], exact le_of_lt h2U
end

lemma inner_content_Union_nat [t2_space G] {μ : compacts G → ennreal}
  (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) (U : ℕ → opens G) :
  inner_content μ (⨆ (i : ℕ), U i) ≤ ∑' (i : ℕ), inner_content μ (U i) :=
begin
  have h3 : ∀ (t : finset ℕ) (K : ℕ → compacts G), μ (t.sup K) ≤ t.sum (λ i, μ (K i)),
  { intros t K, refine finset.induction_on t _ _,
    { simp only [h1, le_zero_iff_eq, finset.sum_empty, finset.sup_empty] },
    { intros n s hn ih, rw [finset.sup_insert, finset.sum_insert hn],
      exact le_trans (h2 _ _) (add_le_add_left' ih) }},
  refine supr_le (λ K, supr_le (λ hK, _)),
  rcases compact.elim_finite_subcover K.2 _ (λ i, (U i).2) _ with ⟨t, ht⟩, swap,
  { convert hK, rw [opens.supr_def], refl },
  rcases compact.finite_compact_cover K.2 t U (by simp only [ht]) with ⟨K', h1K', h2K'⟩,
  convert le_trans (h3 t K') _, { ext1, rw [h2K', compacts.finset_sup_val, finset.sup_eq_supr] },
  refine le_trans (finset.sum_le_sum _) (ennreal.sum_le_tsum t),
  intros i hi, refine le_trans _ (le_supr _ (K' i)),
  refine le_trans (by refl') (le_supr _ (h1K' i hi))
end

/-- Extending an "inner content" on opens to an outer measure on all sets.
  This is only the underlying function.

  Remark: this is very similar to `outer_measure.of_function μ` (where we treat values where
  `μ` is undefined as `⊤`). -/
def of_inner_content_def (μ : opens G → ennreal) (A : set G) : ennreal :=
⨅ (U : opens G) (h : A ⊆ U), μ U

lemma of_inner_content_le_opens {μ : opens G → ennreal} (U : opens G) :
  of_inner_content_def μ U ≤ μ U :=
infi_le_of_le U (infi_le _ subset.rfl)

/-- We prove a second version of the previous lemma, because even though the previous lemma applies
  in this case, applying it will take 10+ seconds to unify, presumably because it unfolds all
  definitions involving (enn)reals. -/
lemma of_inner_content_le_of_is_open {μ : opens G → ennreal}
  {U : set G} (hU : is_open U) : of_inner_content_def μ U ≤ μ ⟨U, hU⟩ :=
infi_le_of_le ⟨U, hU⟩ (infi_le _ subset.rfl)

lemma of_inner_content_of_is_open {μ : opens G → ennreal}
  (h : ∀ (U V : opens G), U.1 ⊆ V.1 → μ U ≤ μ V) {U : set G} (hU : is_open U) :
  of_inner_content_def μ U = μ ⟨U, hU⟩ :=
le_antisymm (infi_le_of_le ⟨U, hU⟩ (infi_le _ subset.rfl))
            (le_infi (λ V, le_infi $ λ hV, h ⟨U, hU⟩ _ hV))

/-- We prove a second version of the previous lemma, because even though the previous lemma applies
  in this case, applying it will take 10+ seconds to unify, presumably because it unfolds all
  definitions involving (enn)reals. -/
lemma of_inner_content_opens {μ : opens G → ennreal}
  (h : ∀ (U V : opens G), U.1 ⊆ V.1 → μ U ≤ μ V) (U : opens G) :
  of_inner_content_def μ U = μ U :=
le_antisymm (infi_le_of_le U (infi_le _ subset.rfl))
            (le_infi (λ V, le_infi $ λ hV, h U _ hV))

lemma of_inner_content_empty {μ : opens G → ennreal} (h : μ ∅ = 0) :
  of_inner_content_def μ ∅ = 0 :=
begin
  refine le_antisymm _ (zero_le _), rw ←h,
  exact infi_le_of_le ∅ (infi_le _ subset.rfl)
end

lemma of_inner_content_mono {μ : opens G → ennreal}
  {{A B : set G}} (h2 : A ⊆ B) : of_inner_content_def μ A ≤ of_inner_content_def μ B :=
infi_le_infi $ λ U, infi_le_infi_const (subset.trans h2)

lemma of_inner_content_exists_open' {μ : opens G → ennreal} {A : set G}
  (hA : of_inner_content_def μ A < ⊤) {ε : nnreal} (hε : ε > 0) :
  ∃ U : opens G, A ⊆ U ∧ μ U ≤ of_inner_content_def μ A + ε :=
begin
  have := ennreal.lt_add_right hA (ennreal.zero_lt_coe_iff.2 hε),
  conv at this {to_lhs, rw of_inner_content_def }, simp only [infi_lt_iff] at this,
  rcases this with ⟨U, h1U, h2U⟩, exact ⟨U, h1U, le_of_lt h2U⟩
end

lemma of_inner_content_exists_open {μ : opens G → ennreal} {A : set G}
  (hA : of_inner_content_def μ A < ⊤) {ε : nnreal} (hε : ε > 0) :
  ∃ U : opens G, A ⊆ U ∧ of_inner_content_def μ U ≤ of_inner_content_def μ A + ε :=
begin
  rcases of_inner_content_exists_open' hA hε with ⟨U, h1U, h2U⟩,
  refine ⟨U, h1U, le_trans (of_inner_content_le_opens U) h2U⟩
end

lemma of_inner_content_Union_nat {μ : opens G → ennreal}
  (h2 : ∀ (s : ℕ → opens G), μ (⨆ (i : ℕ), s i) ≤ ∑' (i : ℕ), μ (s i)) (s : ℕ → set G) :
  of_inner_content_def μ (⋃ (i : ℕ), s i) ≤ ∑' (i : ℕ), of_inner_content_def μ (s i) :=
begin
  apply ennreal.le_of_forall_epsilon_le, intros ε hε h3,
  rcases ennreal.exists_pos_sum_of_encodable (ennreal.zero_lt_coe_iff.2 hε) ℕ with ⟨ε', hε', h2ε'⟩,
  refine le_trans _ (add_le_add_left' (le_of_lt h2ε')),
  rw ← ennreal.tsum_add,
  have : ∀ i, ∃ U : opens G, s i ⊆ U ∧ μ U ≤ of_inner_content_def μ (s i) + ε' i :=
    λ i, of_inner_content_exists_open' (lt_of_le_of_lt (by exact ennreal.le_tsum i) h3) (hε' i),
  choose U hU using this,
  refine le_trans (of_inner_content_mono (Union_subset_Union (λ i, (hU i).1))) _,
  refine le_trans (of_inner_content_le_of_is_open $ is_open_Union (λ i, (U i).property)) _,
  rw ← opens.supr_def, refine le_trans (h2 _) _, convert ennreal.tsum_le_tsum (λ i, (hU i).2)
end

/-- Extending a inner content on opens to an outer measure. -/
def of_inner_content (μ : opens G → ennreal) (h1 : μ ∅ = 0)
  (h2 : ∀ (s : ℕ → opens G), μ (⨆ (i : ℕ), s i) ≤ ∑' (i : ℕ), μ (s i)) : outer_measure G :=
{ measure_of := of_inner_content_def μ,
  empty := of_inner_content_empty h1,
  mono := of_inner_content_mono,
  Union_nat := of_inner_content_Union_nat h2 }

lemma of_inner_content_caratheodory {μ : opens G → ennreal} {h1 : μ ∅ = 0}
  {h2 : ∀ (s : ℕ → opens G), μ (⨆ (i : ℕ), s i) ≤ ∑' (i : ℕ), μ (s i)} (A : set G) :
  (of_inner_content μ h1 h2).caratheodory.is_measurable A ↔ ∀ (U : opens G),
  of_inner_content μ h1 h2 (U ∩ A) + of_inner_content μ h1 h2 (U \ A) ≤ of_inner_content μ h1 h2 U :=
begin
  split,
  { intros h U, exact ge_of_eq (h U) },
  { intros h B, refine le_antisymm (le_inter_add_diff _) _,
    refine le_infi _, intro U, refine le_infi _, intro hU,
    refine le_trans _ (le_trans (h U) $ of_inner_content_le_opens _),
    refine add_le_add' (of_inner_content_mono $ inter_subset_inter_left _ hU)
      (of_inner_content_mono $ diff_subset_diff_left hU) }
end

/-- Extending a "measure" on compact sets to an outer_measure on all sets. -/
def of_content [t2_space G] (μ : compacts G → ennreal) (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) : outer_measure G :=
of_inner_content
  (inner_content μ)
  (inner_content_empty h1)
  (inner_content_Union_nat h1 h2)

variables [t2_space G] {μ : compacts G → ennreal} {h1 : μ ⊥ = 0}
  {h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂}

lemma of_content_opens (U : opens G) : of_content μ h1 h2 U = inner_content μ U :=
of_inner_content_opens inner_content_mono U

lemma le_of_content_compacts (K : compacts G) : μ K ≤ of_content μ h1 h2 K.1 :=
le_infi $ λ U, le_infi $ le_inner_content K U

lemma of_content_interior_compacts (h3 : ∀ (K₁ K₂ : compacts G), K₁.1 ⊆ K₂.1 → μ K₁ ≤ μ K₂)
  (K : compacts G) : of_content μ h1 h2 (interior K.1) ≤ μ K :=
le_trans (le_of_eq (of_content_opens ⟨interior K.1, is_open_interior⟩))
         (inner_content_le h3 _ _ interior_subset)

lemma of_content_exists_compact {μ : compacts G → ennreal} (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) {U : opens G}
  (hU : of_content μ h1 h2 U < ⊤) {ε : nnreal} (hε : ε > 0) : ∃ K : compacts G,
  K.1 ⊆ U.1 ∧ of_content μ h1 h2 U ≤ of_content μ h1 h2 K.1 + ε :=
begin
  rw [of_content_opens] at hU ⊢,
  rcases inner_content_exists_compact hU hε with ⟨K, h1K, h2K⟩,
  exact ⟨K, h1K, le_trans h2K $ add_le_add_right' $ le_of_content_compacts K⟩
end

lemma of_content_exists_open {μ : compacts G → ennreal} (h1 : μ ⊥ = 0)
  (h2 : ∀ (K₁ K₂ : compacts G), μ (K₁ ⊔ K₂) ≤ μ K₁ + μ K₂) {A : set G}
  (hA : of_content μ h1 h2 A < ⊤) {ε : nnreal} (hε : ε > 0) :
  ∃ U : opens G, A ⊆ U ∧ of_content μ h1 h2 U ≤ of_content μ h1 h2 A + ε :=
of_inner_content_exists_open hA hε

end extend
end outer_measure

namespace measure

/-- The conjugate of a measure on a topological group. -/
protected def conj [measurable_space G] [group G] (μ : measure G) : measure G :=
μ.map inv

variables [measurable_space G] [group G] [topological_space G] [topological_group G] [borel_space G]

lemma conj_apply (μ : measure G) {s : set G} (hs : is_measurable s) :
  μ.conj s = μ s.inv :=
by { unfold measure.conj, rw [measure.map_apply measurable_inv hs, inv_preimage] }

@[simp] lemma conj_conj (μ : measure G) : μ.conj.conj = μ :=
begin
  ext1 s hs, rw [μ.conj.conj_apply hs, μ.conj_apply, set.inv_inv], exact measurable_inv.preimage hs
end

variables {μ : measure G}

lemma nonzero.conj (h : μ.nonzero) : μ.conj.nonzero :=
by { dsimp only [nonzero], rwa [μ.conj_apply is_measurable.univ, set.univ_inv] }

lemma regular.conj [t2_space G] (h : μ.regular) : μ.conj.regular :=
begin
  split,
  { intros K hK, rw [μ.conj_apply hK.is_measurable], apply h.le_top_of_compact,
    exact (homeomorph.inv G).compact_preimage.mpr hK },
  { intros A hA, rw [μ.conj_apply hA, ← h.outer_regular_eq],
    refine le_of_eq _, apply infi_congr (preimage inv) (equiv.inv G).injective.surjective_preimage,
    intro U, apply infi_congr_Prop (homeomorph.inv G).is_open_preimage, intro hU,
    apply infi_congr_Prop,
    { apply preimage_subset_preimage_iff, rw [surjective.range_eq], apply subset_univ,
      exact (equiv.inv G).surjective },
    intro h2U, rw [μ.conj_apply hU.is_measurable, inv_preimage],
    exact measurable_inv.preimage hA },
  { intros U hU, rw [μ.conj_apply hU.is_measurable, ← h.inner_regular_eq],
    refine ge_of_eq _,
    apply supr_congr (preimage inv) (equiv.inv G).injective.surjective_preimage,
    intro K, apply supr_congr_Prop (homeomorph.inv G).compact_preimage, intro hK,
    apply supr_congr_Prop,
    { apply preimage_subset_preimage_iff, rw [surjective.range_eq], apply subset_univ,
      exact (equiv.inv G).surjective },
    intro h2U, rw [μ.conj_apply hK.is_measurable, inv_preimage],
    exact continuous_inv U hU },
end

end measure

section conj
variables [measurable_space G] [group G] [topological_space G] [topological_group G] [borel_space G]
  {μ : measure G}

@[simp] lemma regular_conj_iff [t2_space G] : μ.conj.regular ↔ μ.regular :=
by { refine ⟨λ h, _, measure.regular.conj⟩, rw ←μ.conj_conj, exact measure.regular.conj h }

lemma is_right_invariant_conj' (h : is_left_invariant μ) :
  is_right_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_right g A hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv A hA) using 2,
  simp only [←preimage_comp, set.inv], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv]
end

lemma is_left_invariant_conj' (h : is_right_invariant μ) : is_left_invariant μ.conj :=
begin
  intros g A hA, rw [μ.conj_apply (measurable_mul_left g A hA), μ.conj_apply hA],
  convert h g⁻¹ (measurable_inv A hA) using 2,
  simp only [←preimage_comp, set.inv], congr' 1, ext h, simp only [mul_inv_rev, comp_app, inv_inv]
end

@[simp] lemma is_right_invariant_conj : is_right_invariant μ.conj ↔ is_left_invariant μ :=
by { refine ⟨λ h, _, is_right_invariant_conj'⟩, rw ←μ.conj_conj, exact is_left_invariant_conj' h }

@[simp] lemma is_left_invariant_conj : is_left_invariant μ.conj ↔ is_right_invariant μ :=
by { refine ⟨λ h, _, is_left_invariant_conj'⟩, rw ←μ.conj_conj, exact is_right_invariant_conj' h }

end conj

/- we put the construction of the Haar measure in a namespace to partially hide it -/
namespace haar

variables [group G]

/-- The index or Haar covering number(?) of `K` w.r.t. `V`, denoted `(K : V)` -/
def index (K V : set G) : ℕ :=
Inf $ finset.card '' {t : finset G | K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V }

lemma index_empty {V : set G} : index ∅ V = 0 :=
begin
  simp only [index, nat.Inf_eq_zero], left, use ∅,
  simp only [finset.card_empty, empty_subset, mem_set_of_eq, eq_self_iff_true, and_self],
end

variables [topological_space G]

/-- prehaar -/
-- in notes: K₀ compact with non-empty interior, U open containing 1, K compact
def prehaar (K₀ U : set G) (K : compacts G) : ℝ := (index K.1 U : ℝ) / index K₀ U

/-- haar_product X -/
def haar_product (K₀ : set G) : set (compacts G → ℝ) :=
set.pi set.univ (λ K, Icc 0 $ index K.1 K₀)

/-- The closure of `{ prehaar K₀ U }` for `U` open neighbourhoods of `1`, contained in `V`. -/
def cl_prehaar (K₀ : set G) (V : open_nhds_of (1 : G)) : set (compacts G → ℝ) :=
closure $ prehaar K₀ '' { U : set G | U ⊆ V.1 ∧ is_open U ∧ (1 : G) ∈ U }

lemma prehaar_empty (K₀ : positive_compacts G) {U : set G} : prehaar K₀.1 U ⊥ = 0 :=
by { simp only [prehaar, compacts.bot_val, index_empty, nat.cast_zero, euclidean_domain.zero_div] }

variables [topological_group G]

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

lemma index_pos (K : positive_compacts G) {V : set G} (hV : (interior V).nonempty) :
  0 < index K.1 V :=
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

lemma index_union_le (K₁ K₂ : compacts G) {V : set G} (hV : (interior V).nonempty) :
  index (K₁.1 ∪ K₂.1) V ≤ index K₁.1 V + index K₂.1 V :=
begin
  classical,
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩,
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩,
  rw [← h2s, ← h2t],
  refine le_trans _ (finset.card_union_le _ _),
  apply nat.Inf_le, refine ⟨_, _, rfl⟩, rw [mem_set_of_eq],
  apply union_subset; refine subset.trans (by assumption) _; apply bUnion_subset_bUnion_left;
    intros g hg; simp only [mem_def] at hg;
    simp only [mem_def, multiset.mem_union, finset.union_val, hg, or_true, true_or]
end

lemma index_union_eq (K₁ K₂ : compacts G) {V : set G} (hV : (interior V).nonempty)
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
    simp only [mem_Union], use g₀, split,
    { simp only [finset.mem_filter, h1g₀, true_and], use g,
      simp only [hg, h2g₀, mem_inter_eq, mem_preimage, and_self] },
    exact h2g₀ },
  refine le_trans (add_le_add (this K₁.1 $ subset.trans (subset_union_left _ _) h1s)
    (this K₂.1 $ subset.trans (subset_union_right _ _) h1s)) _,
  rw [← finset.card_union_eq, finset.filter_union_right],
  { apply finset.card_le_of_subset, apply finset.filter_subset },
  apply finset.disjoint_filter.mpr,
  rintro g₁ h1g₁ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩,
  simp only [mem_preimage] at h1g₃ h1g₂,
  apply @h g₁⁻¹,
  split; simp only [set.mem_inv, set.mem_mul, exists_exists_and_eq_and, exists_and_distrib_left],
  { refine ⟨_, h2g₂, (g₁ * g₂)⁻¹, _, _⟩, simp only [inv_inv, h1g₂],
    simp only [mul_inv_rev, mul_inv_cancel_left] },
  { refine ⟨_, h2g₃, (g₁ * g₃)⁻¹, _, _⟩, simp only [inv_inv, h1g₃],
    simp only [mul_inv_rev, mul_inv_cancel_left] }
end

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

lemma prehaar_mono {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty)
  {K₁ K₂ : compacts G} (h : K₁.1 ⊆ K₂.1) : prehaar K₀.1 U K₁ ≤ prehaar K₀.1 U K₂ :=
begin
  simp only [prehaar], rw [div_le_div_right], exact_mod_cast index_mono K₂.2 h hU,
  exact_mod_cast index_pos K₀ hU
end

lemma prehaar_self {K₀ : positive_compacts G} {U : set G} (hU : (interior U).nonempty) :
  prehaar K₀.1 U ⟨K₀.1, K₀.2.1⟩ = 1 :=
by { simp only [prehaar], rw [div_self], apply ne_of_gt, exact_mod_cast index_pos K₀ hU }

lemma prehaar_sup_le {K₀ : positive_compacts G} {U : set G} (K₁ K₂ : compacts G)
  (hU : (interior U).nonempty) : prehaar K₀.1 U (K₁ ⊔ K₂) ≤ prehaar K₀.1 U K₁ + prehaar K₀.1 U K₂ :=
begin
  simp only [prehaar], rw [div_add_div_same, div_le_div_right],
  exact_mod_cast index_union_le K₁ K₂ hU, exact_mod_cast index_pos K₀ hU
end

lemma prehaar_sup_eq {K₀ : positive_compacts G} {U : set G} {K₁ K₂ : compacts G}
  (hU : (interior U).nonempty) (h : disjoint (K₁.1.mul U.inv) (K₂.1.mul U.inv)) :
  prehaar K₀.1 U (K₁ ⊔ K₂) = prehaar K₀.1 U K₁ + prehaar K₀.1 U K₂ :=
by { simp only [prehaar], rw [div_add_div_same], congr' 1, exact_mod_cast index_union_eq K₁ K₂ hU h }

lemma prehaar_mem_haar_product (K₀ : positive_compacts G) {U : set G}
  (hU : (interior U).nonempty) : prehaar K₀.1 U ∈ haar_product K₀.1 :=
by { rintro ⟨K, hK⟩ h2K, rw [mem_Icc],
     exact ⟨prehaar_nonneg K₀ _ hU, prehaar_le_index K₀ _ hU⟩ }

lemma nonempty_Inter_cl_prehaar (K₀ : positive_compacts G) :
  (haar_product K₀.1 ∩ ⋂ (V : open_nhds_of (1 : G)), cl_prehaar K₀.1 V).nonempty :=
begin
  have : compact (haar_product K₀.1), { apply compact_univ_pi, intro K, apply compact_Icc },
  rw [← ne_empty_iff_nonempty],
  have := compact.elim_finite_subfamily_closed this (cl_prehaar K₀.1) (λ s, is_closed_closure),
  apply mt this, rintro ⟨t, h1t⟩, rw [← not_nonempty_iff_eq_empty] at h1t, apply h1t,
  let V₀ := ⋂ (V ∈ t), (V : open_nhds_of 1).1,
  have h1V₀ : is_open V₀,
  { apply is_open_bInter, apply finite_mem_finset, rintro ⟨V, hV⟩ h2V, exact hV.1 },
  have h2V₀ : (1 : G) ∈ V₀, { simp only [mem_Inter], rintro ⟨V, hV⟩ h2V, exact hV.2 },
  refine ⟨prehaar K₀.1 V₀, _⟩,
  split,
  { apply prehaar_mem_haar_product K₀, use 1, rwa interior_eq_of_open h1V₀ },
  { simp only [mem_Inter], rintro ⟨V, hV⟩ h2V, apply subset_closure,
    apply mem_image_of_mem, rw [mem_set_of_eq],
    exact ⟨subset.trans (Inter_subset _ ⟨V, hV⟩) (Inter_subset _ h2V), h1V₀, h2V₀⟩ },
end

/-- the Haar measure on compact sets -/
def chaar (K₀ : positive_compacts G) (K : compacts G) : ℝ :=
classical.some (nonempty_Inter_cl_prehaar K₀) K

lemma chaar_mem_haar_product (K₀ : positive_compacts G) : chaar K₀ ∈ haar_product K₀.1 :=
(classical.some_spec (nonempty_Inter_cl_prehaar K₀)).1

lemma chaar_mem_cl_prehaar (K₀ : positive_compacts G) (V : open_nhds_of (1 : G)) :
  chaar K₀ ∈ cl_prehaar K₀.1 V :=
by { have := (classical.some_spec (nonempty_Inter_cl_prehaar K₀)).2, rw [mem_Inter] at this,
     exact this V }

lemma chaar_nonneg (K₀ : positive_compacts G) (K : compacts G) : 0 ≤ chaar K₀ K :=
by { have := chaar_mem_haar_product K₀ K (mem_univ _), rw mem_Icc at this, exact this.1 }

lemma chaar_empty (K₀ : positive_compacts G) : chaar K₀ ⊥ = 0 :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f ⊥, have : continuous eval := continuous_apply ⊥,
  show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)},
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw closure_subset_iff_subset_of_is_closed,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, apply prehaar_empty },
  { apply continuous_iff_is_closed.mp this, exact is_closed_singleton },
end

lemma chaar_mono {K₀ : positive_compacts G} {K₁ K₂ : compacts G} (h : K₁.1 ⊆ K₂.1) :
  chaar K₀ K₁ ≤ chaar K₀ K₂ :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₂ - f K₁,
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_apply K₂) (@continuous_apply _ (λ _, ℝ) _ K₁)),
  rw [← sub_nonneg], show chaar K₀ ∈ eval ⁻¹' (Ici (0 : ℝ)),
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw closure_subset_iff_subset_of_is_closed,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, simp only [mem_preimage, mem_Ici, eval, sub_nonneg],
    apply prehaar_mono _ h, rw interior_eq_of_open h2U, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_Ici },
end

lemma chaar_sup_le {K₀ : positive_compacts G} (K₁ K₂ : compacts G) :
  chaar K₀ (K₁ ⊔ K₂) ≤ chaar K₀ K₁ + chaar K₀ K₂ :=
begin
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₁ + f K₂ - f (K₁ ⊔ K₂),
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_add.comp
      (continuous.prod_mk (continuous_apply K₁) (@continuous_apply _ (λ _, ℝ) _ K₂)))
      (@continuous_apply _ (λ _, ℝ) _(K₁ ⊔ K₂))),
  rw [← sub_nonneg], show chaar K₀ ∈ eval ⁻¹' (Ici (0 : ℝ)),
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀ ⟨set.univ, is_open_univ, mem_univ _⟩),
  unfold cl_prehaar, rw closure_subset_iff_subset_of_is_closed,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩, simp only [mem_preimage, mem_Ici, eval, sub_nonneg],
    apply prehaar_sup_le, rw interior_eq_of_open h2U, exact ⟨1, h3U⟩ },
  { apply continuous_iff_is_closed.mp this, exact is_closed_Ici },
end

lemma chaar_sup_eq [t2_space G] {K₀ : positive_compacts G} {K₁ K₂ : compacts G}
  (h : disjoint K₁.1 K₂.1) : chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ :=
begin
  rcases compact_compact_separated K₁.2 K₂.2 (disjoint_iff.mp h) with
    ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩,
  rw [← disjoint_iff_inter_eq_empty] at hU,
  rcases compact_open_separated_mul K₁.2 h1U₁ h2U₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩,
  rcases compact_open_separated_mul K₂.2 h1U₂ h2U₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩,
  let eval : (compacts G → ℝ) → ℝ := λ f, f K₁ + f K₂ - f (K₁ ⊔ K₂),
  have : continuous eval := continuous_sub.comp
    (continuous.prod_mk (continuous_add.comp
      (continuous.prod_mk (continuous_apply K₁) (@continuous_apply _ (λ _, ℝ) _ K₂)))
      (@continuous_apply _ (λ _, ℝ) _(K₁ ⊔ K₂))),
  rw [eq_comm, ← sub_eq_zero], show chaar K₀ ∈ eval ⁻¹' {(0 : ℝ)},
  let V := V₁ ∩ V₂,
  apply mem_of_subset_of_mem _ (chaar_mem_cl_prehaar K₀
    ⟨V.inv, continuous_inv V (is_open_inter h1V₁ h1V₂),
    by simp only [mem_inv, one_inv, h2V₁, h2V₂, V, mem_inter_eq, true_and]⟩),
  unfold cl_prehaar, rw closure_subset_iff_subset_of_is_closed,
  { rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩,
    simp only [mem_preimage, eval, sub_eq_zero, mem_singleton_iff], rw [eq_comm],
    apply prehaar_sup_eq,
    { rw interior_eq_of_open h2U, exact ⟨1, h3U⟩ },
    { refine disjoint_of_subset _ _ hU,
      { refine subset.trans (mul_subset_mul subset.rfl _) h3V₁,
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_left _ _) },
      { refine subset.trans (mul_subset_mul subset.rfl _) h3V₂,
        exact subset.trans (inv_subset.mpr h1U) (inter_subset_right _ _) }}},
  { apply continuous_iff_is_closed.mp this, exact is_closed_singleton },
end


-- /-- the value of the Haar measure on `G` on all open sets -/
-- def ohaar (K₀ : positive_compacts G) (U : opens G) : ennreal :=
-- ⨆ (K : compacts G) (h : K.1 ⊆ U.1), show nnreal, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩

-- lemma ohaar_eq_chaar (K₀ : positive_compacts G) {K : set G} (oK : is_open K) (cK : compact K) :
--   ohaar K₀ ⟨K, oK⟩ = show nnreal, from ⟨chaar K₀ ⟨K, cK⟩, chaar_nonneg K₀ ⟨K, cK⟩⟩ :=
-- sorry

-- /-- the value of the Haar measure on `G` on any set -/
-- def haar (K₀ : positive_compacts G) (A : set G) : ennreal :=
-- ⨅ (U : opens G) (h : A ⊆ U), ohaar K₀ U

-- lemma haar_eq_ohaar (K₀ : positive_compacts G) (K : opens G) : haar K₀ K.1 = ohaar K₀ K :=
-- sorry

end haar
open haar

variables [topological_space G] [t2_space G] [group G] [topological_group G]

/-- the Haar outer measure on `G` -/
def haar_outer_measure (K₀ : positive_compacts G) : outer_measure G :=
outer_measure.of_content
  (λ K, show nnreal, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩)
  (by { norm_cast, rw [←nnreal.coe_eq, nnreal.coe_zero, subtype.coe_mk, chaar_empty] })
  (λ K₁ K₂, by { norm_cast, simp only [←nnreal.coe_le_coe, nnreal.coe_add, subtype.coe_mk,
    chaar_sup_le] })

lemma haar_outer_measure_exists_open {K₀ : positive_compacts G} {A : set G}
  (hA : haar_outer_measure K₀ A < ⊤) {ε : nnreal} (hε : ε > 0) :
  ∃ U : opens G, A ⊆ U ∧ haar_outer_measure K₀ U ≤ haar_outer_measure K₀ A + ε :=
outer_measure.of_content_exists_open _ _ hA hε

lemma haar_outer_measure_exists_compact {K₀ : positive_compacts G} {U : opens G}
  (hU : haar_outer_measure K₀ U < ⊤) {ε : nnreal} (hε : ε > 0) :
  ∃ K : compacts G, K.1 ⊆ U.1 ∧ haar_outer_measure K₀ U ≤ haar_outer_measure K₀ K.1 + ε :=
outer_measure.of_content_exists_compact _ _ hU hε

lemma haar_outer_measure_caratheodory {K₀ : positive_compacts G} (A : set G) :
  (haar_outer_measure K₀).caratheodory.is_measurable A ↔ ∀ (U : opens G),
  haar_outer_measure K₀ (U ∩ A) + haar_outer_measure K₀ (U \ A) ≤ haar_outer_measure K₀ U :=
outer_measure.of_inner_content_caratheodory A

lemma haar_outer_measure_mono {K₀ : positive_compacts G}
  {{A B : set G}} (h2 : A ⊆ B) : haar_outer_measure K₀ A ≤ haar_outer_measure K₀ B :=
outer_measure.of_inner_content_mono h2

lemma haar_outer_measure_of_is_open {K₀ : positive_compacts G} (U : set G) (hU : is_open U) :
  haar_outer_measure K₀ U =
  outer_measure.inner_content (λ K, show nnreal, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩) ⟨U, hU⟩ :=
outer_measure.of_content_opens ⟨U, hU⟩

lemma haar_outer_measure_le_chaar {K₀ : positive_compacts G} {U : set G} (hU : is_open U)
  (K : compacts G) (h : U ⊆ K.1) :
  haar_outer_measure K₀ U ≤ show nnreal, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩ :=
begin
  rw haar_outer_measure_of_is_open U hU,
  refine outer_measure.inner_content_le _ _ K h, intros K₁ K₂ hK,
  norm_cast, rw [← nnreal.coe_le_coe], exact chaar_mono hK
end

lemma chaar_le_haar_outer_measure {K₀ : positive_compacts G} (K : compacts G) :
   (show nnreal, from ⟨chaar K₀ K, chaar_nonneg K₀ K⟩ : ennreal) ≤ haar_outer_measure K₀ K.1 :=
outer_measure.le_of_content_compacts K

variables [S : measurable_space G] [borel_space G]
include S

lemma haar_caratheodory_measurable (K₀ : positive_compacts G) :
  S ≤ (haar_outer_measure K₀).caratheodory :=
begin
  rw [@borel_space.measurable_eq G _ _], refine generate_from_le _,
  intros U hU, rw haar_outer_measure_caratheodory, intro U',
  rw haar_outer_measure_of_is_open (↑U' ∩ U) (is_open_inter U'.2 hU),
  simp only [outer_measure.inner_content, supr_subtype'],
  haveI : nonempty {L : compacts G // L.1 ⊆ U' ∩ U} := ⟨⟨⊥, empty_subset _⟩⟩,
  rw [ennreal.supr_add], refine supr_le _, rintro ⟨L, hL⟩, simp only [subset_inter_iff] at hL,
  have : ↑U' \ U ⊆ U' \ L.1 := diff_subset_diff_right hL.2,
  refine le_trans (add_le_add_left' $ haar_outer_measure_mono this) _,
  rw haar_outer_measure_of_is_open (↑U' \ L.1) (is_open_diff U'.2 (closed_of_compact L.1 L.2)),
  simp only [outer_measure.inner_content, supr_subtype'],
  haveI : nonempty {M : compacts G // M.1 ⊆ ↑U' \ L.1} := ⟨⟨⊥, empty_subset _⟩⟩,
  rw [ennreal.add_supr], refine supr_le _, rintro ⟨M, hM⟩, simp only [subset_diff] at hM,
  have : (L ⊔ M).1 ⊆ U',
  { simp only [union_subset_iff, compacts.sup_val, hM, hL, and_self] },
  rw haar_outer_measure_of_is_open ↑U' U'.2,
  refine le_trans (ge_of_eq _) (outer_measure.le_inner_content _ _ this), norm_cast,
  simp only [←nnreal.coe_eq, nnreal.coe_add, subtype.coe_mk], exact chaar_sup_eq hM.2.symm
end

/-- the Haar measure on `G` -/
def haar_measure (K₀ : positive_compacts G) : measure G :=
(haar_outer_measure K₀).to_measure $ haar_caratheodory_measurable K₀

lemma haar_measure_apply {K₀ : positive_compacts G} {s : set G} (hs : is_measurable s) :
  haar_measure K₀ s = haar_outer_measure K₀ s :=
to_measure_apply _ _ hs

lemma regular_haar_measure [locally_compact_space G] {K₀ : positive_compacts G} :
  (haar_measure K₀).regular :=
begin
  split,
  { intros K hK, rcases exists_compact_superset hK with ⟨F, h1F, h2F⟩,
    rw [haar_measure_apply hK.is_measurable],
    refine lt_of_le_of_lt (haar_outer_measure_mono h2F) _,
    refine lt_of_le_of_lt (haar_outer_measure_le_chaar is_open_interior ⟨F, h1F⟩ interior_subset)
      ennreal.coe_lt_top },
  { intros A hA, rw [haar_measure_apply hA],
    refine le_infi _, intro U, refine le_infi _, intro hU,
    refine infi_le_of_le U.1 _, refine infi_le_of_le U.2 _, refine infi_le_of_le hU _,
    rw [haar_measure_apply U.2.is_measurable, haar_outer_measure_of_is_open U.1 U.2],
    convert le_refl _ },
  { intros U hU, rw [haar_measure_apply hU.is_measurable, haar_outer_measure_of_is_open U hU],
    dsimp only [outer_measure.inner_content],
    refine supr_le _, intro K, refine supr_le _, intro hK,
    refine le_supr_of_le K.1 _, refine le_supr_of_le K.2 _, refine le_supr_of_le hK _,
    rw [haar_measure_apply K.2.is_measurable], apply chaar_le_haar_outer_measure }
end

end measure_theory

-- #lint


-- typo: has_inhabited_instances -> has_inhabited_instance
