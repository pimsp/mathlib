/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import group_theory.subgroup
open set function

variable {G : Type*}

/-- `a *l s` is the left `a`-coset of `s`, the set of all elements `a * x` for `x ∈ s` -/
@[to_additive left_add_coset
  "`a +l s` is the left `a`-coset of `s`, the set of all elements `a + x` for `x ∈ s`"]
def left_coset [has_mul G] (a : G) (s : set G) : set G := (λ x, a * x) '' s

/-- `s *r a` is the right `a`-coset of `s`, the set of all elements `x * a` for `x ∈ s` -/
@[to_additive right_add_coset
  "`s +r a` is the right `a`-coset of `s`, the set of all elements `x + a` for `x ∈ s`"]
def right_coset [has_mul G] (s : set G) (a : G) : set G := (λ x, x * a) '' s

localized "infix ` *l `:70 := left_coset" in coset
localized "infix ` +l `:70 := left_add_coset" in coset
localized "infix ` *r `:70 := right_coset" in coset
localized "infix ` +r `:70 := right_add_coset" in coset

section coset_mul
variable [has_mul G]

@[to_additive mem_left_add_coset]
lemma mem_left_coset {s : set G} {x : G} (a : G) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : G, a * b) hxS

@[to_additive mem_right_add_coset]
lemma mem_right_coset {s : set G} {x : G} (a : G) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : G, b * a) hxS

/-- `a` and `b` are equivalent for the relation `left_coset_equiv s` if `a *l s = b *l s` -/
@[to_additive left_add_coset_equiv
  "`a` and `b` are equivalent for the relation `left_add_coset_equiv s` if `a +l s = b +l s`"]
def left_coset_equiv (s : set G) (a b : G) := a *l s = b *l s

@[to_additive left_add_coset_equiv_rel]
lemma left_coset_equiv_rel (s : set G) : equivalence (left_coset_equiv s) :=
mk_equivalence (left_coset_equiv s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup G]

@[simp] lemma left_coset_assoc (s : set G) (a b : G) : a *l (b *l s) = (a * b) *l s :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]
attribute [to_additive left_add_coset_assoc] left_coset_assoc

@[simp] lemma right_coset_assoc (s : set G) (a b : G) : s *r a *r b = s *r (a * b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]
attribute [to_additive right_add_coset_assoc] right_coset_assoc

@[to_additive left_add_coset_right_add_coset]
lemma left_coset_right_coset (s : set G) (a b : G) : a *l s *r b = a *l (s *r b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

end coset_semigroup

section coset_monoid
variables [monoid G] (s : set G)

@[simp] lemma one_left_coset : 1 *l s = s :=
set.ext $ by simp [left_coset]
attribute [to_additive zero_left_add_coset] one_left_coset

@[simp] lemma right_coset_one : s *r 1 = s :=
set.ext $ by simp [right_coset]
attribute [to_additive right_add_coset_zero] right_coset_one

end coset_monoid

section coset_submonoid
open submonoid
variables [monoid G] (s : submonoid G)

@[to_additive mem_own_left_add_coset]
lemma mem_own_left_coset (a : G) : a ∈ a *l s :=
suffices a * 1 ∈ a *l s, by simpa,
mem_left_coset a (one_mem s)

@[to_additive mem_own_right_add_coset]
lemma mem_own_right_coset (a : G) : a ∈ (s : set G) *r a :=
suffices 1 * a ∈ (s : set G) *r a, by simpa,
mem_right_coset a (one_mem s)

@[to_additive mem_left_add_coset_left_add_coset]
lemma mem_left_coset_left_coset {a : G} (ha : a *l s = s) : a ∈ s :=
by rw [←submonoid.mem_coe, ←ha]; exact mem_own_left_coset s a

@[to_additive mem_right_add_coset_right_add_coset]
lemma mem_right_coset_right_coset {a : G} (ha : (s : set G) *r a = s) : a ∈ s :=
by rw [←submonoid.mem_coe, ←ha]; exact mem_own_right_coset s a

end coset_submonoid

section coset_group
variables [group G] {s : set G} {x : G}

@[to_additive mem_left_add_coset_iff]
lemma mem_left_coset_iff (a : G) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨a⁻¹ * x, h, by simp⟩)

@[to_additive mem_right_add_coset_iff]
lemma mem_right_coset_iff (a : G) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨x * a⁻¹, h, by simp⟩)

end coset_group

section coset_subgroup
open submonoid
open subgroup
variables [group G] (s : subgroup G)

@[to_additive left_add_coset_mem_left_add_coset]
lemma left_coset_mem_left_coset {a : G} (ha : a ∈ s) : a *l s = s :=
set.ext $ by simp [mem_left_coset_iff, mul_mem_cancel_left s (s.inv_mem ha)]

@[to_additive right_add_coset_mem_right_add_coset]
lemma right_coset_mem_right_coset {a : G} (ha : a ∈ s) : (s : set G) *r a = s :=
set.ext $ assume b, by simp [mem_right_coset_iff, mul_mem_cancel_right s (s.inv_mem ha)]

@[to_additive normal_of_eq_add_cosets]
theorem eq_cosets_of_normal (h : normal s) (g : G) : g *l s = s *r g :=
set.ext $ assume a, by { simp [mem_left_coset_iff, mem_right_coset_iff], rw [h.mem_comm_iff] }

@[to_additive eq_add_cosets_of_normal]
theorem normal_of_eq_cosets (h : ∀ (g : G), g *l s = s *r g) : normal s :=
⟨ assume a ha g, show g * a * g⁻¹ ∈ ↑s,
  by { rw [← mem_right_coset_iff, ← h], exact mem_left_coset g ha } ⟩

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : normal s ↔ ∀ (g : G), g *l s = s *r g :=
⟨eq_cosets_of_normal s, normal_of_eq_cosets s⟩

end coset_subgroup

run_cmd to_additive.map_namespace `quotient_group `quotient_add_group

namespace quotient_group

/-- `left_rel s` for a subgroup `s` relates `x` and `y` iff their left cosets of `s` are the same -/
@[to_additive
  "`left_rel s` for an additive subgroup `s` relates `x` and `y` iff their left cosets of `s` are the same"]
def left_rel [group G] (s : subgroup G) : setoid G :=
⟨λ x y, x⁻¹ * y ∈ s,
  assume x, by simpa using s.one_mem,
  assume x y hxy,
  have (x⁻¹ * y)⁻¹ ∈ s, from s.inv_mem hxy,
  by simpa using this,
  assume x y z hxy hyz,
  have x⁻¹ * y * (y⁻¹ * z) ∈ s, from s.mul_mem hxy hyz,
  by simpa [mul_assoc] using this⟩

/-- `quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group -/
@[to_additive "`quotient s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `quotient s` is a group"]
def quotient [group G] (s : subgroup G) : Type* := quotient (left_rel s)

variables [group G] {s : subgroup G}

/-- `quotient_group.mk` is the projection from the group to the quotient -/
@[to_additive "`quotient_add_group.mk` is the projection from the group to the quotient"]
def mk (a : G) : quotient s :=
quotient.mk' a

@[elab_as_eliminator, to_additive]
lemma induction_on {C : quotient s → Prop} (x : quotient s)
  (H : ∀ z, C (quotient_group.mk z)) : C x :=
quotient.induction_on' x H

@[to_additive]
instance : has_coe_t G (quotient s) := ⟨mk⟩ -- note [use has_coe_t]

@[elab_as_eliminator, to_additive]
lemma induction_on' {C : quotient s → Prop} (x : quotient s)
  (H : ∀ z : G, C z) : C x :=
quotient.induction_on' x H

@[to_additive]
instance (s : subgroup G) : inhabited (quotient s) :=
⟨((1 : G) : quotient s)⟩

@[to_additive quotient_add_group.eq]
protected lemma eq {a b : G} : (a : quotient s) = b ↔ a⁻¹ * b ∈ s :=
quotient.eq'

@[to_additive]
lemma eq_class_eq_left_coset (s : subgroup G) (g : G) :
  {x : G | (x : quotient s) = g} = left_coset g s :=
by { ext, rw [mem_left_coset_iff, set.mem_set_of_eq, eq_comm, quotient_group.eq, subgroup.has_mem] }

end quotient_group

namespace subgroup
open quotient_group
variables [group G] {s : set G}

/-- multiplying with `g` on the left is a bijection sending `s` to `left_coset g s` -/
@[to_additive "adding `g` on the left is a bijection sending `s` to `left_add_coset g s`"]
def left_coset_equiv_subgroup (g : G) : left_coset g s ≃ s :=
⟨λ x, ⟨g⁻¹ * x.1, (mem_left_coset_iff _).1 x.2⟩,
 λ x, ⟨g * x.1, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩

/-- For a subgroup `H` of a group `G`, `(G / H) × H` is in bijection to `G` -/
@[to_additive "For a subgroup `H` of an additive group `G`, `(G / H) × H` is in bijection to `G`"]
noncomputable def group_equiv_quotient_times_subgroup (H : subgroup G) :
  G ≃ quotient H × H :=
calc G ≃ Σ L : quotient H, {x : G // (x : quotient H)= L} :
  (equiv.sigma_preimage_equiv quotient_group.mk).symm
    ... ≃ Σ L : quotient H, left_coset (quotient.out' L) H :
  equiv.sigma_congr_right (λ L,
    begin rw ← eq_class_eq_left_coset,
      show {x | quotient.mk' x = L} ≃ {x : G | quotient.mk' x = quotient.mk' _},
      simp [-quotient.eq']
    end)
    ... ≃ Σ L : quotient H, H :
  equiv.sigma_congr_right (λ L, left_coset_equiv_subgroup _)
    ... ≃ quotient H × H :
  equiv.sigma_equiv_prod _ _

end subgroup

namespace quotient_group

variables [group G]

/-- Sending `(x : H, quotient_group.mk y : t)` to `x * t : quotient_group.mk ⁻¹' t` is a bijection. -/
noncomputable def preimage_mk_equiv_subgroup_times_set
  (H : subgroup G) (t : set (quotient H)) : quotient_group.mk ⁻¹' t ≃ H × t :=
have h : ∀ {x : quotient H} {a : G}, x ∈ t → a ∈ H →
  (quotient.mk' (quotient.out' x * a) : quotient H) = quotient.mk' (quotient.out' x) :=
    λ x a hx ha, quotient.sound' (show (quotient.out' x * a)⁻¹ * quotient.out' x ∈ H,
      from H.inv_mem_iff.mp $
        by rwa [mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_self, one_mul]),
{ to_fun := λ ⟨a, ha⟩, ⟨⟨(quotient.out' (quotient.mk' a))⁻¹ * a,
    @quotient.exact' _ (left_rel H) _ _ $ (quotient.out_eq' _)⟩,
      ⟨quotient.mk' a, ha⟩⟩,
  inv_fun := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, ⟨quotient.out' x * a, show quotient.mk' _ ∈ t,
    by simp [h hx ha, hx]⟩,
  left_inv := λ ⟨a, ha⟩, subtype.eq $ show _ * _ = a, by simp,
  right_inv := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, show (_, _) = _, by simp [h hx ha] }

end quotient_group

/--
We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/
library_note "use has_coe_t"
