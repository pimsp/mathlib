/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.

-/
import group_theory.quotient_group

universes u v

variables (α : Type u) [group α]

def commutator : subgroup α :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

instance normal_commutator : (commutator α).normal :=
subgroup.normal_closure_normal

def abelianization : Type u :=
quotient_group.quotient $ commutator α

namespace abelianization

/-- The equivalence relation whose quotient is the abelianization. -/
def commutator_left_rel : setoid α := quotient_group.left_rel (commutator α)

local attribute [instance] commutator_left_rel

instance : comm_group (abelianization α) :=
{ mul_comm := λ x y, quotient.induction_on₂ x y $ λ a b, quotient.sound
    (subgroup.subset_normal_closure ⟨b⁻¹, a⁻¹, by simp [mul_inv_rev, inv_inv, mul_assoc]⟩),
.. quotient_group.group _}

instance : inhabited (abelianization α) := ⟨1⟩

variable {α}

def of : α →* abelianization α :=
quotient_group.mk_hom _

section lift

variables {β : Type v} [comm_group β] (f : α →* β)

open monoid_hom

lemma commutator_subset_ker : commutator α ≤ f.ker :=
(subgroup.normal_closure_subset_iff (subgroup.normal_comap f)).mp (λ x ⟨p,q,w⟩, mem_ker.mpr
  (by {rw ←w, simp [is_mul_hom.map_mul f, is_group_hom.map_inv f, mul_comm]}))

def lift : abelianization α →* β :=
quotient_group.lift _ f (λ x h, mem_ker.mp (commutator_subset_ker f h))

@[simp] lemma lift.of (x : α) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (g : abelianization α →* β)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
quotient_group.induction_on x hg

end lift

end abelianization
