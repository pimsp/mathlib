/-
Copyright (c) 2018 Kevin Buzzard and Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot.

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import group_theory.coset

universes u v

namespace quotient_group

variables {G : Type u} [group G] (N : subgroup G) [hN : N.normal] {H : Type v} [group H]

section
include hN
@[to_additive quotient_add_group.add_group]
instance : group (quotient N) :=
{ one := (1 : G),
  mul := quotient.map₂' (*)
  (λ a₁ b₁ hab₁ a₂ b₂ hab₂,
    ((N.mul_mem_cancel_right (N.inv_mem hab₂)).1
        (by { rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)],
          exact hN.1 _ hab₁ _ }))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c
    (λ a b c, congr_arg mk (mul_assoc a b c)),
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  mul_one := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_one a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : G) : quotient N))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ N,
      rw ← mul_inv_rev,
      exact N.inv_mem (hN.mem_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)) }

@[to_additive]
def mk_hom : G →* (quotient N) :=
{ to_fun := mk,
  map_mul' := λ x y, rfl,
  map_one' := rfl }

@[simp]
lemma coe_fun_mk_hom : ⇑(@mk_hom _ _ N hN) = quotient_group.mk := rfl

@[simp, to_additive quotient_add_group.ker_mk]
lemma ker_mk : (mk_hom N).ker = N :=
begin
  ext g,
  rw [monoid_hom.mem_ker, eq_comm],
  show (((1 : G) : quotient_group.quotient N)) = g ↔ _,
  rw [quotient_group.eq, one_inv, one_mul],
end
end

@[to_additive quotient_add_group.add_comm_group]
instance {G : Type*} [comm_group G] (H : subgroup G) : comm_group (quotient H) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b
    (λ a b, congr_arg mk (mul_comm a b)),
  ..@quotient_group.group _ _ H H.normal_of_comm }

include hN

@[simp, to_additive quotient_add_group.coe_zero]
lemma coe_one : ((1 : G) : quotient N) = 1 := rfl

@[simp, to_additive quotient_add_group.coe_add]
lemma coe_mul (a b : G) : ((a * b : G) : quotient N) = a * b := rfl

@[simp, to_additive quotient_add_group.coe_neg]
lemma coe_inv (a : G) : ((a⁻¹ : G) : quotient N) = a⁻¹ := rfl

@[simp] lemma coe_pow (a : G) (n : ℕ) : ((a ^ n : G) : quotient N) = a ^ n :=
(mk_hom N).map_pow a n

@[simp] lemma coe_gpow (a : G) (n : ℤ) : ((a ^ n : G) : quotient N) = a ^ n :=
(mk_hom N).map_gpow a n

local notation ` Q ` := quotient N

variables (N)

@[to_additive quotient_add_group.lift]
def lift (φ : G →* H) (HN : ∀x∈N, φ x = 1) : quotient N →* H := {
to_fun := λ q, q.lift_on' φ $ assume a b (hab : a⁻¹ * b ∈ N),
    (calc φ a = φ a * 1           : (mul_one _).symm
    ...       = φ a * φ (a⁻¹ * b) : HN (a⁻¹ * b) hab ▸ rfl
    ...       = φ (a * (a⁻¹ * b)) : (is_mul_hom.map_mul φ a (a⁻¹ * b)).symm
    ...       = φ b               : by rw mul_inv_cancel_left),
  map_mul' := λ q r, quotient.induction_on₂' q r $ φ.map_mul,
  map_one' := φ.map_one }

variables {N} {φ : G →* H} (HN : ∀x∈N, φ x = 1)

@[simp, to_additive quotient_add_group.lift_mk]
lemma lift_mk (g : G) :
  lift N φ HN (g : Q) = φ g := rfl

@[simp, to_additive quotient_add_group.lift_mk']
lemma lift_mk' (g : G) :
  lift N φ HN (mk g : Q) = φ g := rfl

@[to_additive quotient_add_group.map]
def map (M : subgroup H) [M.normal] (f : G →* H) (h : ↑N ⊆ f ⁻¹' M) :
  quotient N →* quotient M :=
quotient_group.lift N ((mk_hom M).comp f)
    (λ x hx, quotient_group.eq.2 (by simpa [M.inv_mem_iff] using h hx))

open function monoid_hom

variables (N) (φ)

/-- The induced map from the quotient by the kernel to the codomain. -/
@[to_additive quotient_add_group.ker_lift]
def ker_lift : quotient φ.ker →* H :=
lift _ φ $ λ g, mem_ker.mp

@[simp, to_additive quotient_add_group.ker_lift_mk]
lemma ker_lift_mk (g : G) : ker_lift N φ g = φ g :=
lift_mk _ _

@[simp, to_additive quotient_add_group.ker_lift_mk']
lemma ker_lift_mk' (g : G) : ker_lift N φ (mk g) = φ g :=
lift_mk' _ _

@[to_additive quotient_add_group.injective_ker_lift]
lemma ker_lift_injective : injective (ker_lift N φ) :=
assume a b, quotient.induction_on₂' a b $ assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ φ.ker, by rw [mem_ker,
  is_mul_hom.map_mul φ, ← h, is_group_hom.map_inv φ, inv_mul_self]

--@[to_additive quotient_add_group.quotient_ker_equiv_range]
noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃ set.range φ :=
equiv.of_bijective (λ x, ⟨lift (ker φ) φ
  (by simp [mem_ker]) x, by exact quotient.induction_on' x (λ x, ⟨x, rfl⟩)⟩)
⟨λ a b h, ker_lift_injective N _ (subtype.mk.inj h),
  λ ⟨x, y, hy⟩, ⟨mk y, subtype.eq hy⟩⟩

noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  (quotient (ker φ)) ≃ H :=
calc (quotient_group.quotient φ.ker) ≃ set.range φ : quotient_ker_equiv_range N _
... ≃ H : ⟨λ a, a.1, λ b, ⟨b, hφ b⟩, λ ⟨_, _⟩, rfl, λ _, rfl⟩

end quotient_group

namespace quotient_add_group
open is_add_group_hom

variables {G : Type u} [_root_.add_group G] (N : add_subgroup G) [hN : N.normal]
variables {H : Type v} [_root_.add_group H]
variables (φ : G →+ H)

include hN
noncomputable def quotient_ker_equiv_range : (quotient φ.ker) ≃ set.range φ :=
@quotient_group.quotient_ker_equiv_range (multiplicative G) _ _ hN.to_subgroup
  (multiplicative H) _ φ.to_multiplicative

noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  quotient (add_monoid_hom.ker φ) ≃ H :=
@quotient_group.quotient_ker_equiv_of_surjective (multiplicative G) _ _ hN.to_subgroup
  (multiplicative H) _ φ.to_multiplicative hφ

attribute [to_additive quotient_add_group.quotient_ker_equiv_range] quotient_group.quotient_ker_equiv_range
attribute [to_additive quotient_add_group.quotient_ker_equiv_of_surjective] quotient_group.quotient_ker_equiv_of_surjective

end quotient_add_group
