/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Free abelian groups as abelianization of free groups.
-/
import algebra.pi_instances
import group_theory.free_group
import group_theory.abelianization

universes u v

variables (α : Type u)

def free_abelian_group : Type u :=
additive $ abelianization $ free_group α

instance : add_comm_group (free_abelian_group α) :=
@additive.add_comm_group _ $ abelianization.comm_group _

instance : inhabited (free_abelian_group α) := ⟨0⟩

variable {α}

namespace free_abelian_group

def of (x : α) : free_abelian_group α :=
abelianization.of $ free_group.of x

def lift {β : Type v} [add_comm_group β] (f : α → β) : free_abelian_group α →+ β :=
monoid_hom.to_additive $ @abelianization.lift _ _ (multiplicative β) _
  (monoid_hom.of $ @free_group.to_group _ (multiplicative β) _ f)

def map {β : Type v} (f : α → β) : free_abelian_group α →+ free_abelian_group β :=
lift (of ∘ f)

namespace lift
variables {β : Type v} [add_comm_group β] (f : α → β)
open free_abelian_group

@[simp] protected lemma add (x y : free_abelian_group α) :
  lift f (x + y) = lift f x + lift f y :=
is_add_hom.map_add _ _ _

@[simp] protected lemma neg (x : free_abelian_group α) : lift f (-x) = -lift f x :=
is_add_group_hom.map_neg _ _

@[simp] protected lemma sub (x y : free_abelian_group α) :
  lift f (x - y) = lift f x - lift f y :=
by simp [sub_eq_add_neg]

@[simp] protected lemma zero : lift f 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] protected lemma of (x : α) : lift f (of x) = f x :=
by simp [of, lift]

protected theorem unique (g : free_abelian_group α →+ β)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
@abelianization.lift.unique (free_group α) _ (multiplicative β) _ _ g.to_multiplicative
  (λ x, @free_group.to_group.unique α (multiplicative β) _ _
    (g.to_multiplicative.comp abelianization.of) hg _) _

protected theorem ext (g h : free_abelian_group α →+ β)
  (H : ∀ x, g (of x) = h (of x)) {x} :
  g x = h x :=
(lift.unique (g ∘ of) g (λ _, rfl)).trans $
eq.symm $ lift.unique _ _ $ λ x, eq.symm $ H x

lemma map_hom {α β γ} [add_comm_group β] [add_comm_group γ]
  (a : free_abelian_group α) (f : α → β) (g : β →+ γ) :
  g (lift f a) = lift (g ∘ f) a :=
lift.unique (g ∘ f) (g.comp (lift f)) (by simp)

end lift

@[simp] lemma map.id (x : free_abelian_group α) : map id x = x :=
(lift.unique (of ∘ id) (add_monoid_hom.id _) (λ x, rfl)).symm

@[simp] lemma map.comp {β γ} (f : α → β) (g : β → γ) (x : free_abelian_group α) :
  map (g ∘ f) x = map g (map f x) :=
(lift.unique (of ∘ g ∘ f) ((map g).comp (map f)) (λ x, rfl)).symm

section
variables (X : Type*) (G : Type*) [add_comm_group G]

/-- The bijection underlying the free-forgetful adjunction for abelian groups.-/
def hom_equiv : (free_abelian_group X →+ G) ≃ (X → G) :=
{ to_fun := λ f, f.1 ∘ of,
  inv_fun := λ f, add_monoid_hom.of (lift f),
  left_inv := λ f, begin ext, simp, exact (lift.unique _ _ (λ x, rfl)).symm, end,
  right_inv := λ f, funext $ λ x, lift.of f x }

@[simp]
lemma hom_equiv_apply (f) (x) : ((hom_equiv X G) f) x = f (of x) := rfl
@[simp]
lemma hom_equiv_symm_apply (f) (x) : ((hom_equiv X G).symm f) x = (lift f) x := rfl

end

local attribute [instance] abelianization.commutator_left_rel

@[elab_as_eliminator]
protected theorem induction_on
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ of x)
  (Cn : ∀ x, C (of x) → C (-of x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on z $ λ x, quot.induction_on x $ λ L,
list.rec_on L C0 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

theorem lift.add' {α β} [add_comm_group β] (a : free_abelian_group α) (f g : α → β) :
  lift (f + g) a = lift f a + lift g a :=
begin
  refine free_abelian_group.induction_on a _ _ _ _,
  { simp only [lift.zero, zero_add] },
  { assume x,
    simp only [lift.of, pi.add_apply] },
  { assume x h,
    simp only [lift.neg, lift.of, pi.add_apply, neg_add] },
  { assume x y hx hy,
    simp only [lift.add, hx, hy],
    ac_refl }
end

instance is_add_group_hom_lift' {α} (β) [add_comm_group β] (a : free_abelian_group α) :
  is_add_group_hom (λf, (lift f a : β)) :=
{ map_add := λ f g, lift.add' a f g }

@[simp] lemma lift.zero' {α β} [add_comm_group β] (x : free_abelian_group α) : lift (0 : α → β) x = 0 :=
is_add_group_hom.map_zero (λ f, (lift f x : β))

variables {β : Type u}

instance : monad free_abelian_group.{u} :=
{ pure := λ α, of,
  bind := λ α β x f, lift f x }

@[elab_as_eliminator]
protected theorem induction_on'
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ pure x)
  (Cn : ∀ x, C (pure x) → C (-pure x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
free_abelian_group.induction_on z C0 C1 Cn Cp

@[simp] lemma map_pure (f : α → β) (x : α) : f <$> (pure x : free_abelian_group α) = pure (f x) :=
lift.of _ _

@[simp] lemma map_zero (f : α → β) : f <$> (0 : free_abelian_group α) = 0 :=
lift.zero (of ∘ f)

@[simp] lemma map_add (f : α → β) (x y : free_abelian_group α) : f <$> (x + y) = f <$> x + f <$> y :=
lift.add _ _ _

@[simp] lemma map_neg (f : α → β) (x : free_abelian_group α) : f <$> (-x) = -(f <$> x) :=
lift.neg _ _

@[simp] lemma map_sub (f : α → β) (x y : free_abelian_group α) : f <$> (x - y) = f <$> x - f <$> y :=
lift.sub _ _ _

@[simp] lemma map_of (f : α → β) (y : α) : f <$> of y = of (f y) := rfl

lemma lift_comp {α} {β} {γ} [add_comm_group γ]
  (f : α → β) (g : β → γ) (x : free_abelian_group α) :
  lift (g ∘ f) x = lift g (f <$> x) :=
begin
  apply free_abelian_group.induction_on x,
  { simp only [lift.zero, map_zero], },
  { intro y, simp [lift.of, map_of, function.comp_app], },
  { intros x w, simp only [w, neg_inj, lift.neg, map_neg], },
  { intros x y w₁ w₂, simp only [w₁, w₂, lift.add, add_right_inj, map_add], },
end

@[simp] lemma pure_bind (f : α → free_abelian_group β) (x) : pure x >>= f = f x :=
lift.of _ _

@[simp] lemma zero_bind (f : α → free_abelian_group β) : 0 >>= f = 0 :=
lift.zero f

@[simp] lemma add_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) : x + y >>= f = (x >>= f) + (y >>= f) :=
lift.add _ _ _

@[simp] lemma neg_bind (f : α → free_abelian_group β) (x : free_abelian_group α) : -x >>= f = -(x >>= f) :=
lift.neg _ _

@[simp] lemma sub_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) : x - y >>= f = (x >>= f) - (y >>= f) :=
lift.sub _ _ _

@[simp] lemma pure_seq (f : α → β) (x : free_abelian_group α) : pure f <*> x = f <$> x :=
pure_bind _ _

@[simp] lemma zero_seq (x : free_abelian_group α) : (0 : free_abelian_group (α → β)) <*> x = 0 :=
zero_bind _

@[simp] lemma add_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) : f + g <*> x = (f <*> x) + (g <*> x) :=
add_bind _ _ _

@[simp] lemma neg_seq (f : free_abelian_group (α → β)) (x : free_abelian_group α) : -f <*> x = -(f <*> x) :=
neg_bind _ _

@[simp] lemma sub_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) : f - g <*> x = (f <*> x) - (g <*> x) :=
sub_bind _ _ _

instance is_add_group_hom_seq (f : free_abelian_group (α → β)) : is_add_group_hom ((<*>) f) :=
{ map_add := λ x y, show lift (<$> (x+y)) _ = _, by simp only [map_add]; exact
@@is_add_hom.map_add _ _ _ (@@free_abelian_group.is_add_group_hom_lift' (free_abelian_group β) _ _).to_is_add_hom _ _ }

@[simp] lemma seq_zero (f : free_abelian_group (α → β)) : f <*> 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] lemma seq_add (f : free_abelian_group (α → β)) (x y : free_abelian_group α) : f <*> (x + y) = (f <*> x) + (f <*> y) :=
is_add_hom.map_add _ _ _

@[simp] lemma seq_neg (f : free_abelian_group (α → β)) (x : free_abelian_group α) : f <*> (-x) = -(f <*> x) :=
is_add_group_hom.map_neg _ _

@[simp] lemma seq_sub (f : free_abelian_group (α → β)) (x y : free_abelian_group α) : f <*> (x - y) = (f <*> x) - (f <*> y) :=
is_add_group_hom.map_sub _ _ _

instance : is_lawful_monad free_abelian_group.{u} :=
{ id_map := λ α x, free_abelian_group.induction_on' x (map_zero id) (λ x, map_pure id x)
    (λ x ih, by rw [map_neg, ih]) (λ x y ihx ihy, by rw [map_add, ihx, ihy]),
  pure_bind := λ α β x f, pure_bind f x,
  bind_assoc := λ α β γ x f g, free_abelian_group.induction_on' x
    (by iterate 3 { rw zero_bind }) (λ x, by iterate 2 { rw pure_bind })
    (λ x ih, by iterate 3 { rw neg_bind }; rw ih)
    (λ x y ihx ihy, by iterate 3 { rw add_bind }; rw [ihx, ihy]) }

instance : is_comm_applicative free_abelian_group.{u} :=
{ commutative_prod := λ α β x y, free_abelian_group.induction_on' x
    (by rw [map_zero, zero_seq, seq_zero])
    (λ p, by rw [map_pure, pure_seq]; exact free_abelian_group.induction_on' y
      (by rw [map_zero, map_zero, zero_seq])
      (λ q, by rw [map_pure, map_pure, pure_seq, map_pure])
      (λ q ih, by rw [map_neg, map_neg, neg_seq, ih])
      (λ y₁ y₂ ih1 ih2, by rw [map_add, map_add, add_seq, ih1, ih2]))
    (λ p ih, by rw [map_neg, neg_seq, seq_neg, ih])
    (λ x₁ x₂ ih1 ih2, by rw [map_add, add_seq, seq_add, ih1, ih2]) }
variable (α)

instance [monoid α] : has_mul (free_abelian_group α) :=
{ mul := λ x, lift $ λ x₂, lift (λ x₁, of $ x₁ * x₂) x }

lemma mul_eq [monoid α] (x y : free_abelian_group α) :
  x * y = lift (λ x₂, lift (λ x₁, of $ x₁ * x₂) x) y := rfl

instance [monoid α] : semigroup (free_abelian_group α) :=
{ mul_assoc := λ x y z, begin
    simp only [mul_eq],
    refine free_abelian_group.induction_on z _ _ _ _;
      simp only [lift.of, lift.zero, lift.neg, lift.add],
    { intros L3,
      refine free_abelian_group.induction_on y _ _ _ _;
        simp only [lift.of, lift.zero, lift.neg, lift.add],
      { intros L2,
        refine free_abelian_group.induction_on x _ _ _ _;
          simp only [lift.of, lift.zero, lift.neg, lift.add],
        { intros L1,
          rw mul_assoc },
        { intros L1 ih,
          rw ih },
        { intros x1 x2 ih1 ih2,
          rw [ih1, ih2] }},
      { intros L2 ih,
        rw ih },
      { intros x1 x2 ih1 ih2,
        rw [ih1, ih2] }},
    { intros L3 ih,
      rw ih },
    { intros x1 x2 ih1 ih2,
      rw [ih1, ih2] },
  end,
  ..free_abelian_group.has_mul _ }

lemma mul_def [monoid α] (x y : free_abelian_group α) :
  x * y = lift (λ x₂, lift (λ x₁, of (x₁ * x₂)) x) y := rfl

instance [monoid α] : ring (free_abelian_group α) :=
{ one := free_abelian_group.of 1,
  mul_one := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    rw lift.of,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros L, erw [lift.of], congr' 1, exact mul_one L },
    { intros L ih, rw [lift.neg, ih] },
    { intros x1 x2 ih1 ih2, rw [lift.add, ih1, ih2] }
  end,
  one_mul := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros L, rw [lift.of, lift.of], congr' 1, exact one_mul L },
    { intros L ih, rw [lift.neg, ih] },
    { intros x1 x2 ih1 ih2, rw [lift.add, ih1, ih2] }
  end,
  left_distrib := λ x y z, lift.add _ _ _,
  right_distrib := λ x y z, begin
    unfold has_mul.mul semigroup.mul,
    refine free_abelian_group.induction_on z rfl _ _ _,
    { intros L, iterate 3 { rw lift.of }, rw lift.add, refl },
    { intros L ih, iterate 3 { rw lift.neg }, rw [ih, neg_add], refl },
    { intros z1 z2 ih1 ih2, iterate 3 { rw lift.add }, rw [ih1, ih2],
      rw [add_assoc, add_assoc], congr' 1, apply add_left_comm }
  end,
  .. free_abelian_group.add_comm_group α,
  .. free_abelian_group.semigroup α }

instance [comm_monoid α] : comm_ring (free_abelian_group α) :=
{ mul_comm := λ x y, begin
    refine free_abelian_group.induction_on x (zero_mul y) _ _ _,
    { intros s, refine free_abelian_group.induction_on y (zero_mul _).symm _ _ _,
      { intros t, unfold has_mul.mul semigroup.mul ring.mul,
        iterate 4 { rw lift.of }, congr' 1, exact mul_comm _ _ },
      { intros t ih, rw [mul_neg_eq_neg_mul_symm, ih, neg_mul_eq_neg_mul] },
      { intros y1 y2 ih1 ih2, rw [mul_add, add_mul, ih1, ih2] } },
    { intros s ih, rw [neg_mul_eq_neg_mul_symm, ih, neg_mul_eq_mul_neg] },
    { intros x1 x2 ih1 ih2, rw [add_mul, mul_add, ih1, ih2] }
  end
  .. free_abelian_group.ring α }

end free_abelian_group
