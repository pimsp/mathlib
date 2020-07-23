import topology.sheaves.sheaf
import category_theory.limits.preserves
import category_theory.limits.types

open category_theory
open category_theory.limits
open topological_space
open opposite
open Top

section

universes v u

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C]
variables {F G : J ⥤ C} (α : F ≅ G)
variables (c : cone F)

def blah : is_limit ((cones.postcompose α.hom).obj c) ≃ is_limit c := sorry

end

section
open sheaf_condition

universes v u

variables {C : Type u} [category.{v} C] [has_products C]
variables {D : Type u} [category.{v} D] [has_products D]
variables (G : C ⥤ D) [preserves_limits G]
variables {X : Top.{v}} (F : presheaf C X)
variables {ι : Type v} (U : ι → opens X)

def bar :
  parallel_pair (left_restriction (F ⋙ G) U) (right_restriction (F ⋙ G) U)
    ≅ parallel_pair (left_restriction F U) (right_restriction F U) ⋙ G :=
begin
fapply nat_iso.of_components,
  intro j,
  cases j,
  dsimp [product_over_opens], sorry, sorry, sorry,
end

def foo : G.map_cone (sheaf_condition.fork F U) ≅
  (cones.postcompose (bar G F U).hom).obj (sheaf_condition.fork (F ⋙ G) U) :=
cones.ext (iso.refl _) (λ j, begin dsimp, simp, sorry, end)

end

universes v u

open sheaf_condition

variables {C : Type (u+1)} [large_category C] [concrete_category C]
variables [reflects_isomorphisms (forget C)]
variables [has_limits C] [preserves_limits (forget C)]

variables {X : Top.{u}} (F : presheaf C X)

def sheaf_condition_in_Type : sheaf_condition F ≃ sheaf_condition (F ⋙ (forget C)) :=
begin
  fsplit,
  { intros S ι U,
    have t1 := S U,
    have t2 := @preserves_limit.preserves _ _ _ _ _ _ _ (forget C) _ _ t1,
    have t3 := is_limit.of_iso_limit t2 (foo _ _ _),
    have t4 := blah _ _ t3,
    exact t4, },
  { intros S ι U,
    let f := equalizer.lift _ (fork_condition F U),
    haveI : is_iso ((forget C).map f) :=
    begin
      sorry,
    end,
    haveI : is_iso f := is_iso_of_reflects_iso f (forget C),
    apply is_limit.of_iso_limit (limit.is_limit _),
    apply iso.symm,
    fapply cones.ext,
    exact (as_iso f),
    intro j,
    cases j,
    dsimp [f],
    simp,
    dsimp [sheaf_condition.fork],
    refl,
    -- we shouldn't really have to check at both points `j`; add a lemma to this effect?
    sorry,
  },
  { intros S, apply subsingleton.elim, },
  { intros S, apply subsingleton.elim, },
end