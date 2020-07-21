/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
import linear_algebra.tensor_product
import linear_algebra.direct_sum_module

section ring

namespace tensor_product

open_locale tensor_product
open linear_map

variables (R : Type*) [comm_ring R]
variables (ι₁ : Type*) (ι₂ : Type*)
variables [decidable_eq ι₁] [decidable_eq ι₂]
variables (M₁ : ι₁ → Type*) (M₂ : ι₂ → Type*)
variables [Π i₁, add_comm_group (M₁ i₁)] [Π i₂, add_comm_group (M₂ i₂)]
variables [Π i₁, module R (M₁ i₁)] [Π i₂, module R (M₂ i₂)]

/-- The linear equivalence `(⊕ i₁, M₁ i₁) ⊗ (⊕ i₂, M₂ i₂) ≃ (⊕ i₁, ⊕ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
def direct_sum :
  direct_sum ι₁ M₁ ⊗[R] direct_sum ι₂ M₂ ≃ₗ[R] direct_sum (ι₁ × ι₂) (λ i, M₁ i.1 ⊗[R] M₂ i.2) :=
begin
  refine linear_equiv.of_linear
    (lift $ direct_sum.to_module R _ _ $ λ i₁, flip $ direct_sum.to_module R _ _ $ λ i₂,
      flip $ curry $ direct_sum.lof R (ι₁ × ι₂) (λ i, M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂))
    (direct_sum.to_module R _ _ $ λ i, map (direct_sum.lof R _ _ _) (direct_sum.lof R _ _ _))
    (linear_map.ext $ direct_sum.to_module.ext _ $ λ i, mk_compr₂_inj $
      linear_map.ext $ λ x₁, linear_map.ext $ λ x₂, _)
    (mk_compr₂_inj $ linear_map.ext $ direct_sum.to_module.ext _ $ λ i₁, linear_map.ext $ λ x₁,
      linear_map.ext $ direct_sum.to_module.ext _ $ λ i₂, linear_map.ext $ λ x₂, _),
  repeat { rw compr₂_apply <|> rw comp_apply <|> rw id_apply <|> rw mk_apply <|>
    rw direct_sum.to_module_lof <|> rw map_tmul <|> rw lift.tmul <|> rw flip_apply <|>
    rw curry_apply },
  cases i; refl
end

@[simp] theorem direct_sum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
  direct_sum R ι₁ ι₂ M₁ M₂ (direct_sum.lof R ι₁ M₁ i₁ m₁ ⊗ₜ direct_sum.lof R ι₂ M₂ i₂ m₂) =
  direct_sum.lof R (ι₁ × ι₂) (λ i, M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) :=
by simp [direct_sum]

end tensor_product

end ring
