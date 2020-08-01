import .encode_alphabet
import computability.turing_machine

namespace tm2
section
parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (k₀ k₁ : K) -- input and output stack
parameters (Γ : K → Type) -- Type of stack elements
-- parameters (input_alphabet : Γ k₀ = Γ')
parameters (Λ : Type*) [inhabited Λ]
--parameters (Λ : Type*) [inhabited Λ]
parameters (σ : Type*) [inhabited σ]

def stmt' := turing.TM2.stmt Γ Λ σ
def cfg' := turing.TM2.cfg Γ Λ σ

def machine := Λ → stmt'

def init_list (l : list (Γ k₀)) : cfg':=
{ l := option.some (default Λ),
  var := default σ,
  stk := λ k, dite (k = k₀) (λ h,begin rw h, exact l end) (λ _,[])}

def halt_list (l : list (Γ k₁)) : cfg':=
{ l := option.none,
  var := default σ,
  stk := λ k, dite (k = k₁) (λ h,begin rw h, exact l end) (λ _,[])}

@[simp] def tm_evaluates_function (tm : machine) (f : list (Γ k₀) →. list (Γ k₁)) (l : list (Γ k₀)) :=
turing.eval (turing.TM2.step tm) (init_list l) = (roption.map halt_list) (f l)

private def computable_by_tm_aux (f : list (Γ k₀) →. list (Γ k₁)) := ∃ tm : machine, ∀ (l : list (Γ k₀)), tm_evaluates_function tm f l

section
parameters ( σ_fin : fintype σ)
parameters ( Γk₀_fin : fintype (Γ k₀))

def computable_by_tm (f : list (Γ k₀) →. list (Γ k₁)) := computable_by_tm_aux f
end
end
end tm2

#check tm2.machine

structure fin_turing_machine_2 :=
 {K : Type*}
 [K_decidable_eq : decidable_eq K] -- Index type of stacks
 (k₀ k₁ : K) -- input and output stack
 (Γ : K → Type) -- Type of stack elements
 (Λ : Type*)
 [Λ_inhabited : inhabited Λ]
 (σ : Type*)
 [σ_inhabited : inhabited σ]
 [σ_fin : fintype σ]
 [Γk₀_fin : fintype (Γ k₀)]
 (M : tm2.machine Γ Λ σ)

variable my_tm : fin_turing_machine_2

@[simp] def tm_2_evaluates_function_list {Γ Γ' : Type*} (tm : fin_turing_machine_2) (f : list Γ →. list Γ') (l : list Γ) (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ') : Prop := @tm2.tm_evaluates_function tm.K tm.K_decidable_eq tm.k₀ tm.k₁ tm.Γ tm.Λ tm.Λ_inhabited tm.σ tm.σ_inhabited tm.M (λ l:list (tm.Γ tm.k₀), begin rw hi at l, rw ho, exact f l, end) begin rw hi, exact l end

def computable_by_tm_2_list {Γ Γ' : Type*} (f : list Γ →. list Γ') : Prop :=
∃ (tm : fin_turing_machine_2) (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ'), ∀ l, tm_2_evaluates_function_list tm f l hi ho

attribute [class] fin_encoding

def computable_by_tm_2 {α β : Type*} [ea : fin_encoding α] [eb : fin_encoding β] (f : α → β) : Prop := @computable_by_tm_2_list ea.Γ eb.Γ (λ l, (option.map eb.encode) ((option.map f) (ea.decode l)))

open turing.TM2.stmt

def id_computer (α : Type*) [ea : fin_encoding α] : fin_turing_machine_2 :=
{ K := fin 1,
  K_decidable_eq := fin.decidable_eq 1,
  k₀ := 0,
  k₁ := 0,
  Γ := λ _, ea.Γ,
  Λ := fin 1,
  Λ_inhabited := unique.inhabited,
  σ := fin 1,
  σ_inhabited := unique.inhabited,
  σ_fin := unique.fintype,
  Γk₀_fin := ea.Γ_fin,
  M := λ _, halt }

open tm2

def id_computable {α : Type*} [ea : fin_encoding α] : computable_by_tm_2 (id: α → α) := begin
  let tr := id_computer α,
  use tr,
  use rfl,
  use rfl,
  intro l,
  have h : tm_2_evaluates_function_list tr (roption.some : list ea.Γ →. list ea.Γ) l rfl rfl :=
  begin
    simp,
    suffices h' : turing.TM2.step tr.M = (λ c, begin
      cases c.l,
      exact none,
      exact some (turing.TM2.cfg.mk none c.var c.stk)
    end ),
    {sorry},
    funext,
    cases x,
    cases x_l,
    simp,
    simp,
    have h : (tr.M x_l) = halt := rfl,
    conv in (tr.M x_l) {rw h},
    simp,
  end,
  simp [-tm_2_evaluates_function_list, ea.encodek],
  sorry
end
