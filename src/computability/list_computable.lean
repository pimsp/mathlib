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

def tm_evaluates_function (tm : machine) (f : list (Γ k₀) →. list (Γ k₁)) (l : list (Γ k₀)) :=
turing.eval (turing.TM2.step tm) (init_list l) = (roption.map halt_list) (f l)

private def computable_by_tm_aux (f : list (Γ k₀) →. list (Γ k₁)) := ∃ tm : machine, ∀ (l : list (Γ k₀)), tm_evaluates_function tm f l

section
parameters [finset σ]
parameters [finset (Γ k₀)]

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
 [σ_fin : finset σ]
 [Γk₀_fin : finset (Γ k₀)]
 (M : tm2.machine Γ Λ σ)

variable my_tm : fin_turing_machine_2

def tm_2_evaluates_function {Γ Γ' : Type*} (tm : fin_turing_machine_2) (f : list Γ →. list Γ') (l : list Γ) (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ') : Prop := @tm2.tm_evaluates_function tm.K tm.K_decidable_eq tm.k₀ tm.k₁ tm.Γ tm.Λ tm.Λ_inhabited tm.σ tm.σ_inhabited tm.M (λ l:list (tm.Γ tm.k₀), begin rw hi at l, rw ho, exact f l, end) begin rw hi, exact l end

def computable_by_tm_2 {Γ Γ' : Type*} (f : list Γ →. list Γ') : Prop :=
∃ (tm : fin_turing_machine_2) (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ'), ∀ l, tm_2_evaluates_function tm f l hi ho
