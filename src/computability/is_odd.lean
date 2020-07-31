import tactic
import .problem

namespace tm2program
open turing.TM2
open turing.TM2.stmt
open problem

section

inductive K₀
| nat_to_list_aux

@[derive decidable_eq]
inductive vars₀
| temp
open vars₀

inductive Λ₀
| nat_to_list₁ ( n : ℕ ) ( f : K₀ ) ( t : K₀ )
open Λ₀


parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (k₀ : K) -- input stack
parameters (lK : K₀ → K)

parameters (Λ : Type*) -- Type of function labels
parameters (lΛ : Λ₀ → Λ)
parameters (vars : Type) [decidable_eq vars]
parameters (lv : vars₀ → vars) 


def σ := vars → option Γ' 

/-
inductive stmt
| push : ∀ k, (σ → Γ k) → stmt → stmt
| peek : ∀ k, (σ → option (Γ k) → σ) → stmt → stmt
| pop : ∀ k, (σ → option (Γ k) → σ) → stmt → stmt
| load : (σ → σ) → stmt → stmt
| branch : (σ → bool) → stmt → stmt → stmt
| goto : (σ → Λ) → stmt
| halt : stmt
open stmt
-/

-- inductive Γ' | blank | bit0 | bit1 | left | right | comma

def Γ : K → Type := λ k : K, Γ' 

def s := stmt Γ Λ σ 
--inductive Γ' | blank | bit0 | bit1 | bra | ket | comma 

-- def const : K₀ → σ → Γ' := λ t _, t 

def set_var : vars₀ → σ → option Γ' → σ := λ v f s x, if lv v = x then s else f x
def get_var : vars₀ → Γ' → σ → Γ' := λ v d f, option.cases_on (f(lv v)) d (λ x, x) 
def get_var' : vars₀ → σ → Γ' := λ v, get_var v Γ'.blank 
def ignore : σ → option Γ' → σ := λ f _, f
def goto' : Λ₀ → stmt Γ Λ σ  := λ l, goto (λ _, lΛ (l) )

def func_nat_to_list₁ ( f : K₀ ) ( t : K₀ ) : ℕ → stmt Γ Λ σ 
| 0 :=
   pop (lK f) ignore $
   pop (lK t) ignore $
   push (lK t) ( λ _, Γ'.comma ) $
   push (lK t) ( λ _, Γ'.ket ) $
   goto' $ nat_to_list₁ 1 f t
| 1 := 
   pop (lK f) (set_var temp) $
   branch ( λ f:σ, f (lv temp) = Γ'.comma ) (
      goto' $ nat_to_list₁ 1 f t
   ) (
      push (lK t) ( λ _, Γ'.comma ) $
      push (lK t) (get_var' temp) $ 
      goto' $ nat_to_list₁ 2 f t
   ) 
| _ := 
   push (lK t) ( λ _, Γ'.bra ) $
   push (lK t) ( λ _, Γ'.bra ) $
   pop (lK f) ignore $
   push (lK f) ( λ _, Γ'.bra ) $
   halt 


end
end tm2program