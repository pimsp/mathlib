import tactic
import data.list
import data.list.basic
import .problem

namespace tm2program
open turing.TM2
open turing.TM2.stmt
open problem

section

inductive K₀
| t1 | t2
parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (lK : K₀ → K)
parameters (k₀ : K) -- input stack
parameters (k₁ : K) -- output stack
parameters (k₂ : K) -- call stack
parameters (h₀₂: k₀ ≠ k₂) -- input stack is not the call stack

@[derive decidable_eq]
inductive vars₀
| temp
open vars₀
parameters {vars : Type} [decidable_eq vars]
parameters (lv : vars₀ → vars) 

inductive Λ₀
| copy_rec ( f : K ) ( t : K ) ( n : fin 2 ) 
| copy_rec₂ ( f : K ) ( t : K ) ( n : fin 1 ) 
| pop_rec ( t : K ) ( n : fin 1 ) 
| list_head ( f : K ) ( t : K ) ( n : fin 2 ) 
| nat_to_list₂ ( f : K ) ( t : K ) ( n : fin 1 )  
open Λ₀

parameters (Λ : Type) -- Type of function labels
parameters (lΛ : Λ₀ → Λ)

def σ := (vars → option Γ') × Λ 


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
def Γ: K → Type := λ k, if k = k₂ then Λ else Γ'



def stmt' := turing.TM2.stmt Γ Λ σ 
--inductive Γ' | blank | bit0 | bit1 | bra | ket | comma 

/-def set_var : vars₀ → σ → option Γ' → σ := λ v f s x, if lv v = x then s else f x
def get_var : vars₀ → Γ' → σ → Γ' := λ v d f, option.cases_on (f(lv v)) d (λ x, x) 
def get_var' : vars₀ → σ → Γ' := λ v, get_var v Γ'.blank 
def ignore : σ → option Γ' → σ := λ f _, f
def goto' : Λ₀ → stmt'  := λ l, goto (λ _, lΛ (l) )
def var_eq : vars₀ → Γ' → σ → bool := λ v x f, f (lv v) = x
def var_undef : vars₀ → σ → bool := λ v f, f (lv v) = none-/

--attribute [class] ne

/-lemma ne_call_stack {k:K} (h:k≠k₂): Γ k = Γ' :=
begin
   change (if k = k₂ then Λ else Γ') = Γ',
   simp [h],
end
def push_const {k:K} (h:k≠k₂) : Γ' → stmt' → stmt' := λ g e, push k ( λ σ, begin
   rw ne_call_stack k₂ Λ h,
   exact g,
end ) e 
def pop' {k:K} (h:k≠k₂) : (σ → option Γ' → σ) → stmt' → stmt' := λ f e, pop k begin 
   rw ne_call_stack k₂ Λ h,
   exact f, 
end e -/

-- rec_list

namespace rec_list
@[derive inhabited]
inductive rec_list 
| empty   : rec_list
| string  : list(bool) → rec_list → rec_list
| sublist : rec_list → rec_list → rec_list

def string_to_bits : list bool → list Γ' := list.map (λ b:bool, ite b Γ'.bit1 Γ'.bit0 )
def bits_to_string : list Γ' → list bool := list.map (λ c:Γ', c = Γ'.bit1 )
@[simp] 
lemma string_to_bits_to_string (l:list bool): bits_to_string ( string_to_bits l) = l :=
begin
   let f : bool → Γ' := (λ b:bool, ite b Γ'.bit1 Γ'.bit0 ),
   let g : Γ' → bool := (λ c:Γ', c = Γ'.bit1 ),
   have h : g ∘ f = id, ext, induction x, repeat {refl},
   change list.map g ( list.map f l ) = l,
   simp [h],
end

def symbol_sign : Γ' → ℤ | Γ'.bra := 1 | Γ'.ket := -1 | _ := 0 
def stack_depth : list Γ' → list ℤ := list.scanl (λ d g, d + symbol_sign g) 0
def index_of_comma₁ : list Γ' → ℕ := λ l, (l.zip (stack_depth l)).index_of (Γ'.comma,0)
def pop_ends : list Γ' → list Γ'  := λ l, l.tail.reverse.tail.reverse  

def split_stack₁ : list Γ' → list Γ' × list Γ' := λ l, l.split_at $ index_of_comma₁ l 
def split_stackₐ' : list Γ' → list(list(Γ'×ℤ)) := λ l, (l.zip (stack_depth l)).split_on (Γ'.comma,0)
def split_stackₐ : list Γ' → list(list(Γ')) := λ l₁, list.map ( λ l₂, list.map ( λ x:Γ'×ℤ, x.1 ) l₂ ) $ split_stackₐ' l₁

lemma split_stack_dec₁ (l:list Γ') (h:l≠[]): (split_stack₁ l).1.length < l.length :=
begin
   sorry,
end
lemma split_stack_dec₂ (l:list Γ') (h:l≠[]): (split_stack₁ l).2.length < l.length :=
begin
   sorry,
end

def rec_list_to_stack : rec_list → list Γ'
| (rec_list.empty) := []
| (rec_list.sublist l' l) := ([Γ'.bra]++rec_list_to_stack l'++[Γ'.ket])++(Γ'.comma::rec_list_to_stack l)
| (rec_list.string b l) := (string_to_bits b)++(Γ'.comma::rec_list_to_stack l)

def stack_to_rec_list' : list Γ' → rec_list
| [] := rec_list.empty
| (Γ'.bra::l) := rec_list.sublist (stack_to_rec_list' $ pop_ends (split_stack₁ l).1) $ stack_to_rec_list' (split_stack₁ l).2
| l := rec_list.string (bits_to_string (split_stack₁ l).1) $ stack_to_rec_list' (split_stack₁ l).2



-- edge case elimination

def no_call_stack: K → K := λ k, if k=k₂ then k₀ else k
include h₀₂
lemma no_call_stack_elim (k:K): Γ ( no_call_stack k ) = Γ' :=
begin
   change (if (if k=k₂ then k₀ else k) = k₂ then Λ else Γ') = Γ',
   cases _inst_1 k k₂ with h h, simp [h],
   exact if_neg h₀₂,
end
def no_option: option Γ' → Γ' := λ l, option.cases_on l Γ'.blank id 

-- syntactic sugar
def push_const: K → Γ' → stmt' → stmt' := λ k g e, push (no_call_stack k) (λ f,by{ rw no_call_stack_elim _ _ h₀₂, use g,}) e
def push_var: K → vars → stmt' → stmt' := λ k v e, push (no_call_stack k) (λ f,by{ rw no_call_stack_elim _ _ h₀₂, use no_option _ _ h₀₂ (f.1 v),}) e
def discard: K → stmt' → stmt' := λ k e, pop k (λ f g, f) e
def pop_var: K → vars → stmt' → stmt' := λ k v e, pop (no_call_stack k) (λ f g, (λ w, if v = w then by{ rw ← no_call_stack_elim _ _ h₀₂, use g, } else f.1 w, f.2)) e 
def goto' : Λ₀ → stmt'  := λ l, goto (λ _, lΛ (l) )
def var_eq_const : vars → Γ' → σ → bool := λ v x f, f.1 v = x
def var_undef : vars → σ → bool := λ v f, f.1 v = none
def call : Λ → Λ → stmt' := λ a b, push k₂ (λ f, begin 
   change (if k₂ = k₂ then Λ else Γ'),
   simp,
   use b,
end) $ goto (λ _, a)
def return : stmt' := pop k₂ begin
   intros f g,
   change option (if k₂ = k₂ then Λ else Γ') at g,
   simp at g,
   cases g, use f,
   use (f.1,g),
end $ goto (λ f, f.2)

-- programs

def func_nat_to_list₂ (f:K) (t:K): ℕ → stmt Γ Λ σ 
| 0 := 
   push_const t Γ'.comma $ 
   push_const t Γ'.ket $
   goto' $ nat_to_list₂ f t 1
| _ := 
   pop_var f (lv temp) $
   branch (var_eq_const (lv temp) Γ'.comma) (
      push_const t Γ'.bra $
      return 
   ) (
      push_const t Γ'.comma $
      push_var t (lv temp) $ 
      goto' $ nat_to_list₂ f t 1
   ) 

/-def func_nat_to_list₂ (f:K) (t:K) (t₂:t≠k₂) (f₂:f≠k₂): ℕ → stmt Γ Λ σ 
| 0 := 
   push_const t₂ Γ'.comma $ 
   push_const t₂ Γ'.ket $
   goto' $ nat_to_list₂ f t 1
| _ := 
   pop' f₂ (set_var temp) $
   branch (var_eq temp Γ'.comma) (
      push_const t₂ Γ'.bra $
      halt 
   ) (
      push_const t₂ Γ'.comma $
      push_var t₂ temp $ 
      goto' $ nat_to_list₂ f t 1
   ) -/

-- f = t is not allowed, reverses
def func_copy_rec₂ (f : K) (t : K): ℕ → stmt Γ Λ σ 
| 0 := 
   push_const (lK K₀.t1) Γ'.comma $
   goto' $ copy_rec₂ f t 1
| _ := 
   pop_var f (lv temp) $
   branch (var_eq_const (lv temp) Γ'.bra) (
      push_const t Γ'.ket $
      push_const t Γ'.comma $
      push_const (lK K₀.t1) Γ'.bit1 $
      goto' $ copy_rec₂ f t 1
   ) $
   branch (var_eq_const (lv temp) Γ'.ket) (
      discard t $
      push_const t Γ'.bra $
      discard (lK K₀.t1) $
      goto' $ copy_rec₂ f t 1
   ) $
   branch (var_eq_const (lv temp) Γ'.comma) (
      push_const t Γ'.comma $
      pop_var (lK K₀.t1) (lv temp) $
      branch (var_eq_const (lv temp) Γ'.bit1) (
         goto' $ copy_rec₂ f t 1
      ) $
      return
   ) $
   push_var t (lv temp) $
   goto' $ copy_rec₂ f t 1

-- f = t is allowed, does not reverse
def func_copy_rec (f : K) (t : K): ℕ → stmt Γ Λ σ 
| 0 :=   call (lΛ (copy_rec₂ f (lK K₀.t2) 0) ) (lΛ (copy_rec f t 1) )
| 1 :=   call (lΛ (copy_rec₂ (lK K₀.t2) t 0) ) (lΛ (copy_rec f t 2) )
| _ :=   return

def func_pop_rec (f : K): ℕ → stmt Γ Λ σ 
| 0 := 
   push_const (lK K₀.t1) Γ'.comma $
   goto' $ pop_rec f 1
| _ := 
   pop_var f (lv temp) $
   branch (var_eq_const (lv temp) Γ'.bra) (
      push_const (lK K₀.t1) Γ'.bit1 $
      goto' $ pop_rec f 1
   ) $
   branch (var_eq_const (lv temp) Γ'.ket) (
      discard (lK K₀.t1) $
      goto' $ pop_rec f 1
   ) $
   branch (var_eq_const (lv temp) Γ'.comma) (
      pop_var (lK K₀.t1) (lv temp) $
      branch (var_eq_const (lv temp) Γ'.bit1) (
         goto' $ pop_rec f 1
      ) $
      return
   ) $
   goto' $ pop_rec f 1

/-def func_clear_stack (t : K): ℕ → stmt Γ Λ σ 
| _ := 
   pop_var t (lv temp) $
   branch (var_undef (lv temp)) return $
   goto' $ clear_stack t 0-/

def func_list_head (f : K) (t : K): ℕ → stmt Γ Λ σ 
| 0 :=   discard f $
         call (lΛ (copy_rec f t 0)) (lΛ (list_head f t 1))
| 1 :=   push_const f Γ'.bra $
         call (lΛ (pop_rec f 0)) (lΛ (list_head f t 2))
| _ :=   return

end
end tm2program