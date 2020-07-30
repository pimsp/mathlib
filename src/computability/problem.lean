import tactic
import computability.primrec
import computability.reduce
import computability.tm_to_partrec
import computability.turing_machine
import data.zmod.basic
import data.equiv.list
import data.list.basic
open function

-- Some option construction

namespace option
def domain_add_option { α β : Type } : ( α → option β ) → ( option α → option β ) := begin
  intros f a,
  cases a,
  use none,
  use f a,
end
@[simp]
lemma domain_add_option_of_some { α β : Type } ( f : α → option β ) ( a : α ) : ( domain_add_option f ) ( some a ) =  f a :=
begin
  trivial,
end
end option

-- Problem namespace

namespace problem

structure problem (α : Type*) [encodable α] :=
(yesinstance : α → Prop)

def is_even : problem ℕ := {
  yesinstance := λ n, n%2 = 0,
  ..encodable.nat,
}

def is_odd : problem ℕ := {
  yesinstance := λ n, n%2 = 1,
  ..encodable.nat,
}

def partrec {α σ} [encodable α] [encodable σ]
  (f : α →. σ) := nat.partrec (λ n,
  roption.bind (encodable.decode α n) (λ a, (f a).map encodable.encode))

def computable {α σ} [encodable α] [encodable σ] (f : α → σ) := partrec (f : α →. σ)

namespace computable
protected theorem id {α : Type*} [encodable α]: computable (@id α) := sorry
end computable


def many_one_reducible {α β} [encodable α] [encodable β] (P : problem α) (Q : problem β) :=
∃ f : α → β, computable f ∧ ∀ a, P.yesinstance a ↔ Q.yesinstance (f a)
-- ∃ f : α → β, computable f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₀ `:1000 := many_one_reducible

lemma is_even_red_to_is_odd: is_even ≤₀ is_odd := begin
  use nat.succ,
  split,
  exact computable.succ,
  intro a,
  change a ≡ 0 [MOD 2] ↔ a+1≡1 [MOD 2],
  repeat {rw ← zmod.nat_coe_eq_nat_coe_iff},
  simp,
end

lemma is_odd_red_to_is_even: is_odd ≤₀ is_even := begin
  use nat.succ,
  split,
  exact computable.succ,
  intro a,
  change a ≡ 1 [MOD 2] ↔ a+1≡0 [MOD 2],
  repeat {rw ← zmod.nat_coe_eq_nat_coe_iff},
  split, {
    intro h,
    simp [h],
    ring,
  },
  intro h,
  apply add_right_cancel,
  simp at h,
  rw h,
  ring,
end

@[refl]
lemma many_one_reducible_refl {α} [encodable α] (P : problem α) :
  P ≤₀ P := ⟨id, computable.id, by simp⟩

-- @[trans]
-- theorem many_one_reducible.trans {α β γ} [encodable α] [encodable β] [encodable γ] {P : problem α} {Q : problem β} {R : problem γ} : P ≤₀ Q → Q ≤₀ R → P ≤₀ R
-- | ⟨f, c₁, h₁⟩ ⟨g, c₂, h₂⟩ := ⟨g ∘ f, c₂.comp c₁,
--   λ a, ⟨λ h, by rwa [←h₂, ←h₁], λ h, by rwa [h₁, h₂]⟩⟩

@[derive inhabited]
inductive propositional_formula (α : Type*)
| atom (a:α) : propositional_formula
| conj (a b: propositional_formula) : propositional_formula
| disj (a b: propositional_formula) : propositional_formula
| not (a:propositional_formula) : propositional_formula

-- Postfix territory
namespace propositional_formula
def to_postfix : (propositional_formula ℕ) → list ℕ
| (atom a) := [a+3]
| (conj a b) :=  (to_postfix a) ++ (to_postfix b) ++ [1]
| (disj a b) :=  (to_postfix a) ++ (to_postfix b) ++ [2]
| (not a) := (to_postfix a) ++ [0]

def from_postfix' : list ℕ → list ( propositional_formula ℕ ) → list ℕ × list ( propositional_formula ℕ )
| [] [f] := ([],[f])
| [] m := ([],[])
| (0::l) (f::m) := from_postfix' l ((not f)::m)
| (0::l) nil := ([],[])
| (1::l) (f::(g::m)) := from_postfix' l ((conj g f)::m)
| (1::l) m := ([],[])
| (2::l) (f::(g::m)) := from_postfix' l ((disj g f)::m)
| (2::l) m := ([],[])
| ((b+3)::l) m := from_postfix' l ((atom b)::m)

def from_postfix : list ℕ → option ( propositional_formula ℕ ) := λ l, list.head' ( from_postfix' l [] ).2

lemma from_to_postfix_id_aux (φ:propositional_formula ℕ) : ∀ l₁:list ℕ, ∀ l₂:list (propositional_formula ℕ), from_postfix' ( φ.to_postfix ++ l₁ ) l₂ = from_postfix' l₁ ( φ :: l₂ ) :=
begin
  induction φ, {
    intros l₁ l₂,
    trivial,
  }, {
    intros l₁ l₂,
    specialize φ_ih_a (φ_b.to_postfix ++ (1 :: l₁) ) l₂,
    specialize φ_ih_b (1 :: l₁) (φ_a :: l₂),
    calc from_postfix' ((φ_a.conj φ_b).to_postfix ++ l₁) l₂
        = from_postfix' ( φ_a.to_postfix ++ φ_b.to_postfix ++ [1] ++ l₁ ) l₂: by trivial
    ... = from_postfix' ( φ_a.to_postfix ++ ( φ_b.to_postfix ++ ( 1 :: l₁ ) ) ) l₂: by simp[list.append_assoc]
    ... = from_postfix' ( φ_b.to_postfix ++ (1 :: l₁) ) (φ_a :: l₂) : φ_ih_a
    ... = from_postfix' ( 1 :: l₁ ) ( φ_b :: φ_a :: l₂) : φ_ih_b
    ... = from_postfix' l₁ (φ_a.conj φ_b :: l₂) : by trivial,
  }, {
    intros l₁ l₂,
    specialize φ_ih_a (φ_b.to_postfix ++ (2 :: l₁) ) l₂,
    specialize φ_ih_b (2 :: l₁) (φ_a :: l₂),
    calc from_postfix' ((φ_a.disj φ_b).to_postfix ++ l₁) l₂
        = from_postfix' ( φ_a.to_postfix ++ φ_b.to_postfix ++ [2] ++ l₁ ) l₂: by trivial
    ... = from_postfix' ( φ_a.to_postfix ++ ( φ_b.to_postfix ++ ( 2 :: l₁ ) ) ) l₂: by simp[list.append_assoc]
    ... = from_postfix' ( φ_b.to_postfix ++ (2 :: l₁) ) (φ_a :: l₂) : φ_ih_a
    ... = from_postfix' ( 2 :: l₁ ) ( φ_b :: φ_a :: l₂) : φ_ih_b
    ... = from_postfix' l₁ (φ_a.disj φ_b :: l₂) : by trivial,
  }, {
    intros l₁ l₂,
    specialize φ_ih (0 :: l₁) l₂,
    calc from_postfix' ( (φ_a.not).to_postfix ++ l₁) l₂
        = from_postfix' ( φ_a.to_postfix ++ [0] ++ l₁ ) l₂: by trivial
    ... = from_postfix' ( φ_a.to_postfix ++ ( 0 :: l₁ ) ) l₂: by simp[list.append_assoc]
    ... = from_postfix' ( 0 :: l₁ ) ( φ_a :: l₂) : φ_ih
    ... = from_postfix' l₁ (φ_a.not :: l₂) : by trivial,
  },
end

end propositional_formula

namespace encodable
open propositional_formula
instance propositional_formula_nat : encodable (propositional_formula ℕ) := {
  encode := encodable.list.encode ∘ to_postfix,
  decode := ( option.domain_add_option from_postfix ) ∘ encodable.list.decode,
  encodek := begin
    intro φ,
    repeat {rw comp_app},
    let el := encodable.list.encodek,
    specialize el φ.to_postfix,
    rw el,
    simp,
    clear el,
    change list.head' ( from_postfix' (to_postfix φ) [] ).2 = some φ,
    let from_to_postfix_id := from_to_postfix_id_aux φ [] [],
    simp at from_to_postfix_id,
    rw from_to_postfix_id,
    trivial,
  end,
}
end encodable
-- End postfix territory

namespace propositional_formula
def eval {α : Type*} (f : α → Prop) : (propositional_formula α) → Prop
  | (atom a) := f a
  | (conj a b) := (eval a) ∧ (eval b)
  | (disj a b) := (eval a) ∨ (eval b)
  | (not a) := ¬(eval a)

-- propositional_formula.eval a = run tm_van_Daan (encode a)

-- note that singleton a = a is also a rec_list (but not a list)
-- inductive rec_list (α : Type*)
-- | nil : rec_list
-- | singleton (a:α) : rec_list
-- | singlelist (a : rec_list) : rec_list
-- | cons (hd : rec_list) (tl : rec_list) : rec_list -- think of this as [hd] concatenated with tl

-- notation h :: t  := rec_list.cons h t
-- notation `[` l:(foldr `, ` (h t, rec_list.cons h t) rec_list.nil `]`) := l

-- -- def encode_to_list {α : Type*} [h: primcodable α]: (propositional_formula α) → list ℕ
-- def encode_to_list : (propositional_formula ℕ) → rec_list ℕ
--   | (atom a) := rec_list.singleton a
--   | (conj a b) := [(encode_to_list a),rec_list.singleton 0,(encode_to_list b)]
--   | (disj a b) := [(encode_to_list a),rec_list.singleton 1,(encode_to_list b)]
--   | (not a) := [rec_list.singleton 0,(encode_to_list a)]

-- def decode_from_list : rec_list ℕ → option (propositional_formula ℕ)
--   | rec_list.nil : begin

end propositional_formula

def is_satisfiable {α : Type*} (p : propositional_formula α) : Prop :=
∃ f : α → Prop, p.eval f

def sat : problem (propositional_formula ℕ) :=
{ yesinstance := λ p, is_satisfiable p }

@[derive [decidable_eq, inhabited]]
inductive Γ' | blank | bit0 | bit1

def tr_pos_num : pos_num → list Γ'
| pos_num.one := [Γ'.bit1]
| (pos_num.bit0 n) := Γ'.bit0 :: tr_pos_num n
| (pos_num.bit1 n) := Γ'.bit1 :: tr_pos_num n

def tr_num : num → list Γ'
| num.zero := []
| (num.pos n) := tr_pos_num n

def tr_nat (n : ℕ) : list Γ' := tr_num n

namespace tm0
section
parameters (Λ : Type*) [inhabited Λ]

def machine := turing.TM0.machine Γ' Λ

example (α : Type*) (S : setoid α) (a : α) : quotient S :=
begin
  refine ⟦a⟧,
end

def list_to_list_blank {Γ : Type} [inhabited Γ] (L : list Γ) : turing.list_blank Γ :=
@quotient.mk (list Γ) (turing.blank_rel.setoid Γ) L

def run_tm0 {α : Type*} [encodable α] (tm : machine) (a : α) : roption (turing.list_blank Γ') :=
turing.TM0.eval tm (tr_nat (encodable.encode a))

def solved_by_turing_machine_0 {α : Type*} [encodable α] (P : problem α) (tm : machine) : Prop := (λ (a : α), run_tm0 tm a = roption.some (list_to_list_blank [Γ'.bit1])) = P.yesinstance ∧ ∀ (a : α), run_tm0 tm a ≠ roption.none
end
end tm0

structure turing_machine_0 :=
 (Λ : Type*)
 [Λ_inhabited : inhabited Λ]
 (M : tm0.machine Λ)

def solvable_by_turing_machine_0 {α : Type*} [encodable α] (P : problem α) : Prop :=
∃ (tm : turing_machine_0), @tm0.solved_by_turing_machine_0 tm.Λ tm.Λ_inhabited _ _ P tm.M

namespace tm2
section
parameters {K : Type*} [decidable_eq K] -- Index type of stacks
parameters (k₀ : K) -- input stack
parameters (Γ : K → Type*) -- Type of stack elements
parameters (input_alphabet : Γ k₀ = Γ')
-- parameters (Λ : Type*) -- Type of function labels
-- parameters (σ : Type*) -- Type of variable settings

-- def stmt' := turing.TM2.stmt Γ Λ σ

-- def machine := Λ → stmt'


end
end tm2



end problem
