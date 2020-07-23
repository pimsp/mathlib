import tactic
import computability.primrec
import computability.reduce
import computability.tm_to_partrec
import data.zmod.basic
open function

namespace problem

structure problem (α : Type*) [primcodable α] :=
(yesinstance : α → Prop)

instance : primcodable ℕ := {
  encode := id,
  decode := some,
  encodek := by simp,
  prim := nat.primrec.succ
}

def is_even [h : primcodable ℕ]: problem ℕ := {
  yesinstance := λ n, n%2 = 0,
  ..h,
}

def is_odd [h : primcodable ℕ]: problem ℕ := {
  yesinstance := λ n, n%2 = 1,
  ..h,
}

def many_one_reducible {α β} [primcodable α] [primcodable β] (P : problem α) (Q : problem β) :=
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
lemma many_one_reducible_refl {α} [primcodable α] (P : problem α) :
  P ≤₀ P := ⟨id, computable.id, by simp⟩

@[trans]
theorem many_one_reducible.trans {α β γ} [primcodable α] [primcodable β] [primcodable γ] {P : problem α} {Q : problem β} {R : problem γ} : P ≤₀ Q → Q ≤₀ R → P ≤₀ R
| ⟨f, c₁, h₁⟩ ⟨g, c₂, h₂⟩ := ⟨g ∘ f, c₂.comp c₁,
  λ a, ⟨λ h, by rwa [←h₂, ←h₁], λ h, by rwa [h₁, h₂]⟩⟩

-- structure algorithm {α : Type*} [primcodable α] (P : problem α) :=
-- (K : Type*)
-- (decstack : decidable_eq K) -- Index type of stacks
-- (Γ : K → Type*) -- Type of stack elements
-- (Λ : Type*) -- Type of function labels
-- (σ : Type*) -- Type of variable settings
-- (tm : Λ → (turing.TM2.stmt (λ _:K, Γ) Λ (option Γ)))

inductive propositional_formula (α : Type*)
| atom (a:α) : propositional_formula
| conj (a b: propositional_formula) : propositional_formula
| disj (a b: propositional_formula) : propositional_formula
| not (a:propositional_formula) : propositional_formula

-- note that singleton a = a is also a rec_list (but not a list)
inductive rec_list (α : Type*)
| nil : rec_list
| singleton (a:α) : rec_list
| singlelist (a : rec_list) : rec_list
| cons (hd : rec_list) (tl : rec_list) : rec_list -- think of this as [hd] concatenated with tl

namespace propositional_formula
def eval {α : Type*} (f : α → Prop) : (propositional_formula α) → Prop
  | (atom a) := f a
  | (conj a b) := (eval a) ∧ (eval b)
  | (disj a b) := (eval a) ∨ (eval b)
  | (not a) := ¬(eval a)

notation h :: t  := rec_list.cons h t
notation `[` l:(foldr `, ` (h t, rec_list.cons h t) rec_list.nil `]`) := l

-- def encode_to_list {α : Type*} [h: primcodable α]: (propositional_formula α) → list ℕ
def encode_to_list : (propositional_formula ℕ) → rec_list ℕ
  | (atom a) := rec_list.singleton a
  | (conj a b) := [(encode_to_list a),rec_list.singleton 0,(encode_to_list b)]
  | (disj a b) := [(encode_to_list a),rec_list.singleton 1,(encode_to_list b)]
  | (not a) := [rec_list.singleton 0,(encode_to_list a)]

-- def decode_from_list : rec_list ℕ → option (propositional_formula ℕ)
--   | rec_list.nil : begin

end propositional_formula

def is_satisfiable {α : Type*} (p : propositional_formula α) : Prop :=
∃ f : α → Prop, p.eval f

instance prop_prim : primcodable (propositional_formula ℕ) := sorry

def sat : problem (propositional_formula ℕ) :=
{ yesinstance := λ p, is_satisfiable p }

end problem
