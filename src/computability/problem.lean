import tactic
import computability.primrec
import computability.reduce
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

end problem
