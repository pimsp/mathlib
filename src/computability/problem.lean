import tactic
import computability.primrec
import computability.reduce
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

lemma even_add_odd_is_odd (a:ℤ) (b:ℤ): b%2=1 → ( a%2=0 ↔ (a+b)%2=1 ) := begin
  intro bh,
  split, {
    intro ah,
    calc (a+b) % 2 = (a%2+b%2)%2 : by simp
    ... = (0+1)%2 : by rw [ah,bh]
    ... = 1 : by ring,
  },
  intro ah,
  calc a % 2 = (a+2*b)%2 : by simp
  ... = (a+b+b)%2 : by ring
  ... = ((a+b)%2 + b%2)%2 : by simp
  ... = (1+1)%2 : by rw [ah,bh]
  ... = 0 : by ring,
end

lemma is_even_red_to_is_odd: is_even ≤₀ is_odd := begin
  use nat.succ,
  split,
  exact computable.succ,
  intro a,
  have h1 :(1:ℤ)%2=1 := by ring,
  have h2 :↑(2:ℕ) = (2:ℤ) := by simp,
  change a%2 = 0 ↔ (a+1) % 2 = 1,
  split, {
    intro ah,
    apply int.coe_nat_inj,
    apply (even_add_odd_is_odd a 1 h1).mp,
    rw ← h2,
    rw ← int.coe_nat_mod,
    rw ah,
    ring,
  }, {
    intro ah,
    apply int.coe_nat_inj,
    dsimp,
  }
end

end problem
