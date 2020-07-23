import computability.primrec
import computability.reduce
open function

namespace problem

structure problem (α : Type*) extends primcodable α :=
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

def many_one_reducible {α β} (P : problem α) (Q : problem β) :=
∃ f : α → β, @computable α β P.to_primcodable Q.to_primcodable f ∧ ∀ a, P.yesinstance a ↔ Q.yesinstance (f a)
-- ∃ f : α → β, computable f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₀ `:1000 := many_one_reducible

lemma is_even_red_to_is_odd: is_even ≤₀ is_odd := begin
  use nat.succ,
  split,
  exact computable.succ,
  intro a,
  split, {
    intro ah,
    change a.succ % 2 = 1,
    have ah' : a % 2 = 0, exact ah,
  }

end

end problem