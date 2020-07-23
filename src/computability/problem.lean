import computability.primrec
import computability.reduce
open function

structure problem (α : Type*) extends primcodable α :=
(yesinstance : α → Prop)

instance : primcodable ℕ := { 
  encode := id,
  decode := some,
  encodek := by simp,
  prim := nat.primrec.succ 
} 

def is_even [h : primcodable ℕ]: problem ℕ := { 
  yesinstance := λ n, n%2 = 1,
  ..h,
}


def is_odd [h : primcodable ℕ]: problem ℕ := { 
  yesinstance := λ n, n%2 = 0,
  ..h,
}

def many_one_reducible {α β} (P : problem α) (Q : problem β) (p : α → Prop) (q : β → Prop) :=
∃ f, computable f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₀ `:1000 := many_one_reducible
