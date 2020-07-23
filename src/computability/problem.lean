import computability.primrec

structure problem (α : Type*) extends primcodable α :=
(yesinstance : α → Prop)

-- instance : problem ℕ is_even :=

example (α : Type) some α:

def is_even : problem ℕ :=
{ encode := id,
  decode := some,
  encodek := by simp only [forall_const, id.def, eq_self_iff_true],
  prim := nat.primrec.succ,
  yesinstance := λ n, n%2 = 0}

def is_odd : problem ℕ :=
{ encode := id,
  decode := some,
  encodek := by simp only [forall_const, id.def, eq_self_iff_true],
  prim := nat.primrec.succ,
  yesinstance := λ n, n%2 = 1}

def many_one_reducible {α β} (P : problem α) (Q : problem β) (p : α → Prop) (q : β → Prop) :=
∃ f, computable f ∧ ∀ a, p a ↔ q (f a)

infix ` ≤₀ `:1000 := many_one_reducible
