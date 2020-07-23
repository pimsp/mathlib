import computability.primrec

structure problem (α : Type*) extends primcodable α :=
(yesness : α → Prop)

-- instance : problem ℕ is_even :=

example (α : Type) : α → option α :=
begin
  exact some,
end

def is_even : problem ℕ :=
{ encode := id,
  decode := some,
  encodek := by simp,
  prim := begin
    sorry,
  end,
  yesness := λ n, n%2 = 0}
