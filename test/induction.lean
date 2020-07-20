import tactic.induction
import tactic.linarith

universes u v w

inductive le : ℕ → ℕ → Type
| zero {n} : le 0 n
| succ {n m} : le n m → le (n + 1) (m + 1)

inductive lt : ℕ → ℕ → Type
| zero {n} : lt 0 (n + 1)
| succ {n m} : lt n m → lt (n + 1) (m + 1)

inductive Fin : ℕ → Type
| zero {n} : Fin (n + 1)
| succ {n} : Fin n → Fin (n + 1)

inductive List (α : Sort*) : Sort*
| nil {} : List
| cons {} (x : α) (xs : List) : List

namespace List

def append {α} : List α → List α → List α
| nil ys := ys
| (cons x xs) ys := cons x (append xs ys)

end List

inductive Vec (α : Sort u) : ℕ → Sort (max 1 u)
| nil : Vec 0
| cons {n} : α → Vec n → Vec (n + 1)

namespace Vec

inductive eq {α} : ∀ n m, Vec α n → Vec α m → Prop
| nil : eq 0 0 nil nil
| cons {n m} {xs : Vec α n} {ys : Vec α m} {x y : α} :
  x = y →
  eq n m xs ys →
  eq (n + 1) (m + 1) (cons x xs) (cons y ys)

end Vec

inductive Two : Type | zero | one

inductive ℕ' : Type
| intro : ℕ → ℕ'

example (k) : 0 + k = k :=
begin
  induction' k,
  { refl },
  { simp }
end

example {k} (fk : Fin k) : Fin (k + 1) :=
begin
  induction' fk,
  { exact Fin.zero },
  { exact Fin.succ ih }
end

example {α} (l : List α) : l.append List.nil = l :=
begin
  induction' l,
  { refl },
  { dsimp only [List.append],
    exact (congr_arg _ ih)
  }
end

example {k l} (h : lt k l) : le k l :=
begin
  induction' h,
  { exact le.zero },
  { exact le.succ ih }
end

example {k l} : lt k l → le k l :=
begin
  induction' k; induction' l; intro hlt,
  { cases hlt },
  { exact le.zero },
  { cases hlt },
  { cases hlt,
    exact le.succ (@ih l hlt_a),
  }
end

example {α n m} {xs : Vec α n} {ys : Vec α m} (h : Vec.eq n m xs ys) : n = m :=
begin
  induction' h,
  case nil {
    refl
  },
  case cons {
    exact congr_arg nat.succ ih,
  }
end

-- A simple induction with complex index arguments.
example {k} (h : lt (k + 1) k) : false :=
begin
  induction' h,
  { exact ih }
end

-- A more complex induction with complex index arguments. Note the dependencies
-- between index arguments.
example {α : Sort u} {x y n m} {xs : Vec α n} {ys : Vec α m}
  : Vec.eq (n + 1) (m + 1) (Vec.cons x xs) (Vec.cons y ys)
  → Vec.eq n m xs ys :=
begin
  intro h,
  induction' h,
  exact h_1
end

-- It also works with cases'.
example {α : Sort u} {x y n m} {xs : Vec α n} {ys : Vec α m}
  : Vec.eq (n + 1) (m + 1) (Vec.cons x xs) (Vec.cons y ys)
  → Vec.eq n m xs ys :=
begin
  intro h,
  cases' h,
  exact h_1
end

-- This example requires elimination of cyclic generalised index equations.
example (n : ℕ) (h : n = n + 3) : false :=
begin
  success_if_fail { cases h },
  induction' h
end

-- It also works with cases'.
example (n : ℕ) (h : n = n + 3) : false :=
begin
  success_if_fail { cases h },
  cases' h
end

-- This example tests type-based naming.
example (k : ℕ') (i : ℕ') : ℕ :=
begin
  induction' k,
  induction' i,
  exact (n + m)
end

-- For constructor arguments that are propositions, the default name is "h".
-- For non-propositions, it is "x".
inductive nat_or_positive
| nat : ℕ' → nat_or_positive
| positive (n : ℕ) : n > 0 → nat_or_positive

example (n : nat_or_positive) : unit :=
begin
  cases' n,
  case nat {
    guard_hyp x := ℕ',
    exact ()
  },
  case positive {
    guard_hyp n := ℕ,
    guard_hyp h := n > 0,
    exact ()
  }
end

-- By default, induction' generates the most general possible induction
-- hypothesis.
example {n m : ℕ} : n + m = m + n :=
begin
  induction' m,
  case zero { simp },
  case succ : k IH {
    guard_hyp k := ℕ,
    guard_hyp n := ℕ,
    guard_hyp IH := ∀ {n}, n + k = k + n,
    ac_refl
  }
end

-- If we don't want a hypothesis to be generalised, we can say so with a
-- "fixing" clause.
example {n m : ℕ} : n + m = m + n :=
begin
  induction' m fixing n,
  case zero { simp },
  case succ : k IH {
    guard_hyp k := ℕ,
    guard_hyp n := ℕ,
    guard_hyp IH := n + k = k + n,
    ac_refl
  }
end

-- We can also fix all hypotheses. This gives us the behaviour of stock
-- `induction`. Hypotheses which depend on the eliminee still get generalised.
example {n m k : ℕ} (h : n + m = k) : n + m = k :=
begin
  induction' n fixing *,
  case zero { simp [*] },
  case succ : n IH {
    guard_hyp n := ℕ,
    guard_hyp m := ℕ,
    guard_hyp k := ℕ,
    guard_hyp h := n.succ + m = k,
    guard_hyp IH := n + m = k → n + m = k,
    -- Neither m nor k were generalised.
    exact h
  }
end

-- We can also generalise only certain hypotheses using a `generalizing`
-- clause. This gives us the behaviour of stock `induction ... generalizing`.
-- Hypotheses which depend on the eliminee get generalised even if they are not
-- mentioned in the `generalizing` clause.
example {n m k : ℕ} (h : n + m = k) : n + m = k :=
begin
  induction' n generalizing k,
  case zero { simp [*] },
  case succ : n IH {
    guard_hyp n := ℕ,
    guard_hyp m := ℕ,
    guard_hyp k := ℕ,
    guard_hyp h := n.succ + m = k,
    guard_hyp IH := ∀ {k}, n + m = k → n + m = k,
    -- k was generalised, but m was not.
    exact h
  }
end

-- Sometimes generalising a hypothesis H does not give us a more general
-- induction hypothesis. In such cases, induction' should not generalise H. The
-- following example is not realistic, but situations like this can occur in
-- practice; see accufact_1_eq_fact below.
example (n m k : ℕ) : m + k = k + m :=
begin
  induction' m,
  case zero { simp },
  case succ {
    guard_hyp ih := ∀ k, m + k = k + m,
    -- k was generalised because this makes the IH more general.
    -- n was not generalised -- if it had been, the IH would be
    --
    --     ∀ n k, m + k = k + m
    --
    -- with one useless additional argument.
    linarith
  }
end

-- This example checks that constructor arguments don't 'steal' the names of
-- generalised hypotheses.
example (n : list ℕ) (n : ℕ) : list ℕ :=
begin
  -- this performs induction on (n : ℕ)
  induction' n,
  { exact n },
  { -- n is the list, which was automatically generalized and keeps its name.
    -- n_1 is the recursive argument of `nat.succ`. It would be called `n` if
    -- there wasn't already an `n` in the context.
    exact (n_1 :: n)
  }
end

-- This example tests whether `induction'` gets confused when there are
-- additional cases around.
example (k : ℕ) (t : Two) : 0 + k = k :=
begin
  cases t,
  induction' k,
  { refl },
  { simp },
  induction' k,
  { refl },
  { simp }
end

-- The type of the induction premise can be a complex expression so long as it
-- normalises to an inductive (possibly applied to params/indexes).
example (n) : 0 + n = n :=
begin
  let T := ℕ,
  change T at n,
  induction' n; simp
end

-- Fail if the type of the induction premise is not an inductive type
example {α} (x : α) (f : α → α) : unit :=
begin
  success_if_fail { induction' x },
  success_if_fail { induction' f },
  exact ()
end

-- The following example used to trigger a bug where eliminate would generate
-- hypotheses with duplicate names.
structure fraction : Type :=
(num           : ℤ)
(denom         : ℤ)
(denom_ne_zero : denom ≠ 0)

lemma fraction.ext (a b : fraction) (hnum : fraction.num a = fraction.num b)
    (hdenom : fraction.denom a = fraction.denom b) :
  a = b :=
begin
  cases' a,
  cases' b,
  guard_hyp num := ℤ,
  guard_hyp denom := ℤ,
  guard_hyp num_1 := ℤ,
  guard_hyp denom_1 := ℤ,
  rw fraction.mk.inj_eq,
  exact and.intro hnum hdenom
end

-- A "with" clause can be used to give the names of constructor arguments (as
-- for `cases`, `induction` etc).
example (x : ℕ × ℕ) (y : Vec ℕ 2) (z : List ℕ) : unit :=
begin
  cases' x with i j k l,
  guard_hyp i := ℕ,
  guard_hyp j := ℕ,
  clear i j,

  cases' y with i j k l,
  -- TODO Note that i is 'skipped' because it is used to name the (n : ℕ)
  -- argument of `cons`, but that argument is cleared by index unification. I
  -- find this a little strange, but `cases` also behaves like this.
  guard_hyp j := ℕ,
  guard_hyp k := Vec ℕ 1,
  clear j k,

  cases' z with i j k l,
  case nil { exact () },
  case cons {
    guard_hyp i := ℕ,
    guard_hyp j := List ℕ,
    exact ()
  }
end

-- "with" also works with induction'.
example (x : List ℕ) : unit :=
begin
  induction' x with i j k l,
  case nil { exact () },
  case cons {
    guard_hyp i := ℕ,
    guard_hyp j := List ℕ,
    guard_hyp k := unit,
    exact ()
  }
end

-- An underscore in a "with" clause means "use the auto-generated name for this
-- argument".
example (x : List ℕ) : unit :=
begin
  induction' x with _ j _ l,
  case nil { exact () },
  case cons {
    guard_hyp x := ℕ,
    guard_hyp j := List ℕ,
    guard_hyp ih := unit,
    exact ()
  }
end

-- induction' and cases' can be used to perform induction/case analysis on
-- arbitrary expressions (not just hypotheses). A very synthetic example:
example {α} : α ∨ ¬ α :=
begin
  cases' classical.em α with a nota,
  { exact (or.inl a) },
  { exact (or.inr nota) }
end

-- Cases'/induction' can add an equation witnessing the case split they
-- performed. Again, a highly synthetic example:
example {α} (xs : list α)
  : xs.reverse.length = 0 ∨ ∃ m, xs.reverse.length = m + 1 :=
begin
  cases' eq : xs.length,
  case zero {
    left,
    rw list.length_reverse,
    exact eq
  },
  case succ : l {
    right,
    rw list.length_reverse,
    use l,
    exact eq
  }
end

--------------------------------------------------------------------------------
-- Jasmin's original use cases
--------------------------------------------------------------------------------

/- Head induction for transitive closure -/

inductive star {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c

namespace star

variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

lemma head (hab : r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc fixing hab,
  case refl {
    exact refl.tail hab },
  case tail : c d hbc hcd hac {
    exact hac.tail hcd }
end

-- In this example, induction' must apply the dependent recursor for star; the
-- nondependent one doesn't apply.
lemma head_induction_on {P : ∀a : α, star r a b → Prop} {a} (h : star r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : star r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction' h,
  case refl {
    exact refl
  },
  case tail : b c hab hbc ih {
    apply ih,
    { exact head hbc _ refl, },
    { intros _ _ hab _, exact head hab _}
  }
end

end star


/- Factorial -/

def accufact : ℕ → ℕ → ℕ
| a 0       := a
| a (n + 1) := accufact ((n + 1) * a) n

lemma accufact_1_eq_fact (n : ℕ) :
  accufact 1 n = nat.fact n :=
have accufact_eq_fact_mul : ∀m a, accufact a m = nat.fact m * a :=
  begin
    intros m a,
    induction' m,
    case zero {
      simp [nat.fact, accufact] },
    case succ {
      simp [nat.fact, accufact, ih, nat.succ_eq_add_one],
      cc }
  end,
by simp [accufact_eq_fact_mul n 1]

/- Substitution -/

namespace expressions

inductive exp : Type
| Var  : string → exp
| Num  : ℤ → exp
| Plus : exp → exp → exp

export exp

def subst (ρ : string → exp) : exp → exp
| (Var y)      := ρ y
| (Num i)      := Num i
| (Plus e₁ e₂) := Plus (subst e₁) (subst e₂)


-- TODO type-based naming
lemma subst_Var (e : exp) :
  subst (λx, Var x) e = e :=
begin
  induction' e,
  case Var {
    rename x s,
    /- Desired state here. -/
    rw [subst]
  },
  case Num {
    rename x z,
    /- Desired state here. -/
    rw [subst]
  },
  case Plus {
    rw [subst],
    rw ih_e,
    rw ih_e_1
   }
end

end expressions


/- Less-than -/

namespace less_than

inductive lt : nat → nat → Type
| zero_succ (n : nat) : lt 0 (1 + n)
| succ_succ {n m : nat} : lt n m → lt (1 + n) (1 + m)

inductive lte : nat → nat → Type
| zero (n : nat) : lte 0 n
| succ {n m : nat} : lte n m → lte (1 + n) (1 + m)

lemma lt_lte {n m} : lt n m → lte n m :=
  begin
    intro lt_n_m,
    induction' lt_n_m,
    case less_than.lt.zero_succ : i {
      constructor
    },
    case less_than.lt.succ_succ : i j lt_i_j ih {
      constructor,
      apply ih
    }
  end.

end less_than


/- Palindromes -/

namespace palindrome

inductive palindrome {α : Type} : list α → Prop
| nil : palindrome []
| single (x : α) : palindrome [x]
| sandwich (x : α) (xs : list α) (hpal : palindrome xs) :
  palindrome ([x] ++ xs ++ [x])

axiom reverse_append_sandwich {α : Type} (x : α) (ys : list α) :
  list.reverse ([x] ++ ys ++ [x]) = [x] ++ list.reverse ys ++ [x]

lemma rev_palindrome {α : Type} (xs : list α) (hpal : palindrome xs) :
  palindrome (list.reverse xs) :=
begin
  induction' hpal,
  case nil {
    exact palindrome.nil
  },
  case single {
    exact palindrome.single _
  },
  case sandwich {
    rw reverse_append_sandwich,
    apply palindrome.sandwich,
    apply ih
  }
end

end palindrome


/- Transitive Closure -/

namespace transitive_closure

inductive tc {α : Type} (r : α → α → Prop) : α → α → Prop
| base (x y : α) (hr : r x y) : tc x y
| step (x y z : α) (hr : r x y) (ht : tc y z) : tc x z

/- The transitive closure is a nice example with lots of variables to keep track
of. We start with a lemma where the variable names do not collide with those
appearing in the definition of the inductive predicate. -/

lemma tc_pets₁ {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b, tc r a b → r b c → tc r a c :=
begin
  intros a b htab hrbc,
  induction' htab fixing c,
  case base : _ _ hrab {
    exact tc.step _ _ _ hrab (tc.base _ _ hrbc)
  },
  case step : _ x _ hrax {
    exact tc.step _ _ _ hrax (ih hrbc)
  }
end

/- The same proof, but this time the variable names clash. Also, this time we
let `xinduction` generalize `z`. -/

lemma tc_pets₂ {α : Type} (r : α → α → Prop) (z : α) :
  ∀x y, tc r x y → r y z → tc r x z :=
begin
  intros x y htxy hryz,
  induction' htxy,
  case base : _ _ hrxy {
    exact tc.step _ _ _ hrxy (tc.base _ _ hryz)
  },
  case step : _ x' y hrxx' htx'y ih {
    exact tc.step _ _ _ hrxx' (ih _ hryz)
  }
end

/- Another proof along the same lines. -/

lemma tc_trans {α : Type} (r : α → α → Prop) (c : α) :
  ∀a b : α, tc r a b → tc r b c → tc r a c :=
begin
  intros a b htab htbc,
  induction' htab,
  case base {
    exact tc.step _ _ _ hr htbc
  },
  case step {
    exact tc.step _ _ _ hr (ih _ htbc)
  }
end

end transitive_closure


/- Evenness -/

inductive even : ℕ → Prop
| zero    : even 0
| add_two : ∀k : ℕ, even k → even (k + 2)

lemma not_even_2_mul_add_1 (n : ℕ) :
  ¬ even (2 * n + 1) :=
begin
  intro h,
  induction' h,
  -- TODO no case tag since there's only one goal. I don't really like this, but
  -- this is the behaviour of induction/cases.
  {
    apply ih (n - 1),
    cases n,
    case zero {
      linarith
    },
    case succ {
      simp [nat.succ_eq_add_one] at *,
      linarith
    }
  }
end


/- Big-Step Semantics -/

namespace semantics

def state :=
string → ℕ

def state.update (name : string) (val : ℕ) (s : state) : state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

inductive stmt : Type
| skip   : stmt
| assign : string → (state → ℕ) → stmt
| seq    : stmt → stmt → stmt
| ite    : (state → Prop) → stmt → stmt → stmt
| while  : (state → Prop) → stmt → stmt

export stmt

/- Our first version is partly uncurried, like in the Logical Verification
course, and also like in Concrete Semantics. This makes the binary infix
notation possible. -/

inductive big_step : stmt × state → state → Prop
| skip {s} :
  big_step (skip, s) s
| assign {x a s} :
  big_step (assign x a, s) (s{x ↦ a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (seq S T, s) u
| ite_true {b : state → Prop} {S T s t} (hcond : b s)
    (hbody : big_step (S, s) t) :
  big_step (ite b S T, s) t
| ite_false {b : state → Prop} {S T s t} (hcond : ¬ b s)
    (hbody : big_step (T, s) t) :
  big_step (ite b S T, s) t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : big_step (S, s) t)
    (hrest : big_step (while b S, t) u) :
  big_step (while b S, s) u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  big_step (while b S, s) s

infix ` ⟹ `:110 := big_step

open big_step

lemma not_big_step_while_true {S s t} :
  ¬ (while (λ_, true) S, s) ⟹ t :=
begin
  intro hw,
  induction' hw,
  case while_true {
    exact ih_hw_1
  },
  case while_false {
    apply hcond,
    trivial
  }
end

/- Desired proof script:

lemma not_big_step_while_true {S s t} :
  ¬ (while (λ_, true) S, s) ⟹ t :=
begin
  xinduction hw,
  case while_true {
    exact ih_hrest },
  case while_false {
    apply hcond,
    apply true.intro }
end -/

/- The next version is fully curried. Ideally, both versions should behave more
or less the same as far as induction is concerned. -/

inductive curried_big_step : stmt → state → state → Prop
| skip {s} :
  curried_big_step skip s s
| assign {x a s} :
  curried_big_step (assign x a) s (s{x ↦ a s})
| seq {S T s t u} (hS : curried_big_step S s t)
    (hT : curried_big_step T t u) :
  curried_big_step (seq S T) s u
| ite_true {b : state → Prop} {S T s t} (hcond : b s)
    (hbody : curried_big_step S s t) :
  curried_big_step (ite b S T) s t
| ite_false {b : state → Prop} {S T s t} (hcond : ¬ b s)
    (hbody : curried_big_step T s t) :
  curried_big_step (ite b S T) s t
| while_true {b : state → Prop} {S s t u} (hcond : b s)
    (hbody : curried_big_step S s t)
    (hrest : curried_big_step (while b S) t u) :
  curried_big_step (while b S) s u
| while_false {b : state → Prop} {S s} (hcond : ¬ b s) :
  curried_big_step (while b S) s s

lemma not_curried_big_step_while_true {S s t} :
  ¬ curried_big_step (while (λ_, true) S) s t :=
begin
  intro hw,
  induction' hw,
  case while_true {
    exact ih_hw_1,
  },
  case while_false {
    exact hcond trivial
  }
end

end semantics


/- Small-Step Semantics -/

namespace semantics

inductive small_step : stmt × state → stmt × state → Prop
| assign {x a s} :
  small_step (assign x a, s) (skip, s{x ↦ a s})
| seq_step {S S' T s s'} (hS : small_step (S, s) (S', s')) :
  small_step (seq S T, s) (seq S' T, s')
| seq_skip {T s} :
  small_step (seq skip T, s) (T, s)
| ite_true {b : state → Prop} {S T s} (hcond : b s) :
  small_step (ite b S T, s) (S, s)
| ite_false {b : state → Prop} {S T s} (hcond : ¬ b s) :
  small_step (ite b S T, s) (T, s)
| while {b : state → Prop} {S s} :
  small_step (while b S, s) (ite b (seq S (while b S)) skip, s)

/- The next example yields unprovable subgoals, where the variables `S`, `s'`,
`T`, and `T'` are not instantiated properly. The reason seems to be that
`(S, s)` and `(T, t)` are replaced en bloc, and hence `(S, s')` and `(S, t')`
are left alone. `cases` does the right thing but gives no induction
hypothesis. -/

lemma small_step_if_equal_states {S T s t s' t'}
    (hstep : small_step (S, s) (T, t)) (hs : s' = s) (ht : t' = t) :
  small_step (S, s') (T, t') :=
begin
  induction' hstep,
  { rw [hs, ht],
    exact small_step.assign,
  },
  { apply small_step.seq_step,
    exact ih hs ht,
  },
  { rw [hs, ht],
    exact small_step.seq_skip,
  },
  { rw [hs, ht],
    exact small_step.ite_true hcond,
  },
  { rw [hs, ht],
    exact small_step.ite_false hcond,
  },
  { rw [hs, ht],
    exact small_step.while,
  }
end

/- `cases` is better behaved. -/

lemma small_step_if_equal_states₂ {S T s t s' t'}
    (hstep : small_step (S, s) (T, t)) (hs : s' = s) (ht : t' = t) :
  small_step (S, s') (T, t') :=
begin
  cases hstep,
  case small_step.assign : x a {
    change t' = s{x ↦ a s} at ht,  /- Change back! -/
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.assign },
  case small_step.seq_step : S S' T s t hS {
    clear hstep,
    have ih : ∀s s' t t', s' = s → t' = t →
      small_step (S, s') (S', t') := sorry,
    /- Ideally the one-point rule shouldn't be used here. -/
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.seq_step hS },
  case small_step.seq_skip {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.seq_skip },
  case small_step.ite_true : _ _ _ _ hcond {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.ite_true hcond },
  case small_step.ite_false : _ _ _ _ hcond {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.ite_false hcond },
  case small_step.while : b S {
    clear hstep,
    /- Desired state here. -/
    rw [hs, ht],
    exact small_step.while }
end

end semantics
