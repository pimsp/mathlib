import data.fintype.basic
import data.num.lemmas
import tactic

namespace encoding
structure encoding (α : Type) :=
(Γ : Type)
(encode : α → list Γ)
(decode : list Γ → option α)
(encodek : decode ∘ encode = option.some)

structure fin_encoding (α : Type) extends encoding α :=
(Γ_fin : fintype Γ)
--(encode_injective : function.injective encode)

#check fin_encoding

@[derive [inhabited,decidable_eq]]
inductive Γ₀₁ | bit0 | bit1

#check list.mem

def Γ₀₁_fin : fintype Γ₀₁ :=
{ elems := {Γ₀₁.bit0, Γ₀₁.bit1},
  complete := λ x, begin cases x, left,trivial,right,left,trivial, end }

@[derive [decidable_eq]]
inductive Γ' | blank | bit0 | bit1 | bra | ket | comma

def Γ'_fin : fintype Γ' :=
{ elems := {Γ'.blank, Γ'.bit0, Γ'.bit1, Γ'.bra, Γ'.ket, Γ'.comma},
  complete := λ x, begin cases x, left,trivial,right,left,trivial,right,right,left,trivial,right,right,right,left,trivial,right,right,right,right,left,trivial,right,right,right,right,right,left,trivial end }

def inclusion_Γ₀₁_Γ' : Γ₀₁ → Γ'
| Γ₀₁.bit0 := Γ'.bit0
| Γ₀₁.bit1 := Γ'.bit1

def section_Γ'_Γ₀₁ : Γ' → Γ₀₁
| Γ'.bit0 := Γ₀₁.bit0
| Γ'.bit1 := Γ₀₁.bit1
| _ := arbitrary Γ₀₁

lemma left_inverse_section_inclusion : function.left_inverse section_Γ'_Γ₀₁ inclusion_Γ₀₁_Γ' := begin intros x, cases x; trivial, end

def inclusion_Γ₀₁_Γ'_injective : function.injective inclusion_Γ₀₁_Γ' :=
begin tidy, cases a₁; cases a₂; simp; finish end

instance inhabited_Γ' : inhabited Γ' := ⟨Γ'.blank⟩

def encode_pos_num : pos_num → list Γ₀₁
| pos_num.one := [Γ₀₁.bit1]
| (pos_num.bit0 n) := Γ₀₁.bit0 :: encode_pos_num n
| (pos_num.bit1 n) := Γ₀₁.bit1 :: encode_pos_num n

def encode_num : num → list Γ₀₁
| num.zero := []
| (num.pos n) := encode_pos_num n

def encode_nat (n : ℕ) : list Γ₀₁ := encode_num n

def decode_pos_num : list Γ₀₁ → pos_num
| [Γ₀₁.bit1] := pos_num.one
| (Γ₀₁.bit0 :: l) := (pos_num.bit0 (decode_pos_num l))
| (Γ₀₁.bit1 :: l) := (pos_num.bit1 (decode_pos_num l))
| _ := pos_num.one

def decode_num : list Γ₀₁ → num
| [] := num.zero
| l := decode_pos_num l

namespace encodable
instance encodable_num : encodable num :=
{ encode := λ n, n,
  decode := λ n, some n,
  encodek := begin
    intros a,
    simp,
  end}
end encodable

def decode_nat : list Γ₀₁ → nat := λ l, encodable.encode(decode_num(l))

def encode_pos_num_nonempty (n : pos_num) : (encode_pos_num n) ≠ [] :=
begin
  cases n with m,
  exact list.cons_ne_nil Γ₀₁.bit1 list.nil,
  exact list.cons_ne_nil Γ₀₁.bit1 (encode_pos_num m),
  exact list.cons_ne_nil Γ₀₁.bit0 (encode_pos_num n),
end


def encodek_pos_num : ∀ n, (decode_pos_num(encode_pos_num n) ) = n := begin
  intros n,
  induction n with m hm m hm,
  trivial,
  change decode_pos_num ((Γ₀₁.bit1) :: encode_pos_num m) = m.bit1,
  have h := encode_pos_num_nonempty m,
  calc decode_pos_num (Γ₀₁.bit1 :: encode_pos_num m)
    = pos_num.bit1 (decode_pos_num (encode_pos_num m)) : begin cases (encode_pos_num m), exfalso, trivial,trivial, end
    ... = m.bit1 : by rw hm,
  calc decode_pos_num (Γ₀₁.bit0 :: encode_pos_num m)
    = pos_num.bit0 (decode_pos_num (encode_pos_num m)) :  by trivial
    ... = m.bit0 : by rw hm,
end

def encodek_num : ∀ n, (decode_num(encode_num n) ) = n := begin
  intros n,
  cases n,
  trivial,
  change decode_num (encode_pos_num n) = num.pos n,
  have h : encode_pos_num n ≠ [] := encode_pos_num_nonempty n,
  have h' : decode_num (encode_pos_num n) = decode_pos_num (encode_pos_num n) := begin
    cases encode_pos_num n; trivial,
  end,
  rw h',
  rw (encodek_pos_num n),
  simp only [pos_num.cast_to_num],
end

def encodek_nat : ∀ n, (decode_nat(encode_nat n) ) = n := begin
  intros n,
  change decode_nat (encode_num n) = n,
  have h :decode_num (encode_num n) = n :=
  begin
    change decode_num (encode_num n) = n,
    exact encodek_num ↑n,
  end,
  have h' : encodable.encode (decode_num (encode_num n)) = encodable.encode n :=
  begin
    rw h,
    simp,
    change (λ n, n : num → ℕ) ↑n = n,
    simp,
  end,
  exact h',
end

def encoding_nat_Γ₀₁ : encoding ℕ :=
{ Γ := Γ₀₁,
  encode := encode_nat,
  decode := λ n, option.some (decode_nat n),
  encodek := begin funext, simp, exact encodek_nat x end
  }

def fin_encoding_nat_Γ₀₁ : fin_encoding ℕ :=
{ Γ_fin := Γ₀₁_fin,
..encoding_nat_Γ₀₁
  }

def encoding_nat_Γ' : encoding ℕ :=
{ Γ := Γ',
  encode := (list.map inclusion_Γ₀₁_Γ') ∘ encode_nat,
  decode :=  option.some ∘ decode_nat ∘ (list.map section_Γ'_Γ₀₁),
  encodek := begin
    funext,
    simp,
     have h : section_Γ'_Γ₀₁ ∘ inclusion_Γ₀₁_Γ' = id := begin funext, simp, exact left_inverse_section_inclusion x end,
    simp [h],
    exact encodek_nat x,
  end}

def fin_encoding_nat_Γ' : fin_encoding ℕ :=
{ Γ_fin := Γ'_fin,
..encoding_nat_Γ'
  }

def encode_bool : bool → list Γ₀₁
| ff := [Γ₀₁.bit0]
| tt := [Γ₀₁.bit1]

def decode_bool : list Γ₀₁ → bool
| [Γ₀₁.bit0] := ff
| [Γ₀₁.bit1] := tt
| _ := arbitrary bool

def encodek_bool : ∀ b, (decode_bool(encode_bool b) ) = b := λ b,
begin
  cases b; refl
end

def encoding_bool_Γ₀₁ : fin_encoding bool :=
{ Γ := Γ₀₁,
  encode := encode_bool,
  decode := option.some ∘ decode_bool,
  encodek := begin funext, simp [encodek_bool x], end,
  Γ_fin := Γ₀₁_fin }

end encoding
