import data.fintype.basic
import data.num.lemmas

structure encoding (α : Type*) :=
(Γ : Type)
(encode : α → list Γ)
(encode_injective : function.injective encode)

@[derive [decidable_eq]]
inductive Γ₀₁ | bit0 | bit1

@[derive [decidable_eq]]
inductive Γ' | blank | bit0 | bit1 | bra | ket | comma

instance inhabited_Γ' : inhabited Γ' := ⟨Γ'.blank⟩

def encode_pos_num : pos_num → list Γ'
| pos_num.one := [Γ'.bit1]
| (pos_num.bit0 n) := Γ'.bit0 :: encode_pos_num n
| (pos_num.bit1 n) := Γ'.bit1 :: encode_pos_num n

def encode_num : num → list Γ'
| num.zero := []
| (num.pos n) := encode_pos_num n

def encode_nat (n : ℕ) : list Γ' := encode_num n

def decode_pos_num : list Γ' → pos_num
| [Γ'.bit1] := pos_num.one
| (Γ'.bit0 :: l) := (pos_num.bit0 (decode_pos_num l))
| (Γ'.bit1 :: l) := (pos_num.bit1 (decode_pos_num l))
| _ := pos_num.one

def decode_num : list Γ' → num
| [] := num.zero
| l := decode_pos_num l

namespace num
def to_nat : num → ℕ
| zero := sorry
| _ := sorry
end num

def decode_nat : list Γ' → nat := num.to_nat ∘ decode_num

def encodek_nat : ∀ n, (decode_nat(encode_nat n) ) = n := sorry

-- def tr_pos_num_nonempty (n : pos_num) : (tr_pos_num n) ≠ [] :=
-- begin
--   cases n with m,
--   exact list.cons_ne_nil Γ'.bit1 list.nil,
--   exact list.cons_ne_nil Γ'.bit1 (tr_pos_num m),
--   exact list.cons_ne_nil Γ'.bit0 (tr_pos_num n),
-- end

-- @[simp] theorem tr_nat_zero : tr_nat 0 = [] := rfl

-- #check tr_pos_num_nonempty

-- def tr_pos_num_injective : function.injective tr_pos_num :=
-- begin
--   intros x y h,

-- end

-- def tr_num_injective : function.injective tr_num :=
-- begin
--   intros x y h,
--   cases x with a ha; cases y with b hb; simp,
--   change [] = tr_num (num.pos b) at h,
--   exact tr_pos_num_nonempty b h.symm,
--   exact tr_pos_num_nonempty a h,
--   exact tr_pos_num_injective h,
-- end

-- def tr_nat_injective : function.injective tr_nat :=
-- begin
--   intros x y h,
--   change tr_num x = tr_num y at h,
--   have h' := tr_num_injective h,
--   exact num.of_nat_inj.mp h',
-- end

def encoding_nat : encoding ℕ :=
{ Γ := Γ',
  encode := encode_nat,
  encode_injective := function.left_inverse.injective encodek_nat}
