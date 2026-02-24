import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import SudokuLean.ToNat

set_option linter.style.whitespace false


inductive Symbols4
| one
| two
| three
| four
deriving Repr, BEq, DecidableEq

def Symbols4.toNat : Symbols4 → Nat
  | .one   => 1
  | .two   => 2
  | .three => 3
  | .four  => 4

instance : LT Symbols4 where
  lt a b := a.toNat < b.toNat

instance : LE Symbols4 where
  le a b := a.toNat ≤ b.toNat

instance (a b : Symbols4) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

instance (a b : Symbols4) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance: LinearOrder Symbols4 where
  le_refl a := Nat.le_refl _
  le_trans a b c := Nat.le_trans
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_antisymm a b h1 h2 := by
    have: a.toNat = b.toNat := Nat.le_antisymm h1 h2
    cases a <;> cases b <;> injection this <;> (try contradiction) <;> rfl
  le_total a b := Nat.le_total a.toNat b.toNat
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance

instance : BoundedOrder Symbols4 where
  top := .four
  le_top x := by cases x <;> decide
  bot := .one
  bot_le x := by cases x <;> decide


instance : HAdd Symbols4 Nat Nat where
  hAdd a n := a.toNat + n

instance: ToNat Symbols4 where
  toNat := Symbols4.toNat
  toNat_injective := by intro a b h; cases a <;> cases b <;> first | rfl | contradiction
  toNat_le_iff := by
    intro a b
    apply Iff.intro <;> intro h
    · cases a <;> cases b <;> first | decide | contradiction
    · cases a <;> cases b <;> first | decide | contradiction
  toNat_add := by intro a x; rfl



instance : Fintype Symbols4 where
  elems := {Symbols4.one, .two, .three, .four}
  complete x := by cases x <;> simp

@[simp]
lemma card_Symbols4: Fintype.card Symbols4 = 4 := by
  simp [Fintype.card, Finset.univ, Fintype.elems]


instance : OfNat Symbols4 1 where ofNat := Symbols4.one
instance : OfNat Symbols4 2 where ofNat := Symbols4.two
instance : OfNat Symbols4 3 where ofNat := Symbols4.three
instance : OfNat Symbols4 4 where ofNat := Symbols4.four



@[simp] theorem symbols4_one_eq_1   : Symbols4.one   = (1 : Symbols4) := rfl
@[simp] theorem symbols4_two_eq_2   : Symbols4.two   = (2 : Symbols4) := rfl
@[simp] theorem symbols4_three_eq_3 : Symbols4.three = (3 : Symbols4) := rfl
@[simp] theorem symbols4_four_eq_4  : Symbols4.four  = (4 : Symbols4) := rfl



instance : HAdd Symbols4 Symbols4 Nat where
  hAdd a b := a.toNat + b.toNat
