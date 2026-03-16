import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import SudokuProverLogic.ToNat

set_option linter.style.whitespace false


inductive Symbols9
| one
| two
| three
| four
| five
| six
| seven
| eight
| nine
deriving Repr, BEq, DecidableEq

def Symbols9.toNat : Symbols9 → Nat
  | .one   => 1
  | .two   => 2
  | .three => 3
  | .four  => 4
  | .five  => 5
  | .six  => 6
  | .seven  => 7
  | .eight  => 8
  | .nine  => 9

instance : LT Symbols9 where
  lt a b := a.toNat < b.toNat

instance : LE Symbols9 where
  le a b := a.toNat ≤ b.toNat

instance (a b : Symbols9) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

instance (a b : Symbols9) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance: LinearOrder Symbols9 where
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

instance : BoundedOrder Symbols9 where
  top := .nine
  le_top x := by cases x <;> decide
  bot := .one
  bot_le x := by cases x <;> decide


instance : HAdd Symbols9 Nat Nat where
  hAdd a n := a.toNat + n

instance: ToNat Symbols9 where
  toNat := Symbols9.toNat
  toNat_injective := by intro a b h; cases a <;> cases b <;> first | rfl | contradiction
  toNat_le_iff := by
    intro a b
    apply Iff.intro <;> intro h
    · cases a <;> cases b <;> first | decide | contradiction
    · cases a <;> cases b <;> first | decide | contradiction
  toNat_add := by intro a x; rfl



instance : Fintype Symbols9 where
  elems := {Symbols9.one, .two, .three, .four, .five, .six, .seven, .eight, .nine}
  complete x := by cases x <;> simp

@[simp]
lemma card_Symbols9: Fintype.card Symbols9 = 9 := by
  simp [Fintype.card, Finset.univ, Fintype.elems]


instance : OfNat Symbols9 1 where ofNat := Symbols9.one
instance : OfNat Symbols9 2 where ofNat := Symbols9.two
instance : OfNat Symbols9 3 where ofNat := Symbols9.three
instance : OfNat Symbols9 4 where ofNat := Symbols9.four
instance : OfNat Symbols9 5 where ofNat := Symbols9.five
instance : OfNat Symbols9 6 where ofNat := Symbols9.six
instance : OfNat Symbols9 7 where ofNat := Symbols9.seven
instance : OfNat Symbols9 8 where ofNat := Symbols9.eight
instance : OfNat Symbols9 9 where ofNat := Symbols9.nine



@[simp] theorem Symbols9_one_eq_1   : Symbols9.one   = (1 : Symbols9) := rfl
@[simp] theorem Symbols9_two_eq_2   : Symbols9.two   = (2 : Symbols9) := rfl
@[simp] theorem Symbols9_three_eq_3 : Symbols9.three = (3 : Symbols9) := rfl
@[simp] theorem Symbols9_four_eq_4  : Symbols9.four  = (4 : Symbols9) := rfl
@[simp] theorem Symbols9_four_eq_5  : Symbols9.five  = (5 : Symbols9) := rfl
@[simp] theorem Symbols9_four_eq_6  : Symbols9.six   = (6 : Symbols9) := rfl
@[simp] theorem Symbols9_four_eq_7  : Symbols9.seven = (7 : Symbols9) := rfl
@[simp] theorem Symbols9_four_eq_8  : Symbols9.eight = (8 : Symbols9) := rfl
@[simp] theorem Symbols9_four_eq_9  : Symbols9.nine  = (9 : Symbols9) := rfl



instance : HAdd Symbols9 Symbols9 Nat where
  hAdd a b := a.toNat + b.toNat
