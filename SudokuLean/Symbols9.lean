import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

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
  | .six   => 6
  | .seven => 7
  | .eight => 8
  | .nine  => 9

instance : Fintype Symbols9 where
  elems := {Symbols9.one, .two, .three, .four, .five, .six, .seven, .eight, .nine}
  complete x := by cases x <;> simp


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
@[simp] theorem Symbols9_five_eq_5  : Symbols9.five  = (5 : Symbols9) := rfl
@[simp] theorem Symbols9_six_eq_6   : Symbols9.six   = (6 : Symbols9) := rfl
@[simp] theorem Symbols9_seven_eq_7 : Symbols9.seven = (7 : Symbols9) := rfl
@[simp] theorem Symbols9_eight_eq_8 : Symbols9.eight = (8 : Symbols9) := rfl
@[simp] theorem Symbols9_nine_eq_9  : Symbols9.nine  = (9 : Symbols9) := rfl


instance : HAdd Symbols9 Symbols9 Nat where
  hAdd a b := a.toNat + b.toNat

instance : HAdd Symbols9 Nat Nat where
  hAdd a n := a.toNat + n
