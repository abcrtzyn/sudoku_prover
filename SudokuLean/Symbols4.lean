import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

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

instance : HAdd Symbols4 Nat Nat where
  hAdd a n := a.toNat + n
