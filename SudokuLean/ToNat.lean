import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Basic

class ToNat (α : Type) [HAdd α Nat Nat] [LinearOrder α] where
  toNat : α → Nat
  toNat_injective : ∀ {a b : α}, toNat a = toNat b → a = b
  toNat_le_iff : ∀ {a b : α}, a ≤ b ↔ toNat a ≤ toNat b
  toNat_add : ∀ (a : α) (n : Nat), a + n = toNat a + n

attribute [instance] ToNat.toNat
export ToNat (toNat)

lemma ToNat.toNat_lt_iff {α} [HAdd α Nat Nat] [LinearOrder α] [ToNat α] {a b : α} :
  a < b ↔ toNat a < toNat b := by
  rw [lt_iff_le_and_ne, Nat.lt_iff_le_and_ne,ToNat.toNat_le_iff]
  refine and_congr_right ?_ -- (λ _ => ToNat.toNat_injective.ne_iff)
  intro _
  apply Iff.intro
  · exact mt ToNat.toNat_injective
  · exact mt (congrArg toNat)
  -- rw [lt_iff_le_not_ne, Nat.lt_iff_le_not_ne, ToNat.toNat_le_iff, ToNat.toNat_le_iff]
