import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.Notation
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.List.Chain
import Mathlib.Algebra.Group.Defs
import SudokuLean.ToNat

set_option linter.style.longLine false
set_option linter.style.whitespace false

-- This file is dedicated to themometers and other comparison constraints.

-- A thermometer is a line where every cell on the line is greater than the previous
-- Basicially a sequence of less than constroints
-- This definition does not care which cells are included in the therometer
-- (they don't have to be adjacent)

-- lower on the list -> lower digit
def Thermometer {α} [LT α] (f: Nat -> α) (l: List Nat) : Prop := List.IsChain (· < ·) (List.map f l)




-- A puzzle constraint might look like
-- Thermometer solution [21,11,1,2]
-- bulb is at 21, goes up to cell 2

-- for a puzzle where less than is a constraint and there are multiple chained together,
-- I would like to be able to convert it to a thermo



-- theorems for lt and thermos




-- any two elements on the thermo are related
theorem thermo_pairwise {α} [LT α] [IsTrans α (· < ·)] (f: Nat -> α) (l: List Nat):
  Thermometer f l -> List.Pairwise (· < ·) (List.map f l) := by
  intro h
  apply List.isChain_iff_pairwise.mp
  apply h

lemma thermo_distance {α} [LinearOrder α] [HAdd α Nat Nat] [ToNat α]
  {f: Nat -> α} {l: List Nat} (thermo: Thermometer f l)
  (i j : Nat) (hi : i < l.length) (hj : j < l.length) (h_le : i ≤ j) :
  f l[i] + (j - i) ≤ toNat (f l[j]) := by
  simp only [ToNat.toNat_add]
  induction j, h_le using Nat.le_induction with
  | base => simp
  | succ k h_ik ih =>
    have h_lt : toNat (f l[k]) < toNat (f l[k+1]) := by
      apply ToNat.toNat_lt_iff.mp
      unfold Thermometer at thermo
      rw [List.isChain_map, List.isChain_iff_getElem] at thermo
      apply thermo k hj
    have ih_k : toNat (f l[i]) + (k - i) ≤ toNat (f l[k]) := by
      apply ih
      -- ih (Nat.lt_of_succ_le hj)

    -- 3. Combine: (min + dist_k) + 1 ≤ f[k] + 1 ≤ f[k+1]
    calc
      toNat (f l[i]) + (k + 1 - i)
        = toNat (f l[i]) + (k - i) + 1 := by rw [Nat.add_assoc, Nat.sub_add_comm h_ik]
      _ ≤ toNat (f l[k]) + 1           := Nat.add_le_add_right ih_k 1
      _ ≤ toNat (f l[k+1])             := Nat.succ_le_of_lt h_lt


-- helper lemma
lemma bottom_first {α} [Preorder α] [OrderBot α] {f: Nat -> α} {l : List Nat} (thermo : Thermometer f l):
  ∀ (i) (h1: i < l.length), (List.map f l)[i]'(by rw [<- List.length_map f] at h1; assumption) = ⊥ -> i = 0 := by
  intro i h1 h2
  rw [<- List.length_map f] at h1
  match i with
  | 0 => rfl
  | k+1 =>
    exfalso
    have h3: (List.map f l)[k] < (List.map f l)[k + 1] := by
      apply List.isChain_iff_getElem.mp
      apply thermo
    rw [h2] at h3
    simp only [List.getElem_map, not_lt_bot] at h3

-- helper lemma
lemma top_last {α} [Preorder α] [OrderTop α] {f: Nat -> α} {l : List Nat} (thermo : Thermometer f l):
  ∀ (i) (h1: i < l.length), (List.map f l)[i]'(by rw [<- List.length_map f] at h1; assumption) = ⊤ -> i = l.length - 1 := by
  intro i h1 h2
  by_contra! h_not_last
  have hi_plus_one : i + 1 < l.length := by
    -- 'omega' is the best tactic for this Nat logic
    omega
  rw [<- List.length_map f] at h1
  rw [<- List.length_map f] at hi_plus_one
  have h_lt : (List.map f l)[i] < (List.map f l)[i+1] := by
    apply List.isChain_iff_getElem.mp
    apply thermo
  rw [h2] at h_lt
  simp only [List.getElem_map, not_top_lt] at h_lt


-- this states that 1 can not be anywhere on the thermo besides the head of the list
theorem bottom_is_only_first {α} [Preorder α] [OrderBot α] {f: Nat -> α} {l : List Nat} {target: Nat} (target_val: f target = ⊥) (thermo : Thermometer f l)
  (h1: target ∈ l.tail := by decide): False := by
  -- we need an index to target
  apply List.get_of_mem at h1
  cases h1 with | intro n h1
  cases n with | mk n h2
  simp only [List.get_eq_getElem, List.getElem_tail] at h1
  simp only [List.length_tail] at h2
  let bot_first := bottom_first thermo (n+1) (Nat.add_lt_of_lt_sub h2)
  absurd bot_first
  simp only [List.getElem_map, Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, imp_false, not_not]
  rw [h1, target_val]

theorem bottom_not_lt {α} [Preorder α] [OrderBot α] {f: Nat -> α} {target: Nat} {x: α} (h1: f target = ⊥) (h2: x < f target): False := by
  exact not_lt_bot (h1 ▸ h2)


theorem top_is_only_last {α} [Preorder α] [OrderTop α] {f: Nat -> α} {l : List Nat} {target: Nat} (target_val: f target = ⊤) (thermo : Thermometer f l)
  (h1: target ∈ l.dropLast := by decide): False := by
  apply List.get_of_mem at h1
  cases h1 with | intro n h1
  cases n with | mk n h2
  simp only [List.get_eq_getElem, List.getElem_dropLast] at h1
  simp only [List.length_dropLast] at h2
  let top_last := top_last thermo n (Nat.lt_of_lt_pred h2)
  absurd top_last
  simp only [List.getElem_map, Classical.not_imp]
  constructor
  · rw [h1, target_val]
  · exact Nat.ne_of_lt h2

theorem top_not_gt {α} [Preorder α] [OrderTop α] {f: Nat -> α} {target: Nat} {x: α} (h1: f target = ⊤) (h2: f target < x): False := by
  exact not_top_lt (h1 ▸ h2)


-- a sublist of thermometer is still a thermometer
-- Sublist is more general, not contiguous. I suspect that it will be harder to use
theorem sub_noncont_thermo {α} [LT α] [Trans (α := α) (· < ·) (· < ·) (· < ·)] {f: Nat -> α} {l: List Nat} {l': List Nat} (h1: Thermometer f l) (h2: List.Sublist l' l): Thermometer f l' := by
  unfold Thermometer at *
  refine List.IsChain.sublist h1 (List.Sublist.map f h2)

-- Contiguous sublist infix. This is probably easier to use.
theorem sub_cont_thermo {α} [LT α] {f: Nat -> α} {l: List Nat} {l': List Nat} (h1: Thermometer f l) (h2: l' <:+: l): Thermometer f l' := by
  unfold Thermometer at *
  refine List.IsChain.infix h1 (List.IsInfix.map f h2)

-- For a thermometer (maybe a subthermo)
-- If the difference between min of the min cell and max of the max cell is 'equal' to the length of the thermo, fill in the thermo
-- example thermo [c0, c1, c2]  2 <= c0  c2 <= 4  ->  c0 = 2  c1 = 3  c2 = 4


theorem fill_by_min_max {α} [PartialOrder α] {f: Nat -> α}
  {value: α} {cell: Nat} (h0: value ≤ f cell) (h1: f cell ≤ value): f cell = value := le_antisymm h1 h0

-- this theorem can't fill the whole thermo, but we can do the head, and return hypotheses for the next time
-- its like induction
theorem fill_thermo {α} [LinearOrder α] [HAdd α Nat Nat] [ToNat α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] {f: Nat -> α} {l: List Nat}
  (thermo: Thermometer f l)
  (h3: l.length >= 1 := by decide) {min max: α}
  (h0: min ≤ f (l.head (List.ne_nil_of_length_pos (Nat.lt_of_succ_le h3))))
  (h1: f (l.getLast (List.ne_nil_of_length_pos (Nat.lt_of_succ_le h3))) ≤ max)
  (h2: l.length = toNat max - toNat min + (1: Nat) := by decide):
  ∀ x (h4: x < l.length), toNat (f l[x]) = min + x := by
    -- intro x xl
    have mins: ∀ x (h4: x < l.length), min+x ≤ toNat (f l[x]) := by
      intro x xl
      rw [ToNat.toNat_add]
      induction x with
      | zero =>
        rw [List.head_eq_getElem] at h0
        apply ToNat.toNat_le_iff.mp
        apply h0
      | succ x xih =>
        unfold Thermometer at thermo
        rw [List.isChain_map] at thermo
        rw [List.isChain_iff_getElem] at thermo
        specialize thermo x xl
        specialize xih (Nat.lt_of_succ_lt xl)
        rw [ToNat.toNat_lt_iff] at thermo
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt xih thermo)
    intro x xl
    let h_dist := thermo_distance thermo x (l.length-1) xl (Nat.sub_lt h3 (by decide)) (Nat.le_sub_one_of_lt xl)
    conv at h_dist =>
      enter [1, 2, 1, 1]
      rw [h2]
    simp only [Nat.add_one_sub_one] at h_dist
    rw [← List.getElem_length_sub_one_eq_getLast (l := l) (Nat.sub_lt (Nat.lt_of_succ_le h3) Nat.zero_lt_one)] at h1
    rw [ToNat.toNat_le_iff] at h1
    have this: f l[x] + (toNat max - toNat min - x) ≤ toNat max := le_trans h_dist h1
    have h_upper : toNat (f l[x]) ≤ min + x := by
      have xl2: x < toNat max - toNat min + 1 := (h2 ▸ xl)
      rw [ToNat.toNat_add] at this
      conv =>
        enter [2]
        apply ToNat.toNat_add
      apply Nat.le_of_add_le_add_right (b := toNat max - toNat min - x)
      refine le_trans this ?_
      clear this h_dist
      omega
    exact le_antisymm h_upper (mins x xl)








-- def Lazy_Thermometer {α} [LE α] (f: Nat -> α) (l: List Nat): Prop := List.IsChain (· ≤ ·) (List.map f l)
-- if two cells are in the same region on this thermo, they must be different, and so less than, might not be a useful theorem, but still might prove it
