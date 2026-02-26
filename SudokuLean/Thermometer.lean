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
structure Thermometer {α} [LT α] (f: Nat -> α) (l: List Nat) where
  len: l.length ≥ 1 := by decide -- no reason to have a 1 cell thermo, but whatever
  property: List.IsChain (· < ·) (List.map f l)

-- a version of isChain_getElem with the included map to make it easier to apply to this case
lemma Thermometer.iff_getElem {α} [LT α] {f: Nat -> α} {l: List Nat} (thermo: Thermometer f l): ∀ k (klen: k+1 < l.length), f l[k] < f l[k + 1] := by
  replace thermo := thermo.property
  rw [List.isChain_map, List.isChain_iff_getElem] at thermo
  apply thermo



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
  apply h.property

lemma thermo_distance {α} [LinearOrder α] [HAdd α Nat Nat] [ToNat α]
  {f: Nat -> α} {l: List Nat} (thermo: Thermometer f l)
  (i j : Nat) (hi : i < l.length) (hj : j < l.length) (h_le : i ≤ j) :
  toNat (f l[i]) + (j - i) ≤ toNat (f l[j]) := by
  induction j, h_le using Nat.le_induction with
  | base => simp
  | succ k h_ik ih =>
    have h_lt : toNat (f l[k]) < toNat (f l[k+1]) := by
      apply ToNat.toNat_lt_iff.mp
      apply Thermometer.iff_getElem thermo
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
  ∀ (i) (h1: i < l.length), f l[i] = ⊥ -> i = 0 := by
  intro i h1 h2
  match i with
  | 0 => rfl
  | k+1 =>
    exfalso
    absurd (h2 ▸ thermo.iff_getElem k h1)
    simp

-- helper lemma
lemma top_last {α} [Preorder α] [OrderTop α] {f: Nat -> α} {l : List Nat} (thermo : Thermometer f l):
  ∀ (i) (h1: i < l.length), f l[i] = ⊤ -> i = l.length - 1 := by
  intro i h1 h2
  by_contra! h_not_last
  have hi_plus_one : i + 1 < l.length := by omega
  have h_lt : f l[i] < f l[i+1] := by apply thermo.iff_getElem
  rw [h2] at h_lt
  simp at h_lt


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
  simp only [Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, imp_false, not_not]
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
  simp only [Classical.not_imp]
  constructor
  · rw [h1, target_val]
  · exact Nat.ne_of_lt h2

theorem top_not_gt {α} [Preorder α] [OrderTop α] {f: Nat -> α} {target: Nat} {x: α} (h1: f target = ⊤) (h2: f target < x): False := by
  exact not_top_lt (h1 ▸ h2)


-- a sublist of thermometer is still a thermometer
-- Sublist is more general, not contiguous. I suspect that it will be harder to use
theorem sub_noncont_thermo {α} [LT α] [Trans (α := α) (· < ·) (· < ·) (· < ·)] {f: Nat -> α} {l: List Nat} {l': List Nat} (h1: Thermometer f l) (h2: List.Sublist l' l) (len': l'.length ≥ 1 := by decide): Thermometer f l' := by
  constructor
  · assumption
  refine List.IsChain.sublist h1.property (List.Sublist.map f h2)

-- Contiguous sublist infix. This is probably easier to use.
theorem sub_cont_thermo {α} [LT α] {f: Nat -> α} {l: List Nat} {l': List Nat} (h1: Thermometer f l) (h2: l' <:+: l) (len': l'.length ≥ 1 := by decide): Thermometer f l' := by
  constructor
  · assumption
  refine List.IsChain.infix h1.property (List.IsInfix.map f h2)

-- set_option trace.Meta.synthInstance true

-- on a thermo, if f l.0 has a minimum, for a given x, min+x <= f l.x
theorem thermometer_mins {α} [HAdd α Nat Nat] [LinearOrder α] [ToNat α]
  {f: Nat -> α} {l: List Nat} {min: α} (thermo: Thermometer f l)
  (h0: min ≤ f (l.get ⟨0, (by exact Nat.lt_of_succ_le thermo.len)⟩)):
  ∀ x (h4: x < l.length := by decide), toNat min + x ≤ toNat (f l[x]) := by
  intro x xl
  simp only [List.get_eq_getElem, ToNat.toNat_le_iff] at h0
  let h_dist := thermo_distance thermo 0 x (by exact Nat.lt_of_succ_le thermo.len) xl (by simp only [Nat.zero_le])
  simp at h_dist
  omega


theorem thermometer_maxs {α} [HAdd α Nat Nat] [LinearOrder α] [ToNat α]
  {f: Nat -> α} {l: List Nat} {max: α} (thermo: Thermometer f l)
  (h0: f (l.get ⟨l.length-1, (by exact Nat.sub_lt thermo.len (by decide))⟩) ≤ max):
  ∀ x (h4: x < l.length := by decide), toNat (f l[x])+(l.length - 1 - x) ≤ toNat max := by
  intro x xl
  simp only [List.get_eq_getElem, ToNat.toNat_le_iff] at h0
  let h_dist := thermo_distance thermo x (l.length-1) xl (by exact Nat.sub_lt thermo.len (by decide))
  simp at h_dist
  omega


-- if the cell is le at ge to value than it is value by antisymm
theorem fill_by_min_max {α} [PartialOrder α] {f: Nat -> α}
  {value: α} {cell: Nat} (h0: value ≤ f cell) (h1: f cell ≤ value): f cell = value := le_antisymm h1 h0


-- For a thermometer (maybe a subthermo)
-- If the difference between min of the min cell and max of the max cell is 'equal' to the length of the thermo, fill in the thermo
-- example thermo [c0, c1, c2]  2 <= c0  c2 <= 4  ->  c0 = 2  c1 = 3  c2 = 4
theorem fill_thermo {α} [LinearOrder α] [HAdd α Nat Nat] [ToNat α] [Trans (α := α) (· ≤ ·) (· ≤ ·) (· ≤ ·)] {f: Nat -> α} {l: List Nat}
  (thermo: Thermometer f l)
  {min max: α}
  (h0: min ≤ f (l.get ⟨0, (by exact Nat.lt_of_succ_le thermo.len)⟩))
  (h1: f (l.get ⟨l.length-1, (by exact Nat.sub_lt thermo.len (by decide))⟩) ≤ max)
  (h2: l.length = toNat max - toNat min + (1: Nat) := by decide):
  ∀ x (h4: x < l.length), toNat (f l[x]) = min + x := by
    simp only [List.get_eq_getElem] at *
    intro x xl
    rw [ToNat.toNat_add]
    -- we are going to sandwhich this thing hard
    -- mins says min + x ≤ f l x
    let mins := thermometer_mins thermo h0 x xl
    -- maxs says f l x + (length - x - 1) ≤ max
    let maxs := thermometer_maxs thermo h1 x xl
    -- in order to use antisymm, we want maxs to look like, omega can handle it!
    replace maxs: toNat (f l[x]) ≤ toNat min + x := by omega
    exact le_antisymm maxs mins


-- def Lazy_Thermometer {α} [LE α] (f: Nat -> α) (l: List Nat): Prop := List.IsChain (· ≤ ·) (List.map f l)
-- if two cells are in the same region on this thermo, they must be different, and so less than, might not be a useful theorem, but still might prove it
