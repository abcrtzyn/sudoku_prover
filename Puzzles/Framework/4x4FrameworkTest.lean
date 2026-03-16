import SudokuProverLogic.Basic
import SudokuProverLogic.Symbols4
import SudokuProverLogic.Tactics
import Mathlib.Tactic.IntervalCases


set_option linter.style.whitespace false



structure TestPuzzle (solution: Nat -> Symbols4) where
  row1: UniqueSet solution { 0, 1, 2, 3}
  row2: UniqueSet solution { 4, 5, 6, 7}
  row3: UniqueSet solution { 8, 9,10,11}
  row4: UniqueSet solution {12,13,14,15}
  col1: UniqueSet solution { 0, 4, 8,12}
  col2: UniqueSet solution { 1, 5, 9,13}
  col3: UniqueSet solution { 2, 6,10,14}
  col4: UniqueSet solution { 3, 7,11,15}
  box1: UniqueSet solution { 0, 1, 4, 5}
  box2: UniqueSet solution { 2, 3, 6, 7}
  box3: UniqueSet solution { 8, 9,12,13}
  box4: UniqueSet solution {10,11,14,15}
  given2: solution 2 = 4
  given4: solution 4 = 4
  given6: solution 6 = 3
  given9: solution 9 = 4
  given11: solution 11 = 3
  given13: solution 13 = 1
  outside_grid: ∀ x, x ≥ 16 -> solution x = Symbols4.one -- just need something to call default

-- 1 3 4 2
-- 4 2 3 1
-- 2 4 1 3
-- 3 1 2 4


theorem SolveTestPuzzle {S : Set (Nat → Symbols4)} (H : ∀ f, f ∈ S ↔ TestPuzzle f):
  ∃! (g: Nat -> Symbols4), g ∈ S := by
  have k : IsSound S [] := by intro c d h; cases h
  -- here we go
  replace k := add_fact k 5 2 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 5 with
    | two => rfl
    | one => exfalso; exact digit_in_region h H.col2 H.given13
    | three => exfalso; exact digit_in_region h H.row2 H.given6
    | four => exfalso; exact digit_in_region h H.box1 H.given4
  )
  replace k := add_fact k 1 3 (by
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.col2)
    locked_support_cases h 3
    · assumption
    · exfalso; exact digit_in_cell h ((get_d k 5 2) f hf)
    · exfalso; exact digit_in_cell h H.given9
    · exfalso; exact digit_in_cell h H.given13
  )
  replace k := add_fact k 0 1 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 0 with
    | one => rfl
    | two => exfalso; exact digit_in_region h H.box1 ((get_d k 5 2) f hf)
    | three => exfalso; exact digit_in_region h H.box1 ((get_d k 1 3) f hf)
    | four => exfalso; exact digit_in_region h H.box1 H.given4
  )
  replace k := add_fact k 3 2 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 3 with
    | two => rfl
    | one => exfalso; exact digit_in_region h H.row1 ((get_d k 0 1) f hf)
    | three => exfalso; exact digit_in_region h H.row1 ((get_d k 1 3) f hf)
    | four => exfalso; exact digit_in_region h H.row1 H.given2
  )
  replace k := add_fact k 7 1 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 with
    | one => rfl
    | two => exfalso; exact digit_in_region h H.row2 ((get_d k 5 2) f hf)
    | three => exfalso; exact digit_in_region h H.row2 H.given6
    | four => exfalso; exact digit_in_region h H.row2 H.given4
  )
  replace k := add_fact k 15 4 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 15 with
    | four => rfl
    | one => exfalso; exact digit_in_region h H.col4 ((get_d k 7 1) f hf)
    | two => exfalso; exact digit_in_region h H.col4 ((get_d k 3 2) f hf)
    | three => exfalso; exact digit_in_region h H.col4 H.given11
  )
  replace k := add_fact k 14 2 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 14 with
    | two => rfl
    | one => exfalso; exact digit_in_region h H.row4 H.given13
    | three => exfalso; exact digit_in_region h H.box4 H.given11
    | four => exfalso; exact digit_in_region h H.row4 ((get_d k 15 4) f hf)
  )
  replace k := add_fact k 10 1 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 10 with
    | one => rfl
    | two => exfalso; exact digit_in_region h H.box4 ((get_d k 14 2) f hf)
    | three => exfalso; exact digit_in_region h H.box4 H.given11
    | four => exfalso; exact digit_in_region h H.box4 ((get_d k 15 4) f hf)
  )
  replace k := add_fact k 8 2 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 8 with
    | two => rfl
    | one => exfalso; exact digit_in_region h H.row3 ((get_d k 10 1) f hf)
    | three => exfalso; exact digit_in_region h H.row3 H.given11
    | four => exfalso; exact digit_in_region h H.row3 H.given9
  )
  replace k := add_fact k 12 3 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 12 with
    | three => rfl
    | one => exfalso; exact digit_in_region h H.box3 H.given13
    | two => exfalso; exact digit_in_region h H.box3 ((get_d k 8 2) f hf)
    | four => exfalso; exact digit_in_region h H.box3 H.given9
  )
  -- create th function g and use it
  let digits: Array Symbols4 :=
    #[1,3,4,2,
      4,2,3,1,
      2,4,1,3,
      3,1,2,4]
  have len: digits.size = 16 := by decide
  let g : Nat → Symbols4 := fun x => digits[x]? |>.getD 1
  use g
  constructor
  · simp only
    apply (H g).mpr
    -- prove that g obeys the constraints of the puzzle
    constructor
    iterate 12 apply injOn_by_card; decide
    iterate 6 decide
    -- and outside the grid
    intro n hn
    unfold g
    conv =>
      enter [1, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  -- prove that forall h, h = g
  intro h hh
  replace H := (H h).mp hh
  ext x
  by_cases xin: x < 16
  · interval_cases x
    · exact (get_d k 0 1) h hh
    · exact (get_d k 1 3) h hh
    · exact H.given2
    · exact (get_d k 3 2) h hh
    · exact H.given4
    · exact (get_d k 5 2) h hh
    · exact H.given6
    · exact (get_d k 7 1) h hh
    · exact (get_d k 8 2) h hh
    · exact H.given9
    · exact (get_d k 10 1) h hh
    · exact H.given11
    · exact (get_d k 12 3) h hh
    · exact H.given13
    · exact (get_d k 14 2) h hh
    · exact (get_d k 15 4) h hh
  rw [H.outside_grid]
  · unfold g
    simp at xin
    conv =>
      enter [2, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  push_neg at xin
  apply xin
