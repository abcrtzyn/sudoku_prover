import SudokuLean.Basic
import SudokuLean.BaselineConstraints
import SudokuLean.Symbols9
import SudokuLean.Tactics
import Mathlib.Tactic.IntervalCases


set_option linter.style.whitespace false


-- this is the 18 clue tough from Andrew Stuart Sudoku Wiki
structure TestPuzzle2 (solution: Nat -> Symbols9) where
  b: NormalSudoku solution
  given1:  solution  1 = 3
  given5:  solution  5 = 7
  given10: solution 10 = 6
  given11: solution 11 = 7
  given12: solution 12 = 1
  given15: solution 15 = 3
  given16: solution 16 = 5
  given19: solution 19 = 1
  given20: solution 20 = 9
  given27: solution 27 = 5
  given35: solution 35 = 7
  given37: solution 37 = 7
  given39: solution 39 = 2
  given41: solution 41 = 3
  given43: solution 43 = 1
  given45: solution 45 = 9
  given53: solution 53 = 8
  given60: solution 60 = 6
  given61: solution 61 = 8
  given64: solution 64 = 8
  given65: solution 65 = 6
  given68: solution 68 = 2
  given69: solution 69 = 9
  given70: solution 70 = 7
  given75: solution 75 = 7
  given79: solution 79 = 4
  outside_grid: ∀ x, x ≥ 81 -> solution x = Symbols9.one -- just need something to call default




theorem SolveTestPuzzle2 {S : Set (Nat → Symbols9)} (H : ∀ f, f ∈ S ↔ TestPuzzle2 f):
  ∃! (g: Nat -> Symbols9), g ∈ S := by
  have k : IsSound S [] := by intro c d h; cases h

  replace k := add_fact k 2 5 (by
    -- hidden single in box 1
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box1)
    locked_support_cases h 5
    · exfalso; apply digit_in_region h H.b.col1 H.given27
    · exfalso; apply digit_in_cell h H.given1
    · assumption
    · exfalso; apply digit_in_region h H.b.col1 H.given27
    · exfalso; apply digit_in_cell h H.given10
    · exfalso; apply digit_in_cell h H.given11
    · exfalso; apply digit_in_region h H.b.col1 H.given27
    · exfalso; apply digit_in_cell h H.given19
    · exfalso; apply digit_in_cell h H.given20
  )
  replace k := add_fact k 24 7 (by
    -- hidden single in box 3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box3)
    locked_support_cases h 7
    · exfalso; apply digit_in_region h H.b.row1 H.given5
    · exfalso; apply digit_in_region h H.b.row1 H.given5
    · exfalso; apply digit_in_region h H.b.row1 H.given5
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_cell h H.given16
    · exfalso; apply digit_in_region h H.b.col9 H.given35
    · assumption
    · exfalso; apply digit_in_region h H.b.col8 H.given70
    · exfalso; apply digit_in_region h H.b.col9 H.given35
  )
  replace k := add_fact k 36 6 (by
    -- hidden single in box 4
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box4)
    locked_support_cases h 6
    · exfalso; apply digit_in_cell h H.given27
    · exfalso; apply digit_in_region h H.b.col2 H.given10
    · exfalso; apply digit_in_region h H.b.col3 H.given65
    · assumption
    · exfalso; apply digit_in_region h H.b.col2 H.given10
    · exfalso; apply digit_in_region h H.b.col3 H.given65
    · exfalso; apply digit_in_cell h H.given45
    · exfalso; apply digit_in_region h H.b.col2 H.given10
    · exfalso; apply digit_in_region h H.b.col3 H.given65
  )
  replace k := add_fact k 49 7 (by
    -- hidden single in box 5
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box5)
    locked_support_cases h 7
    · exfalso; apply digit_in_region h H.b.row4 H.given35
    · exfalso; apply digit_in_region h H.b.row4 H.given35
    · exfalso; apply digit_in_region h H.b.row4 H.given35
    · exfalso; apply digit_in_cell h H.given39
    · exfalso; apply digit_in_region h H.b.row5 H.given37
    · exfalso; apply digit_in_cell h H.given41
    · exfalso; apply digit_in_region h H.b.col4 H.given75
    · assumption
    · exfalso; apply digit_in_region h H.b.col6 H.given5
  )
  replace k := add_fact k 54 7 (by
    -- hidden single in box 7
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box7)
    locked_support_cases h 7
    · assumption
    · exfalso; apply digit_in_region h H.b.col2 H.given37
    · exfalso; apply digit_in_region h H.b.col3 H.given11
    · exfalso; apply digit_in_region h H.b.row8 H.given70
    · exfalso; apply digit_in_region h H.b.row8 H.given70
    · exfalso; apply digit_in_region h H.b.row8 H.given70
    · exfalso; apply digit_in_region h H.b.row9 H.given75
    · exfalso; apply digit_in_region h H.b.row9 H.given75
    · exfalso; apply digit_in_region h H.b.row9 H.given75
  )
  replace k := add_fact k 6 8 (by
    -- hidden single in box 3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box3)
    locked_support_cases h 8
    · assumption
    · exfalso; apply digit_in_region h H.b.col8 H.given61
    · exfalso; apply digit_in_region h H.b.col9 H.given53
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_region h H.b.col8 H.given61
    · exfalso; apply digit_in_region h H.b.col9 H.given53
    · exfalso; apply digit_in_cell h ((get_d k 24 7) f hf)
    · exfalso; apply digit_in_region h H.b.col8 H.given61
    · exfalso; apply digit_in_region h H.b.col9 H.given53
  )
  replace k := add_fact k 8 1 (by
    -- hidden single in box 3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.box3)
    locked_support_cases h 1
    · exfalso; apply digit_in_cell h ((get_d k 6 8) f hf)
    · exfalso; apply digit_in_region h H.b.col8 H.given43
    · assumption
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_cell h H.given16
    · exfalso; apply digit_in_region h H.b.row2 H.given12
    · exfalso; apply digit_in_cell h ((get_d k 24 7) f hf)
    · exfalso; apply digit_in_region h H.b.row3 H.given19
    · exfalso; apply digit_in_region h H.b.row3 H.given19
  )
  replace k := add_fact k 78 1 (by
    -- hidden single in column 7
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.col7)
    locked_support_cases h 1
    · exfalso; apply digit_in_cell h ((get_d k 6 8) f hf)
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_cell h ((get_d k 24 7) f hf)
    · exfalso; apply digit_in_region h H.b.box6 H.given43
    · exfalso; apply digit_in_region h H.b.box6 H.given43
    · exfalso; apply digit_in_region h H.b.box6 H.given43
    · exfalso; apply digit_in_cell h H.given60
    · exfalso; apply digit_in_cell h H.given69
    · assumption
  )
  replace k := add_fact k 26 6 (by
    -- hidden single in column 9
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.col9)
    locked_support_cases h 6
    · exfalso; apply digit_in_cell h ((get_d k 8 1) f hf)
    · exfalso; apply digit_in_region h H.b.row2 H.given10
    · assumption
    · exfalso; apply digit_in_cell h H.given35
    · exfalso; apply digit_in_region h H.b.row5 ((get_d k 36 6) f hf)
    · exfalso; apply digit_in_cell h H.given53
    · exfalso; apply digit_in_region h H.b.box9 H.given60
    · exfalso; apply digit_in_region h H.b.box9 H.given60
    · exfalso; apply digit_in_region h H.b.box9 H.given60
  )
  replace k := add_fact k 63 1 (by
    -- hidden single in column 1
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_locked_set H.b.col1)
    locked_support_cases h 1
    · exfalso; apply digit_in_region h H.b.box1 H.given19
    · exfalso; apply digit_in_region h H.b.box1 H.given19
    · exfalso; apply digit_in_region h H.b.box1 H.given19
    · exfalso; apply digit_in_cell h H.given27
    · exfalso; apply digit_in_cell h ((get_d k 36 6) f hf)
    · exfalso; apply digit_in_cell h H.given45
    · exfalso; apply digit_in_cell h ((get_d k 54 7) f hf)
    · assumption
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 78 1) f hf)
  )
  replace k := add_fact k 25 2 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 25 with
    | one => exfalso; exact digit_in_region h H.b.box3 ((get_d k 8 1) f hf)
    | two => rfl
    | three => exfalso; exact digit_in_region h H.b.box3 H.given15
    | four => exfalso; exact digit_in_region h H.b.col8 H.given79
    | five => exfalso; exact digit_in_region h H.b.box3 H.given16
    | six => exfalso; exact digit_in_region h H.b.box3 ((get_d k 26 6) f hf)
    | seven => exfalso; exact digit_in_region h H.b.box3 ((get_d k 24 7) f hf)
    | eight => exfalso; exact digit_in_region h H.b.box3 ((get_d k 6 8) f hf)
    | nine => exfalso; exact digit_in_region h H.b.row3 H.given20
  )
  replace k := add_fact k 7 9 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 with
    | one => exfalso; exact digit_in_region h H.b.box3 ((get_d k 8 1) f hf)
    | two => exfalso; exact digit_in_region h H.b.box3 ((get_d k 25 2) f hf)
    | three => exfalso; exact digit_in_region h H.b.box3 H.given15
    | four => exfalso; exact digit_in_region h H.b.col8 H.given79
    | five => exfalso; exact digit_in_region h H.b.box3 H.given16
    | six => exfalso; exact digit_in_region h H.b.box3 ((get_d k 26 6) f hf)
    | seven => exfalso; exact digit_in_region h H.b.box3 ((get_d k 24 7) f hf)
    | eight => exfalso; exact digit_in_region h H.b.box3 ((get_d k 6 8) f hf)
    | nine => rfl
  )
  replace k := add_fact k 17 4 (by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 17 with
    | one => exfalso; exact digit_in_region h H.b.box3 ((get_d k 8 1) f hf)
    | two => exfalso; exact digit_in_region h H.b.box3 ((get_d k 25 2) f hf)
    | three => exfalso; exact digit_in_region h H.b.box3 H.given15
    | four => rfl
    | five => exfalso; exact digit_in_region h H.b.box3 H.given16
    | six => exfalso; exact digit_in_region h H.b.box3 ((get_d k 26 6) f hf)
    | seven => exfalso; exact digit_in_region h H.b.box3 ((get_d k 24 7) f hf)
    | eight => exfalso; exact digit_in_region h H.b.box3 ((get_d k 6 8) f hf)
    | nine => exfalso; exact digit_in_region h H.b.box3 ((get_d k 7 9) f hf)
  )
  replace k := add_fact k 44 9 (by sorry
    -- hidden single
  )
  replace k := add_fact k 72 3 (by sorry
    -- hidden single
  )
  replace k := add_fact k 74 2 (by sorry
    -- naked single
  )
  replace k := add_fact k 56 4 (by sorry
    -- naked single
  )
  replace k := add_fact k 80 5 (by sorry
    -- naked single
  )
  replace k := add_fact k 38 8 (by sorry
    -- naked single
  )
  replace k := add_fact k 71 3 (by sorry
    -- naked single
  )
  replace k := add_fact k 73 9 (by sorry
    -- naked single
  )
  replace k := add_fact k 55 5 (by sorry
    -- naked single
  )
  replace k := add_fact k 62 2 (by sorry
    -- naked single
  -- pair in row 4
  )
  have c28c33pair: ∀ f (hf:f ∈ S), LockedSet f {28, 33} {2, 4} := by
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.row4)
    intro c h
    rcases h with rfl | rfl
    · cases h: f 28 with
      | one => exfalso; exact digit_in_region h H.b.col2 H.given19
      | two => simp
      | three => exfalso; exact digit_in_region h H.b.col2 H.given1
      | four => simp
      | five => exfalso; exact digit_in_region h H.b.col2 ((get_d k 55 5) f hf)
      | six => exfalso; exact digit_in_region h H.b.col2 H.given10
      | seven => exfalso; exact digit_in_region h H.b.col2 H.given37
      | eight => exfalso; exact digit_in_region h H.b.col2 H.given64
      | nine => exfalso; exact digit_in_region h H.b.col2 ((get_d k 73 9) f hf)
    · cases h: f 33 with
      | one => exfalso; exact digit_in_region h H.b.col7 ((get_d k 78 1) f hf)
      | two => simp
      | three => exfalso; exact digit_in_region h H.b.col7 H.given15
      | four => simp
      | five => exfalso; exact digit_in_region h H.b.row4 H.given27
      | six => exfalso; exact digit_in_region h H.b.col7 H.given60
      | seven => exfalso; exact digit_in_region h H.b.col7 ((get_d k 24 7) f hf)
      | eight => exfalso; exact digit_in_region h H.b.col7 ((get_d k 6 8) f hf)
      | nine => exfalso; exact digit_in_region h H.b.col7 H.given69
  have c40c67pair: ∀ f (hf:f ∈ S), LockedSet f {40, 67} {4, 5} := by
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.col5)
    intro c h
    rcases h with rfl | rfl
    · cases h: f 40 with
      | one => exfalso; exact digit_in_region h H.b.row5 H.given43
      | two => exfalso; exact digit_in_region h H.b.row5 H.given39
      | three => exfalso; exact digit_in_region h H.b.row5 H.given41
      | four => simp
      | five => simp
      | six => exfalso; exact digit_in_region h H.b.row5 ((get_d k 36 6) f hf)
      | seven => exfalso; exact digit_in_region h H.b.row5 H.given37
      | eight => exfalso; exact digit_in_region h H.b.row5 ((get_d k 38 8) f hf)
      | nine => exfalso; exact digit_in_region h H.b.row5 ((get_d k 44 9) f hf)
    · cases h: f 67 with
      | one => exfalso; exact digit_in_region h H.b.row8 ((get_d k 63 1) f hf)
      | two => exfalso; exact digit_in_region h H.b.row8 H.given68
      | three => exfalso; exact digit_in_region h H.b.row8 ((get_d k 71 3) f hf)
      | four => simp
      | five => simp
      | six => exfalso; exact digit_in_region h H.b.row8 H.given65
      | seven => exfalso; exact digit_in_region h H.b.row8 H.given70
      | eight => exfalso; exact digit_in_region h H.b.row8 H.given64
      | nine => exfalso; exact digit_in_region h H.b.row8 H.given69
  have c23c50pair: ∀ f (hf:f ∈ S), LockedSet f {23, 50} {4, 5} := by
    -- hidden pair in col 6
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_hidden_set (H.b.col6)
    intro d this
    rcases this with rfl | rfl
    · let h := (region_full_locked_set H.b.col6)
      locked_support_cases h 4
      · exfalso; exact digit_in_cell h H.given5
      · exfalso; exact digit_in_region h H.b.row2 ((get_d k 17 4) f hf)
      · exact ⟨_, by simp, h⟩
        -- first instance of using a pair to cross out a candidate
      · exfalso; refine locked_set_in_region h H.b.row4 (c28c33pair f hf)
      · exfalso; exact digit_in_cell h H.given41
      · exact ⟨_, by simp, h⟩
      · exfalso; exact digit_in_region h H.b.row7 ((get_d k 56 4) f hf)
      · exfalso; exact digit_in_cell h H.given68
      · exfalso; exact digit_in_region h H.b.row9 H.given79
    · let h := (region_full_locked_set H.b.col6)
      locked_support_cases h 5
      · exfalso; exact digit_in_cell h H.given5
      · exfalso; exact digit_in_region h H.b.row2 H.given16
      · exact ⟨_, by simp, h⟩
      · exfalso; refine digit_in_region h H.b.row4 H.given27
      · exfalso; exact digit_in_cell h H.given41
      · exact ⟨_, by simp, h⟩
      · exfalso; exact digit_in_region h H.b.row7 ((get_d k 55 5) f hf)
      · exfalso; exact digit_in_cell h H.given68
      · exfalso; exact digit_in_region h H.b.row9 ((get_d k 80 5) f hf)
  replace k := add_fact k 47 1 (by sorry)
    -- hidden single
  replace k := add_fact k 29 3 (by sorry)
    -- naked single
  replace k := add_fact k 34 6 (by sorry)
  replace k := add_fact k 52 3 (by sorry)
    -- naked single
  replace k := add_fact k 48 6 (by sorry)
    -- hidden single
  replace k := add_fact k 77 6 (by sorry)
    -- hidden single
  replace k := add_fact k 76 8 (by sorry)
    -- naked single
  replace k := add_fact k 3 4 (by sorry)
    -- naked single
  replace k := add_fact k 0 2 (by sorry)
    -- hidden single ↓
  replace k := add_fact k 22 3 (by sorry)
  replace k := add_fact k 23 5 (by
    intro f hf
    replace H := (H f).mp hf
    replace h := (c23c50pair f hf)
    locked_maps_cases h 23
    · exfalso; exact digit_in_region h H.b.box2 ((get_d k 3 4) f hf)
    · assumption
  )
  replace k := add_fact k 50 4 (by
    -- resolve pair c23c50
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_single
    simpa using locked_set_reducton (c23c50pair f hf) ((get_d k 23 5) f hf)
  )
  clear c23c50pair
  replace k := add_fact k 66 5 (by sorry)
  replace k := add_fact k 4 6 (by sorry)
    -- naked single ↓
  replace k := add_fact k 9 8 (by sorry)
  replace k := add_fact k 21 8 (by sorry)
  replace k := add_fact k 67 4 (by sorry)
  replace k := add_fact k 40 5 (by sorry)
  replace k := add_fact k 14 9 (by sorry)
  replace k := add_fact k 18 4 (by sorry)
  replace k := add_fact k 30 9 (by sorry)
  replace k := add_fact k 46 2 (by sorry)
  replace k := add_fact k 13 2 (by sorry)
  replace k := add_fact k 28 4 (by sorry)
  replace k := add_fact k 33 2 (by sorry)
  replace k := add_fact k 31 1 (by sorry)
  replace k := add_fact k 42 4 (by sorry)
  replace k := add_fact k 51 5 (by sorry)
  replace k := add_fact k 57 3 (by sorry)
  replace k := add_fact k 59 1 (by sorry)
  replace k := add_fact k 32 8 (by sorry)
  replace k := add_fact k 58 9 (by sorry)
  -- create th function g and use it
  let digits: Array Symbols9 :=
  #[2,3,5,4,6,7,8,9,1,
    8,6,7,1,2,9,3,5,4,
    4,1,9,8,3,5,7,2,6,
    5,4,3,9,1,8,2,6,7,
    6,7,8,2,5,3,4,1,9,
    9,2,1,6,7,4,5,3,8,
    7,5,4,3,9,1,6,8,2,
    1,8,6,5,4,2,9,7,3,
    3,9,2,7,8,6,1,4,5]
  have len: digits.size = 81 := by decide
  let g : Nat → Symbols9 := fun x => digits[x]? |>.getD 1
  use g
  constructor
  · simp only
    apply (H g).mpr
    -- prove that g obeys the constraints of the puzzle
    constructor
    · constructor
      iterate 27 apply injOn_by_card; decide
    iterate 26 decide
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
  by_cases xin: x < 81
  · interval_cases x
    · exact (get_d k 0 2) h hh
    · exact H.given1
    · exact (get_d k 2 5) h hh
    · exact (get_d k 3 4) h hh
    · exact (get_d k 4 6) h hh
    · exact H.given5
    · exact (get_d k 6 8) h hh
    · exact (get_d k 7 9) h hh
    · exact (get_d k 8 1) h hh
    · exact (get_d k 9 8) h hh
    · exact H.given10
    · exact H.given11
    · exact H.given12
    · exact (get_d k 13 2) h hh
    · exact (get_d k 14 9) h hh
    · exact H.given15
    · exact H.given16
    · exact (get_d k 17 4) h hh
    · exact (get_d k 18 4) h hh
    · exact H.given19
    · exact H.given20
    · exact (get_d k 21 8) h hh
    · exact (get_d k 22 3) h hh
    · exact (get_d k 23 5) h hh
    · exact (get_d k 24 7) h hh
    · exact (get_d k 25 2) h hh
    · exact (get_d k 26 6) h hh
    · exact H.given27
    · exact (get_d k 28 4) h hh
    · exact (get_d k 29 3) h hh
    · exact (get_d k 30 9) h hh
    · exact (get_d k 31 1) h hh
    · exact (get_d k 32 8) h hh
    · exact (get_d k 33 2) h hh
    · exact (get_d k 34 6) h hh
    · exact H.given35
    · exact (get_d k 36 6) h hh
    · exact H.given37
    · exact (get_d k 38 8) h hh
    · exact H.given39
    · exact (get_d k 40 5) h hh
    · exact H.given41
    · exact (get_d k 42 4) h hh
    · exact H.given43
    · exact (get_d k 44 9) h hh
    · exact H.given45
    · exact (get_d k 46 2) h hh
    · exact (get_d k 47 1) h hh
    · exact (get_d k 48 6) h hh
    · exact (get_d k 49 7) h hh
    · exact (get_d k 50 4) h hh
    · exact (get_d k 51 5) h hh
    · exact (get_d k 52 3) h hh
    · exact H.given53
    · exact (get_d k 54 7) h hh
    · exact (get_d k 55 5) h hh
    · exact (get_d k 56 4) h hh
    · exact (get_d k 57 3) h hh
    · exact (get_d k 58 9) h hh
    · exact (get_d k 59 1) h hh
    · exact H.given60
    · exact H.given61
    · exact (get_d k 62 2) h hh
    · exact (get_d k 63 1) h hh
    · exact H.given64
    · exact H.given65
    · exact (get_d k 66 5) h hh
    · exact (get_d k 67 4) h hh
    · exact H.given68
    · exact H.given69
    · exact H.given70
    · exact (get_d k 71 3) h hh
    · exact (get_d k 72 3) h hh
    · exact (get_d k 73 9) h hh
    · exact (get_d k 74 2) h hh
    · exact H.given75
    · exact (get_d k 76 8) h hh
    · exact (get_d k 77 6) h hh
    · exact (get_d k 78 1) h hh
    · exact H.given79
    · exact (get_d k 80 5) h hh
  rw [H.outside_grid]
  · unfold g
    simp at xin
    conv =>
      enter [2, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  push_neg at xin
  apply xin
