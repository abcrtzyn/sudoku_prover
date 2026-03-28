import SudokuProverLogic.Basic
import SudokuProverLogic.BaselineConstraints
import SudokuProverLogic.Symbols9
import SudokuProverLogic.Tactics
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

lemma c2 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 2 = 5 := by
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

lemma c24 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 24 = 7 := by
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

lemma c36 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 36 = 6 := by
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

lemma c49 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 49 = 7 := by
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

lemma c54 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 54 = 7 := by
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

lemma c6 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 6 = 8 := by
  let h := (region_full_locked_set H.b.box3)
  locked_support_cases h 8
  · assumption
  · exfalso; apply digit_in_region h H.b.col8 H.given61
  · exfalso; apply digit_in_region h H.b.col9 H.given53
  · exfalso; apply digit_in_cell h H.given15
  · exfalso; apply digit_in_region h H.b.col8 H.given61
  · exfalso; apply digit_in_region h H.b.col9 H.given53
  · exfalso; apply digit_in_cell h (c24 H)
  · exfalso; apply digit_in_region h H.b.col8 H.given61
  · exfalso; apply digit_in_region h H.b.col9 H.given53
lemma c8 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 8 = 1 := by
  let h := (region_full_locked_set H.b.box3)
  locked_support_cases h 1
  · exfalso; apply digit_in_cell h (c6 H)
  · exfalso; apply digit_in_region h H.b.col8 H.given43
  · assumption
  · exfalso; apply digit_in_cell h H.given15
  · exfalso; apply digit_in_cell h H.given16
  · exfalso; apply digit_in_region h H.b.row2 H.given12
  · exfalso; apply digit_in_cell h (c24 H)
  · exfalso; apply digit_in_region h H.b.row3 H.given19
  · exfalso; apply digit_in_region h H.b.row3 H.given19

lemma c78 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 78 = 1 := by
  let h := (region_full_locked_set H.b.col7)
  locked_support_cases h 1
  · exfalso; apply digit_in_cell h (c6 H)
  · exfalso; apply digit_in_cell h H.given15
  · exfalso; apply digit_in_cell h (c24 H)
  · exfalso; apply digit_in_region h H.b.box6 H.given43
  · exfalso; apply digit_in_region h H.b.box6 H.given43
  · exfalso; apply digit_in_region h H.b.box6 H.given43
  · exfalso; apply digit_in_cell h H.given60
  · exfalso; apply digit_in_cell h H.given69
  · assumption

lemma c26 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 26 = 6 := by
  let h := (region_full_locked_set H.b.col9)
  locked_support_cases h 6
  · exfalso; apply digit_in_cell h (c8 H)
  · exfalso; apply digit_in_region h H.b.row2 H.given10
  · assumption
  · exfalso; apply digit_in_cell h H.given35
  · exfalso; apply digit_in_region h H.b.row5 (c36 H)
  · exfalso; apply digit_in_cell h H.given53
  · exfalso; apply digit_in_region h H.b.box9 H.given60
  · exfalso; apply digit_in_region h H.b.box9 H.given60
  · exfalso; apply digit_in_region h H.b.box9 H.given60

lemma c63 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 63 = 1 := by
  let h := (region_full_locked_set H.b.col1)
  locked_support_cases h 1
  · exfalso; apply digit_in_region h H.b.box1 H.given19
  · exfalso; apply digit_in_region h H.b.box1 H.given19
  · exfalso; apply digit_in_region h H.b.box1 H.given19
  · exfalso; apply digit_in_cell h H.given27
  · exfalso; apply digit_in_cell h (c36 H)
  · exfalso; apply digit_in_cell h H.given45
  · exfalso; apply digit_in_cell h (c54 H)
  · assumption
  · exfalso; apply digit_in_region h H.b.row9 (c78 H)

lemma c25 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 25 = 2 := by
  cases h: f 25 with
  | one => exfalso; exact digit_in_region h H.b.box3 (c8 H)
  | two => rfl
  | three => exfalso; exact digit_in_region h H.b.box3 H.given15
  | four => exfalso; exact digit_in_region h H.b.col8 H.given79
  | five => exfalso; exact digit_in_region h H.b.box3 H.given16
  | six => exfalso; exact digit_in_region h H.b.box3 (c26 H)
  | seven => exfalso; exact digit_in_region h H.b.box3 (c24 H)
  | eight => exfalso; exact digit_in_region h H.b.box3 (c6 H)
  | nine => exfalso; exact digit_in_region h H.b.row3 H.given20

lemma c7  {f: Nat -> Symbols9} (H: TestPuzzle2 f): f  7 = 9 := by
  cases h: f 7 with
  | one => exfalso; exact digit_in_region h H.b.box3 (c8 H)
  | two => exfalso; exact digit_in_region h H.b.box3 (c25 H)
  | three => exfalso; exact digit_in_region h H.b.box3 H.given15
  | four => exfalso; exact digit_in_region h H.b.col8 H.given79
  | five => exfalso; exact digit_in_region h H.b.box3 H.given16
  | six => exfalso; exact digit_in_region h H.b.box3 (c26 H)
  | seven => exfalso; exact digit_in_region h H.b.box3 (c24 H)
  | eight => exfalso; exact digit_in_region h H.b.box3 (c6 H)
  | nine => rfl

lemma c17 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 17 = 4 := by
  cases h: f 17 with
  | one => exfalso; exact digit_in_region h H.b.box3 (c8 H)
  | two => exfalso; exact digit_in_region h H.b.box3 (c25 H)
  | three => exfalso; exact digit_in_region h H.b.box3 H.given15
  | four => rfl
  | five => exfalso; exact digit_in_region h H.b.box3 H.given16
  | six => exfalso; exact digit_in_region h H.b.box3 (c26 H)
  | seven => exfalso; exact digit_in_region h H.b.box3 (c24 H)
  | eight => exfalso; exact digit_in_region h H.b.box3 (c6 H)
  | nine => exfalso; exact digit_in_region h H.b.box3 (c7 H)

lemma c44 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 44 = 9 := by sorry
lemma c72 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 72 = 3 := by sorry
lemma c74 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 74 = 2 := by sorry
lemma c56 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 56 = 4 := by sorry
lemma c80 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 80 = 5 := by sorry
lemma c38 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 38 = 8 := by sorry
lemma c71 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 71 = 3 := by sorry
lemma c73 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 73 = 9 := by sorry
lemma c55 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 55 = 5 := by sorry
lemma c62 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 62 = 2 := by sorry
lemma c28c33pair {f: Nat -> Symbols9} (H: TestPuzzle2 f): LockedSet f {28, 33} {2, 4} := by
  apply locked_set_from_naked_set (H.b.row4)
  intro c h
  rcases h with rfl | rfl
  · cases h: f 28 with
    | one => exfalso; exact digit_in_region h H.b.col2 H.given19
    | two => simp
    | three => exfalso; exact digit_in_region h H.b.col2 H.given1
    | four => simp
    | five => exfalso; exact digit_in_region h H.b.col2 (c55 H)
    | six => exfalso; exact digit_in_region h H.b.col2 H.given10
    | seven => exfalso; exact digit_in_region h H.b.col2 H.given37
    | eight => exfalso; exact digit_in_region h H.b.col2 H.given64
    | nine => exfalso; exact digit_in_region h H.b.col2 (c73 H)
  · cases h: f 33 with
    | one => exfalso; exact digit_in_region h H.b.col7 (c78 H)
    | two => simp
    | three => exfalso; exact digit_in_region h H.b.col7 H.given15
    | four => simp
    | five => exfalso; exact digit_in_region h H.b.row4 H.given27
    | six => exfalso; exact digit_in_region h H.b.col7 H.given60
    | seven => exfalso; exact digit_in_region h H.b.col7 (c24 H)
    | eight => exfalso; exact digit_in_region h H.b.col7 (c6 H)
    | nine => exfalso; exact digit_in_region h H.b.col7 H.given69

lemma c40c67pair {f: Nat -> Symbols9} (H: TestPuzzle2 f): LockedSet f {40, 67} {4, 5} := by
  apply locked_set_from_naked_set (H.b.col5)
  intro c h
  rcases h with rfl | rfl
  · cases h: f 40 with
    | one => exfalso; exact digit_in_region h H.b.row5 H.given43
    | two => exfalso; exact digit_in_region h H.b.row5 H.given39
    | three => exfalso; exact digit_in_region h H.b.row5 H.given41
    | four => simp
    | five => simp
    | six => exfalso; exact digit_in_region h H.b.row5 (c36 H)
    | seven => exfalso; exact digit_in_region h H.b.row5 H.given37
    | eight => exfalso; exact digit_in_region h H.b.row5 (c38 H)
    | nine => exfalso; exact digit_in_region h H.b.row5 (c44 H)
  · cases h: f 67 with
    | one => exfalso; exact digit_in_region h H.b.row8 (c63 H)
    | two => exfalso; exact digit_in_region h H.b.row8 H.given68
    | three => exfalso; exact digit_in_region h H.b.row8 (c71 H)
    | four => simp
    | five => simp
    | six => exfalso; exact digit_in_region h H.b.row8 H.given65
    | seven => exfalso; exact digit_in_region h H.b.row8 H.given70
    | eight => exfalso; exact digit_in_region h H.b.row8 H.given64
    | nine => exfalso; exact digit_in_region h H.b.row8 H.given69

lemma c23c50pair {f: Nat -> Symbols9} (H: TestPuzzle2 f): LockedSet f {23, 50} {4, 5} := by
  -- hidden pair in col 6
  apply locked_set_from_hidden_set (H.b.col6)
  intro d this
  let h := (region_full_locked_set H.b.col6)
  rcases this with rfl | rfl
  · locked_support_cases h 4
    · exfalso; exact digit_in_cell h H.given5
    · exfalso; exact digit_in_region h H.b.row2 (c17 H)
    · exact ⟨_, by simp, h⟩
      -- first instance of using a pair to cross out a candidate
    · exfalso; refine locked_set_in_region h H.b.row4 (c28c33pair H)
    · exfalso; exact digit_in_cell h H.given41
    · exact ⟨_, by simp, h⟩
    · exfalso; exact digit_in_region h H.b.row7 (c56 H)
    · exfalso; exact digit_in_cell h H.given68
    · exfalso; exact digit_in_region h H.b.row9 H.given79
  · locked_support_cases h 5
    · exfalso; exact digit_in_cell h H.given5
    · exfalso; exact digit_in_region h H.b.row2 H.given16
    · exact ⟨_, by simp, h⟩
    · exfalso; refine digit_in_region h H.b.row4 H.given27
    · exfalso; exact digit_in_cell h H.given41
    · exact ⟨_, by simp, h⟩
    · exfalso; exact digit_in_region h H.b.row7 (c55 H)
    · exfalso; exact digit_in_cell h H.given68
    · exfalso; exact digit_in_region h H.b.row9 (c80 H)

lemma c47 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 47 = 1 := by sorry
lemma c29 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 29 = 3 := by sorry
lemma c34 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 34 = 6 := by sorry
lemma c52 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 52 = 3 := by sorry
lemma c48 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 48 = 6 := by sorry
lemma c77 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 77 = 6 := by sorry
lemma c76 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 76 = 8 := by sorry
lemma c3  {f: Nat -> Symbols9} (H: TestPuzzle2 f): f  3 = 4 := by sorry
lemma c0  {f: Nat -> Symbols9} (H: TestPuzzle2 f): f  0 = 2 := by sorry
lemma c22 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 22 = 3 := by sorry
lemma c23 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 23 = 5 := by
  replace h := (c23c50pair H)
  locked_maps_cases h 23
  · exfalso; exact digit_in_region h H.b.box2 (c3 H)
  · assumption

lemma c50 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 50 = 4 := by
  -- resolve pair c23c50
  apply locked_set_single
  simpa using locked_set_reducton (c23c50pair H) (c23 H)

lemma c66 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 66 = 5 := by sorry
lemma c4  {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 4  = 6 := by sorry
lemma c9  {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 9  = 8 := by sorry
lemma c21 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 21 = 8 := by sorry
lemma c67 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 67 = 4 := by sorry
lemma c40 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 40 = 5 := by sorry
lemma c14 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 14 = 9 := by sorry
lemma c18 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 18 = 4 := by sorry
lemma c30 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 30 = 9 := by sorry
lemma c46 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 46 = 2 := by sorry
lemma c13 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 13 = 2 := by sorry
lemma c28 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 28 = 4 := by sorry
lemma c33 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 33 = 2 := by sorry
lemma c31 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 31 = 1 := by sorry
lemma c42 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 42 = 4 := by sorry
lemma c51 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 51 = 5 := by sorry
lemma c57 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 57 = 3 := by sorry
lemma c59 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 59 = 1 := by sorry
lemma c32 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 32 = 8 := by sorry
lemma c58 {f: Nat -> Symbols9} (H: TestPuzzle2 f): f 58 = 9 := by sorry


theorem SolveTestPuzzle2 {S : Set (Nat → Symbols9)} (H : ∀ f, f ∈ S ↔ TestPuzzle2 f):
  ∃! (g: Nat -> Symbols9), g ∈ S := by
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
    · exact (c0 H)
    · exact H.given1
    · exact (c2 H)
    · exact (c3 H)
    · exact (c4 H)
    · exact H.given5
    · exact (c6 H)
    · exact (c7 H)
    · exact (c8 H)
    · exact (c9 H)
    · exact H.given10
    · exact H.given11
    · exact H.given12
    · exact (c13 H)
    · exact (c14 H)
    · exact H.given15
    · exact H.given16
    · exact (c17 H)
    · exact (c18 H)
    · exact H.given19
    · exact H.given20
    · exact (c21 H)
    · exact (c22 H)
    · exact (c23 H)
    · exact (c24 H)
    · exact (c25 H)
    · exact (c26 H)
    · exact H.given27
    · exact (c28 H)
    · exact (c29 H)
    · exact (c30 H)
    · exact (c31 H)
    · exact (c32 H)
    · exact (c33 H)
    · exact (c34 H)
    · exact H.given35
    · exact (c36 H)
    · exact H.given37
    · exact (c38 H)
    · exact H.given39
    · exact (c40 H)
    · exact H.given41
    · exact (c42 H)
    · exact H.given43
    · exact (c44 H)
    · exact H.given45
    · exact (c46 H)
    · exact (c47 H)
    · exact (c48 H)
    · exact (c49 H)
    · exact (c50 H)
    · exact (c51 H)
    · exact (c52 H)
    · exact H.given53
    · exact (c54 H)
    · exact (c55 H)
    · exact (c56 H)
    · exact (c57 H)
    · exact (c58 H)
    · exact (c59 H)
    · exact H.given60
    · exact H.given61
    · exact (c62 H)
    · exact (c63 H)
    · exact H.given64
    · exact H.given65
    · exact (c66 H)
    · exact (c67 H)
    · exact H.given68
    · exact H.given69
    · exact H.given70
    · exact (c71 H)
    · exact (c72 H)
    · exact (c73 H)
    · exact (c74 H)
    · exact H.given75
    · exact (c76 H)
    · exact (c77 H)
    · exact (c78 H)
    · exact H.given79
    · exact (c80 H)
  rw [H.outside_grid]
  · unfold g
    simp at xin
    conv =>
      enter [2, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  push_neg at xin
  apply xin
