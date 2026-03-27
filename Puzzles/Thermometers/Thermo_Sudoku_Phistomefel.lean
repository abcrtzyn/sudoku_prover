import SudokuProverLogic.Basic
import SudokuProverLogic.Symbols9
import SudokuProverLogic.Thermometer
import SudokuProverLogic.Tactics
import SudokuProverLogic.BaselineConstraints
import Mathlib.Tactic.IntervalCases

set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option warningAsError true

-- Thermo Sudoku by Phistomefel
-- https://logic-masters.de/Raetselportal/Raetsel/zeigen.php?id=000362
structure ThermoSudoku (solution: Nat -> Symbols9) where
b: NormalSudoku solution
thermo1: Thermometer solution [27,18,9,10]
thermo2: Thermometer solution [28,29,20,11,2,1]
thermo3: Thermometer solution [13,4,5,6,7]
thermo4: Thermometer solution [13,14,15,16]
thermo5: Thermometer solution [30,39]
thermo6: Thermometer solution [55,64,73,74,65]
thermo7: Thermometer solution [58,49,50,51]
thermo8: Thermometer solution [60,61,62,71,70]
thermo9: Thermometer solution [80,79,78,77,68,69]
outside_grid: ∀ x, x ≥ 81 -> solution x = Symbols9.one


-- there is a set of 8s and 9s in box 9 pointing in row 8
lemma row8point8 {f: Nat -> Symbols9} (H: ThermoSudoku f): SupportSet f {69,70,71} 8 := by
  let h := (region_full_locked_set H.b.box9)
  locked_support_cases h 8
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 2
  · exact in_support_set h
  · exact in_support_set h
  · exact in_support_set h
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 2
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 0

lemma row8point9 {f: Nat -> Symbols9} (H: ThermoSudoku f): SupportSet f {69,70} 9 := by
  let h := (region_full_locked_set H.b.box9)
  locked_support_cases h 9
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 2
  · exact in_support_set h
  · exact in_support_set h
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 3
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 2
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 0

lemma c65max7 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 65 ≤ 7 := by
  cases h: f 65 <;> try decide
  · exfalso; exact support_set_in_region h H.b.row8 (row8point8 H)
  · exfalso; exact support_set_in_region h H.b.row8 (row8point9 H)

lemma c68max7 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 68 ≤ 7 := by
  cases h: f 68 <;> try decide
  · exfalso; exact support_set_in_region h H.b.row8 (row8point8 H)
  · exfalso; exact support_set_in_region h H.b.row8 (row8point9 H)

-- hidden triple 789 in row 9. allows a hidden pointing pair 6
lemma c72c75c76triple {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {72,75,76} {7,8,9} := by
  apply locked_set_from_hidden_set (H.b.row9)
  intro d ds
  let h := (region_full_locked_set H.b.row9)
  rcases ds with rfl | rfl | rfl
  · locked_support_cases h 7
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 3
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 3
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 0
  · locked_support_cases h 8
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 3
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 3
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 0
  · locked_support_cases h 9
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 3
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 3
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 0

lemma row9point6 {f: Nat -> Symbols9} (H: ThermoSudoku f): SupportSet f {74, 77} 6 := by
  let h := (region_full_locked_set H.b.row9)
  locked_support_cases h 6
  · exfalso; exact locked_set_in_cell h (c72c75c76triple H)
  · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 H) 2
  · exact in_support_set h
  · exfalso; exact locked_set_in_cell h (c72c75c76triple H)
  · exfalso; exact locked_set_in_cell h (c72c75c76triple H)
  · exact in_support_set h
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 2
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 0

lemma row8point7 {f: Nat -> Symbols9} (H: ThermoSudoku f): SupportSet f {65,68} 7 := by
  let h := (row9point6 H)
  support_cases h
  · apply in_support_set (x:=65)
    apply ToNat.toNat_injective (fill_thermo H.thermo6 3 (by decide) h.symm.le 4 (by decide) (c65max7 H) (by decide) 4)
  · apply in_support_set (x:=68)
    apply ToNat.toNat_injective (fill_thermo H.thermo9 3 (by decide) h.symm.le 4 (by decide) (c68max7 H) (by decide) 4)

lemma c62 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 62 = 7 := by
  -- hidden single in box 9
  let h := support_set_from_locked_set (region_full_locked_set H.b.box9) 7
  support_cases h
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 1
  · exact h
  · exfalso; apply support_set_in_region h H.b.row8 (row8point7 H)
  · exfalso; apply support_set_in_region h H.b.row8 (row8point7 H)
  · exfalso; apply support_set_in_region h H.b.row8 (row8point7 H)
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 2
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 H) 0

lemma c71 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 71 = 8 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo8 2 (by decide) (c62 H).symm.le 4 (by decide) le_top (by decide) 3)

lemma c70 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 70 = 9 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo8 2 (by decide) (c62 H).symm.le 4 (by decide) le_top (by decide) 4)

lemma c69 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 69 = 6 := by
  -- naked single
  cases h: f 69 <;> try exfalso; apply digit_less_than_thermo_min h H.thermo9 0 (by decide) bot_le 5
  · rfl
  · exfalso; apply digit_in_region h H.b.box9 (c62 H)
  · exfalso; apply digit_in_region h H.b.box9 (c71 H)
  · exfalso; apply digit_in_region h H.b.box9 (c70 H)

-- fill thermo9
lemma c80 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 80 = 1 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) (c69 H).le (by decide) 0)

lemma c79 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 79 = 2 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) (c69 H).le (by decide) 1)

lemma c78 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 78 = 3 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) (c69 H).le (by decide) 2)

lemma c77 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 77 = 4 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) (c69 H).le (by decide) 3)

lemma c68 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 68 = 5 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) (c69 H).le (by decide) 4)

lemma c73min5 {f: Nat -> Symbols9} (H: ThermoSudoku f): 5 ≤ f 73 := by
  cases h: f 73 <;> try decide
  · exfalso; apply digit_in_region h H.b.row9 (c80 H)
  · exfalso; apply digit_in_region h H.b.row9 (c79 H)
  · exfalso; apply digit_in_region h H.b.row9 (c78 H)
  · exfalso; apply digit_in_region h H.b.row9 (c77 H)

lemma c73 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 73 = 5 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo6 2 (by decide) (c73min5 H) 4 (by decide) (c65max7 H) (by decide) 2)

lemma c74 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 74 = 6 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo6 2 (by decide) (c73min5 H) 4 (by decide) (c65max7 H) (by decide) 3)

lemma c65 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 65 = 7 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo6 2 (by decide) (c73min5 H) 4 (by decide) (c65max7 H) (by decide) 4)

-- lets clean up some pencil marks
lemma c60min4 {f: Nat -> Symbols9} (H: ThermoSudoku f): 4 ≤ f 60 := by
  cases h: f 60 <;> try decide
  · exfalso; apply digit_in_region h H.b.box9 (c80 H)
  · exfalso; apply digit_in_region h H.b.box9 (c79 H)
  · exfalso; apply digit_in_region h H.b.box9 (c78 H)

lemma c61max5 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 61 ≤ 5 := by
  cases h: f 61 <;> try decide
  · exfalso; apply digit_in_region h H.b.box9 (c69 H)
  · exfalso; apply digit_in_region h H.b.box9 (c62 H)
  · exfalso; apply digit_in_region h H.b.box9 (c71 H)
  · exfalso; apply digit_in_region h H.b.box9 (c70 H)

lemma c60 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 60 = 4 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo8 0 (by decide) (c60min4 H) 1 (by decide) (c61max5 H) (by decide) 0)

lemma c61 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 61 = 5 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo8 0 (by decide) (c60min4 H) 1 (by decide) (c61max5 H) (by decide) 1)

lemma row3point1 {f: Nat -> Symbols9} (H: ThermoSudoku f): SupportSet f {24,25} 1 := by
  let h := (region_full_locked_set H.b.box3)
  locked_support_cases h 1
  · exfalso; apply bottom_is_only_first h H.thermo3
  · exfalso; apply bottom_is_only_first h H.thermo3
  · exfalso; apply digit_in_region h H.b.col9 (c80 H)
  · exfalso; apply bottom_is_only_first h H.thermo4
  · exfalso; apply bottom_is_only_first h H.thermo4
  · exfalso; apply digit_in_region h H.b.col9 (c80 H)
  · exact in_support_set h
  · exact in_support_set h
  · exfalso; apply digit_in_region h H.b.col9 (c80 H)

lemma c0 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 0 = 1 := by
  let h := (region_full_locked_set H.b.box1)
  locked_support_cases h 1
  · assumption
  · exfalso; apply bottom_is_only_first h H.thermo2
  · exfalso; apply bottom_is_only_first h H.thermo2
  · exfalso; apply bottom_is_only_first h H.thermo1
  · exfalso; apply bottom_is_only_first h H.thermo1
  · exfalso; apply bottom_is_only_first h H.thermo2
  · exfalso; apply bottom_is_only_first h H.thermo1
  · exfalso; apply support_set_in_region h H.b.row3 (row3point1 H)
  · exfalso; apply bottom_is_only_first h H.thermo2

lemma c27min2 {f: Nat -> Symbols9} (H: ThermoSudoku f): 2 ≤ f 27 := by
  cases h: f 27 <;> try decide
  · exfalso; apply digit_in_region h H.b.col1 (c0 H)

lemma c19 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 19 = 2 := by
  let h := (region_full_locked_set H.b.box1)
  locked_support_cases h 2
  · exfalso; apply digit_in_cell h (c0 H)
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 5
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 4
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min2 H) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min2 H) 3
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 3
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min2 H) 1
  · exact h
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 2

lemma c11max5 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 11 ≤ 5 := by
  cases h: f 11 <;> first | decide | exfalso; apply digit_greater_than_thermo_max h H.thermo2 5 (by decide) le_top 3 | exfalso
  · exfalso; apply digit_in_region h H.b.col3 (c74 H)
  · exfalso; apply digit_in_region h H.b.col3 (c65 H)

lemma c28 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 28 = 1 := by
  -- set up upper bound of 2 for this cell
  cases h: f 28 <;> try exfalso; apply digit_greater_than_thermo_max h H.thermo2 3 (by decide) (c11max5 H) 0
  · rfl
  · exfalso; apply digit_in_region h H.b.col2 (c19 H)

lemma c55 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 55 = 3 := by
  -- set up upper bound of 3 for this cell
  cases h: f 55 <;> try exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65 H).le 0
  · exfalso; apply digit_in_region h H.b.col2 (c28 H)
  · exfalso; apply digit_in_region h H.b.col2 (c19 H)
  · rfl

lemma c64 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 64 = 4 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo6 0 (by decide) ((c55 H).symm.le) 4 (by decide) ((c65 H).le) (by decide) 1)

lemma c63 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 63 = 2 := by
  -- naked single
  cases h: f 63
  · exfalso; apply digit_in_region h H.b.col1 (c0 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.box7 (c55 H)
  · exfalso; apply digit_in_region h H.b.box7 (c64 H)
  · exfalso; apply digit_in_region h H.b.box7 (c73 H)
  · exfalso; apply digit_in_region h H.b.box7 (c74 H)
  · exfalso; apply digit_in_region h H.b.box7 (c65 H)
  · exfalso; apply digit_in_region h H.b.row8 (c71 H)
  · exfalso; apply digit_in_region h H.b.row8 (c70 H)

lemma c27min3 {f: Nat -> Symbols9} (H: ThermoSudoku f): 3 ≤ f 27 := by
  cases h: f 27 <;> try decide
  · exfalso; apply digit_in_region h H.b.col1 (c0 H)
  · exfalso; apply digit_in_region h H.b.col1 (c63 H)


lemma c20 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 20 = 3 := by
  let h := (region_full_locked_set H.b.box1)
  locked_support_cases h 3
  · exfalso; apply digit_in_cell h (c0 H)
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 5
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 4
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 H) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 H) 3
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 3
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 H) 1
  · exfalso; apply digit_in_cell h (c19 H)
  · exact h

lemma c29 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 29 = 2 := by
  apply ToNat.toNat_injective (fill_thermo H.thermo2 0 (by decide) ((c28 H).symm.le) 2 (by decide) ((c20 H).le) (by decide) 1 (by decide))


lemma c6min5 {f: Nat -> Symbols9} (H: ThermoSudoku f): 5 ≤ f 6 := by
  -- thermo3 min is 4, 4 in column
  cases h: f 6 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo3 0 (by decide) bot_le 3 | exfalso
  · apply digit_in_region h H.b.col7 (c60 H)

lemma c15min5 {f: Nat -> Symbols9} (H: ThermoSudoku f): 5 ≤ f 15 := by
  -- thermo4 min is 3, 3 and 4 in column
  cases h: f 15 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo4 0 (by decide) bot_le 2 | exfalso
  · apply digit_in_region h H.b.col7 (c78 H)
  · apply digit_in_region h H.b.col7 (c60 H)

lemma c7max8 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 7 ≤ 8 := by
  cases h: f 7 <;> first | decide | exfalso
  · apply digit_in_region h H.b.col8 (c70 H)

lemma c16max8 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 16 ≤ 8 := by
  cases h: f 16 <;> first | decide | exfalso
  · apply digit_in_region h H.b.col8 (c70 H)

lemma c6c15pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {6,15} {5,7} := by
  -- by min max, and 6 in col
  apply locked_set_from_naked_set (H.b.box3)
  intro c h
  rcases h with rfl | rfl
  · cases h: f 6 <;> first | decide | absurd (c6min5 H); rw [h]; decide | exfalso
    · apply digit_in_region h H.b.col7 (c69 H)
    · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 H) 3
    · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 H) 3
  · cases h: f 15 <;> first | decide | absurd (c15min5 H); rw [h]; decide | exfalso
    · apply digit_in_region h H.b.col7 (c69 H)
    · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) (c16max8 H) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) (c16max8 H) 2

lemma c7c16pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {7,16} {6,8} := by
  -- by min max, and 7 in box
  apply locked_set_from_naked_set (H.b.box3)
  intro c h
  rcases h with rfl | rfl
  · cases h: f 7 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo3 3 (by decide) (c6min5 H) 4 | exfalso
    · apply locked_set_in_region h H.b.box3 (c6c15pair H)
    · absurd (c7max8 H); rw [h]; decide
  · cases h: f 16 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo4 2 (by decide) (c15min5 H) 3 | exfalso
    · apply locked_set_in_region h H.b.box3 (c6c15pair H)
    · absurd (c16max8 H); rw [h]; decide

lemma c8c17pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {8,17} {2,3} := by
  -- hidden in box using thermo mins
  apply locked_set_from_hidden_set (H.b.box3)
  intro d this
  let h := (region_full_locked_set H.b.box3)
  rcases this with rfl | rfl
  · locked_support_cases h 2
    · exfalso; apply locked_set_in_cell h (c6c15pair H)
    · exfalso; apply locked_set_in_cell h (c7c16pair H)
    · exact ⟨_, by simp, h⟩
    · exfalso; apply locked_set_in_cell h (c6c15pair H)
    · exfalso; apply locked_set_in_cell h (c7c16pair H)
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_in_region h H.b.row3 (c19 H)
    · exfalso; apply digit_in_region h H.b.row3 (c19 H)
    · exfalso; apply digit_in_region h H.b.row3 (c19 H)
  · locked_support_cases h 3
    · exfalso; apply locked_set_in_cell h (c6c15pair H)
    · exfalso; apply locked_set_in_cell h (c7c16pair H)
    · exact ⟨_, by simp, h⟩
    · exfalso; apply locked_set_in_cell h (c6c15pair H)
    · exfalso; apply locked_set_in_cell h (c7c16pair H)
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_in_region h H.b.row3 (c20 H)
    · exfalso; apply digit_in_region h H.b.row3 (c20 H)
    · exfalso; apply digit_in_region h H.b.row3 (c20 H)

lemma c24c25c26triple {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {24,25,26} {1,4,9} := by
  apply locked_set_from_naked_set (H.b.box3)
  intro c ch
  cases h: f c
  · decide
  · exfalso; refine locked_set_in_region h H.b.box3 (c8c17pair H) (by simp [Set.subset_def]) (by decide) ?_ ?_
    rcases ch with rfl | rfl | rfl <;> decide
    rcases ch with rfl | rfl | rfl <;> decide
  · exfalso; refine locked_set_in_region h H.b.box3 (c8c17pair H) (by simp [Set.subset_def]) (by decide) ?_ ?_
    rcases ch with rfl | rfl | rfl <;> decide
    rcases ch with rfl | rfl | rfl <;> decide
  · decide
  · exfalso; refine locked_set_in_region h H.b.box3 (c6c15pair H) (by simp [Set.subset_def]) (by decide) ?_ ?_
    rcases ch with rfl | rfl | rfl <;> decide
    rcases ch with rfl | rfl | rfl <;> decide
  · exfalso; refine locked_set_in_region h H.b.box3 (c7c16pair H) (by simp [Set.subset_def]) (by decide) ?_ ?_
    rcases ch with rfl | rfl | rfl <;> decide
    rcases ch with rfl | rfl | rfl <;> decide
  · exfalso; refine locked_set_in_region h H.b.box3 (c6c15pair H) (by simp [Set.subset_def]) (by decide) ?_ ?_
    rcases ch with rfl | rfl | rfl <;> decide
    rcases ch with rfl | rfl | rfl <;> decide
  · exfalso; refine locked_set_in_region h H.b.box3 (c7c16pair H) (by simp [Set.subset_def]) (by decide) ?_ ?_
    rcases ch with rfl | rfl | rfl <;> decide
    rcases ch with rfl | rfl | rfl <;> decide
  · decide

lemma c18min5 {f: Nat -> Symbols9} (H: ThermoSudoku f): 5 ≤ f 18 := by
  cases h: f 18 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 H) 1 | exfalso
  · apply locked_set_in_region h H.b.row3 (c24c25c26triple H)

lemma c11 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 11 = 4 := by
  let h := (region_full_locked_set H.b.box1)
  locked_support_cases h 4
  · exfalso; apply digit_in_cell h (c0 H)
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 5
  · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 4
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (c18min5 H) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (c18min5 H) 3
  · exact h
  · exfalso; absurd (c18min5 H); rw [h]; decide
  · exfalso; apply digit_in_cell h (c19 H)
  · exfalso; apply digit_in_cell h (c20 H)

lemma c66c67pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {66,67} {1,3} := by
  -- naked pair
  apply locked_set_from_naked_set H.b.row8
  intro c ch
  cases h: f c
  · simp
  · exfalso; refine digit_in_region h H.b.row8 (c63 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · simp
  · exfalso; refine digit_in_region h H.b.row8 (c64 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.row8 (c68 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.row8 (c69 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.row8 (c65 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.row8 (c71 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.row8 (c70 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)

lemma c56 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 56 = 1 := by
  -- hidden single in col3
  let h := (region_full_locked_set H.b.col3)
  locked_support_cases h 1
  · exfalso; apply digit_in_region h H.b.box1 (c0 H)
  · exfalso; apply digit_in_region h H.b.box1 (c0 H)
  · exfalso; apply digit_in_region h H.b.box1 (c0 H)
  · exfalso; apply digit_in_region h H.b.box4 (c28 H)
  · exfalso; apply digit_in_region h H.b.box4 (c28 H)
  · exfalso; apply digit_in_region h H.b.box4 (c28 H)
  · exact h
  · exfalso; apply digit_in_cell h (c65 H)
  · exfalso; apply digit_in_cell h (c74 H)

lemma c54c72pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {54,72} {8,9} := by
  -- naked pair in box7
  apply locked_set_from_naked_set H.b.box7
  intro c ch
  cases h: f c
  · exfalso; refine digit_in_region h H.b.box7 (c56 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.box7 (c63 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.box7 (c55 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.box7 (c64 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.box7 (c73 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.box7 (c74 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · exfalso; refine digit_in_region h H.b.box7 (c65 H) (by contrapose ch; rw [ch]; decide)
      (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  · simp
  · simp

lemma c5c14_6 {f: Nat -> Symbols9} (H: ThermoSudoku f): SupportSet f {5, 14} 6 := by
  -- this is support set by maps to logic in cell 5
  -- complicated logic
  -- c5 is currently either a 3 or 6
  -- if it is a 3, the thermometer forces 2 into c4
  -- c14 is currently 2 3 or 6, it can only be 6
  cases h: f 5
  · exfalso; apply digit_less_than_thermo_min h H.thermo3 0 (by decide) bot_le 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo3 0 (by decide) bot_le 2
  · -- the complicated case
    have c4: f 4 = 2 := by
      apply ToNat.toNat_injective (fill_thermo H.thermo3 0 (by decide) bot_le 2 (by decide) h.le (by decide) 1)
    cases h1: f 14
    · exfalso; apply digit_less_than_thermo_min h1 H.thermo4 0 (by decide) bot_le 1
    · exfalso; apply digit_in_region h1 H.b.box2 c4
    · exfalso; apply digit_in_region h1 H.b.box2 h
    · exfalso; apply digit_in_region h1 H.b.col6 (c77 H)
    · exfalso; apply digit_in_region h1 H.b.col6 (c68 H)
    · exact in_support_set h1
    -- · exfalso; apply digit_greater_than_thermo_max H.thermo4 (c16max8 H) 1; simp at this; rw [h1] at this; contradiction
    · exfalso; apply digit_greater_than_thermo_max h1 H.thermo4 3 (by decide) (c16max8 H) 1
    · exfalso; apply digit_greater_than_thermo_max h1 H.thermo4 3 (by decide) (c16max8 H) 1
    · exfalso; apply digit_greater_than_thermo_max h1 H.thermo4 3 (by decide) (c16max8 H) 1
  · exfalso; apply digit_in_region h H.b.col6 (c77 H)
  · exfalso; apply digit_in_region h H.b.col6 (c68 H)
  · exact in_support_set h
  · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 H) 2
  · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 H) 2
  · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 H) 2

lemma c18 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 18 = 6 := by
  -- hidden single in row 3
  let h := (region_full_locked_set H.b.row3)
  locked_support_cases h 6
  · apply h
  · exfalso; apply digit_in_cell h (c19 H)
  · exfalso; apply digit_in_cell h (c20 H)
  · exfalso; apply support_set_in_region h H.b.box2 (c5c14_6 H)
  · exfalso; apply support_set_in_region h H.b.box2 (c5c14_6 H)
  · exfalso; apply support_set_in_region h H.b.box2 (c5c14_6 H)
  · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair H)
  · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair H)
  · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair H)


lemma c9 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 9 = 7 := by
  cases h: f 9
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 2
  · rfl
  · exfalso; apply locked_set_in_region h H.b.col1 (c54c72pair H)
  · exfalso; apply locked_set_in_region h H.b.col1 (c54c72pair H)

lemma c2 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 2 = 5 := by
  let h := (region_full_locked_set H.b.box1)
  locked_support_cases h 5
  · exfalso; apply digit_in_cell h (c0 H)
  · exfalso; apply digit_in_region h H.b.col2 (c73 H)
  · exact h
  · exfalso; apply digit_in_cell h (c9 H)
  · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) ((c18 H).symm.le) 3
  · exfalso; apply digit_in_cell h (c11 H)
  · exfalso; apply digit_in_cell h (c18 H)
  · exfalso; apply digit_in_cell h (c19 H)
  · exfalso; apply digit_in_cell h (c20 H)

lemma c1c10pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {1,10} {8,9} := by
  apply locked_set_from_naked_set H.b.box1
  intro c hc
  cases h: f c
  · exfalso; refine digit_in_region h H.b.box1 (c0 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.box1 (c19 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.box1 (c20 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.box1 (c11 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.box1 (c2 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.box1 (c18 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.box1 (c9 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · decide
  · decide

lemma c6 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 6 = 7 := by
  replace h := (c6c15pair H)
  locked_maps_cases h 6
  · exfalso; apply digit_in_region h H.b.row1 (c2 H)
  · exact h

lemma c15 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 15 = 5 := by
  apply locked_set_single
  simpa using locked_set_reducton (c6c15pair H) (c6 H)


lemma c7 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 7 = 8 := by
  replace h := (c7c16pair H)
  locked_maps_cases h 7
  · exfalso; apply digit_less_than_thermo_min h H.thermo3 3 (by decide) ((c6 H).symm.le) 4
  · exact h

lemma c16 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 16 = 6 := by
  apply locked_set_single
  simpa using locked_set_reducton (c7c16pair H) (c7 H)


lemma c5 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 5 = 6 := by
  replace h := (c5c14_6 H)
  support_cases h
  · exact h
  · exfalso; apply digit_in_region h H.b.row2 (c16 H)


lemma c1 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 1 = 9 := by
  replace h := (c1c10pair H)
  locked_maps_cases h 1
  · exfalso; apply digit_in_region h H.b.row1 (c7 H)
  · exact h

lemma c10 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 10 = 8 := by
  apply locked_set_single
  simpa using locked_set_reducton (c1c10pair H) (c1 H)


lemma c12 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 12 = 9 := by
  let h := (region_full_locked_set H.b.box2)
  locked_support_cases h 9
  · exfalso; apply digit_in_region h H.b.row1 (c1 H)
  · exfalso; apply digit_in_region h H.b.row1 (c1 H)
  · exfalso; apply digit_in_region h H.b.row1 (c1 H)
  · exact h
  · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) le_top 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) le_top 1
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)

lemma c13 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 13 = 1 := by
  let h := (region_full_locked_set H.b.box2)
  locked_support_cases h 1
  · exfalso; apply digit_in_region h H.b.row1 (c0 H)
  · exfalso; apply digit_in_region h H.b.row1 (c0 H)
  · exfalso; apply digit_in_region h H.b.row1 (c0 H)
  · exfalso; apply digit_in_cell h (c12 H)
  · exact h
  · exfalso; apply digit_less_than_thermo_min h H.thermo4 0 (by decide) bot_le 1
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)

lemma c67 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 67 = 3 := by
  replace h := (c66c67pair H)
  locked_maps_cases h 67
  · exfalso; apply digit_in_region h H.b.col5 (c13 H)
  · exact h

lemma c66 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 66 = 1 := by
  apply locked_set_single
  simpa using locked_set_reducton (c66c67pair H) (c67 H)


lemma c38c47pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {38,47} {8,9} := by
  apply locked_set_from_naked_set H.b.col3
  intro c hc
  cases h: f c
  · exfalso; refine digit_in_region h H.b.col3 (c56 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.col3 (c29 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.col3 (c20 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.col3 (c11 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.col3 (c2 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.col3 (c74 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · exfalso; refine digit_in_region h H.b.col3 (c65 H) ?_ ?_
    · contrapose hc; rw [hc]; decide
    · rcases hc with rfl | rfl <;> decide
  · decide
  · decide

lemma c47c51pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {47,51} {8,9} := by
  apply locked_set_from_naked_set H.b.row6
  intro c ch
  cases ch with
  | inl h => rw [h]; apply (c38c47pair H).mapsTo (by decide)
  | inr h =>
    rw [h]
    cases h: f 51
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) bot_le 3
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) bot_le 3
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) bot_le 3
    · exfalso; apply digit_in_region h H.b.col7 (c60 H)
    · exfalso; apply digit_in_region h H.b.col7 (c15 H)
    · exfalso; apply digit_in_region h H.b.col7 (c69 H)
    · exfalso; apply digit_in_region h H.b.col7 (c6 H)
    · decide
    · decide

lemma c58min2 {f: Nat -> Symbols9} (H: ThermoSudoku f): 2 ≤ f 58 := by
  cases h: f 58 <;> try decide
  · exfalso; apply digit_in_region h H.b.row7 (c56 H)

lemma c50 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 50 = 7 := by
  cases h: f 50
  · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58min2 H) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58min2 H) 2
  · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58min2 H) 2
  · exfalso; apply digit_in_region h H.b.col6 (c77 H)
  · exfalso; apply digit_in_region h H.b.col6 (c68 H)
  · exfalso; apply digit_in_region h H.b.col6 (c5 H)
  · rfl
  · exfalso; apply locked_set_in_region h H.b.row6 (c47c51pair H)
  · exfalso; apply locked_set_in_region h H.b.row6 (c47c51pair H)

lemma c46 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 46 = 6 := by
  cases h: f 46
  · exfalso; apply digit_in_region h H.b.col2 (c28 H)
  · exfalso; apply digit_in_region h H.b.col2 (c19 H)
  · exfalso; apply digit_in_region h H.b.col2 (c55 H)
  · exfalso; apply digit_in_region h H.b.col2 (c64 H)
  · exfalso; apply digit_in_region h H.b.col2 (c73 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.row6 (c50 H)
  · exfalso; apply digit_in_region h H.b.col2 (c10 H)
  · exfalso; apply digit_in_region h H.b.col2 (c1 H)

lemma c37 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 37 = 7 := by
  cases h: f 37
  · exfalso; apply digit_in_region h H.b.col2 (c28 H)
  · exfalso; apply digit_in_region h H.b.col2 (c19 H)
  · exfalso; apply digit_in_region h H.b.col2 (c55 H)
  · exfalso; apply digit_in_region h H.b.col2 (c64 H)
  · exfalso; apply digit_in_region h H.b.col2 (c73 H)
  · exfalso; apply digit_in_region h H.b.col2 (c46 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col2 (c10 H)
  · exfalso; apply digit_in_region h H.b.col2 (c1 H)


lemma c58 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 58 = 2 := by
  cases h: f 58
  · exfalso; apply digit_in_region h H.b.box8 (c66 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.box8 (c67 H)
  · exfalso; apply digit_in_region h H.b.box8 (c77 H)
  · exfalso; apply digit_in_region h H.b.box8 (c68 H)
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 0
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 0

lemma c4 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 4 = 4 := by
  cases h: f 4
  · exfalso; apply digit_in_region h H.b.row1 (c0 H)
  · exfalso; apply digit_in_region h H.b.col5 (c58 H)
  · exfalso; apply digit_in_region h H.b.col5 (c67 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.row1 (c2 H)
  · exfalso; apply digit_in_region h H.b.row1 (c5 H)
  · exfalso; apply digit_in_region h H.b.row1 (c6 H)
  · exfalso; apply digit_in_region h H.b.row1 (c7 H)
  · exfalso; apply digit_in_region h H.b.row1 (c1 H)

lemma c49 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 49 = 5 := by
  cases h: f 49
  · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58 H).symm.le 1
  · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58 H).symm.le 1
  · exfalso; apply digit_in_region h H.b.col5 (c67 H)
  · exfalso; apply digit_in_region h H.b.col5 (c4 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.row6 (c46 H)
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 1
  · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) (c50 H).le 1

lemma c23 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 23 = 8 := by
  cases h: f 23
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply digit_in_region h H.b.row3 (c19 H)
  · exfalso; apply digit_in_region h H.b.row3 (c20 H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply digit_in_region h H.b.col6 (c68 H)
  · exfalso; apply digit_in_region h H.b.row3 (c18 H)
  · exfalso; apply digit_in_region h H.b.col6 (c50 H)
  · rfl
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)

lemma c22 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 22 = 7 := by
  cases h: f 22
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply digit_in_region h H.b.row3 (c19 H)
  · exfalso; apply digit_in_region h H.b.row3 (c20 H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply digit_in_region h H.b.col5 (c49 H)
  · exfalso; apply digit_in_region h H.b.row3 (c18 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.row3 (c23 H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)

lemma c21 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 21 = 5 := by
  cases h: f 21
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · exfalso; apply digit_in_region h H.b.row3 (c19 H)
  · exfalso; apply digit_in_region h H.b.row3 (c20 H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)
  · rfl
  · exfalso; apply digit_in_region h H.b.row3 (c18 H)
  · exfalso; apply digit_in_region h H.b.row3 (c22 H)
  · exfalso; apply digit_in_region h H.b.row3 (c23 H)
  · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple H)

lemma c57 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 57 = 6 := by
  -- hidden single in box 8
  let h := (region_full_locked_set H.b.box8)
  locked_support_cases h 6
  · exact h
  · exfalso; apply digit_in_cell h (c58 H)
  · exfalso; apply digit_in_region h H.b.col6 (c5 H)
  · exfalso; apply digit_in_cell h (c66 H)
  · exfalso; apply digit_in_cell h (c67 H)
  · exfalso; apply digit_in_cell h (c68 H)
  · exfalso; apply digit_in_region h H.b.row9 (c74 H)
  · exfalso; apply digit_in_region h H.b.row9 (c74 H)
  · exfalso; apply digit_in_region h H.b.row9 (c74 H)

lemma c59 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 59 = 9 := by
  cases h: f 59
  · exfalso; apply digit_in_region h H.b.row7 (c56 H)
  · exfalso; apply digit_in_region h H.b.row7 (c58 H)
  · exfalso; apply digit_in_region h H.b.row7 (c55 H)
  · exfalso; apply digit_in_region h H.b.row7 (c60 H)
  · exfalso; apply digit_in_region h H.b.row7 (c61 H)
  · exfalso; apply digit_in_region h H.b.row7 (c57 H)
  · exfalso; apply digit_in_region h H.b.col6 (c50 H)
  · exfalso; apply digit_in_region h H.b.col6 (c23 H)
  · rfl

lemma c54 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 54 = 8 := by
  replace h := (c54c72pair H)
  locked_maps_cases h 54
  · exact h
  · exfalso; apply digit_in_region h H.b.row7 (c59 H)

lemma c72 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 72 = 9 := by
  apply locked_set_single
  simpa using locked_set_reducton (c54c72pair H) (c54 H)


lemma c75c76pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {75,76} {7,8} := by
  have this1: ({7, 8, 9} \ {9}: Set Symbols9) = {7, 8} := by
    ext x
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    apply Iff.intro
    · intro ⟨h1, h2⟩
      rcases h1 with rfl | rfl | rfl
      · left; rfl
      · right; rfl
      · contradiction
    · intro h
      rcases h with rfl | rfl
      · decide
      · decide
  simpa [this1] using locked_set_reducton (c72c75c76triple H) (c72 H)


lemma c76 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 76 = 8 := by
  replace h := (c75c76pair H)
  locked_maps_cases h 76
  · exfalso; apply digit_in_region h H.b.col5 (c22 H)
  · exact h

lemma c75 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 75 = 7 := by
  apply locked_set_single
  simpa using locked_set_reducton (c75c76pair H) (c76 H)


lemma c32 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 32 = 3 := by
  cases h: f 32
  · exfalso; apply digit_in_region h H.b.row4 (c28 H)
  · exfalso; apply digit_in_region h H.b.row4 (c29 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col6 (c77 H)
  · exfalso; apply digit_in_region h H.b.col6 (c68 H)
  · exfalso; apply digit_in_region h H.b.col6 (c5 H)
  · exfalso; apply digit_in_region h H.b.col6 (c50 H)
  · exfalso; apply digit_in_region h H.b.col6 (c23 H)
  · exfalso; apply digit_in_region h H.b.col6 (c59 H)

lemma c14 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 14 = 2 := by
  cases h: f 14
  · exfalso; apply digit_in_region h H.b.row2 (c13 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col6 (c32 H)
  · exfalso; apply digit_in_region h H.b.col6 (c77 H)
  · exfalso; apply digit_in_region h H.b.col6 (c68 H)
  · exfalso; apply digit_in_region h H.b.col6 (c5 H)
  · exfalso; apply digit_in_region h H.b.col6 (c50 H)
  · exfalso; apply digit_in_region h H.b.col6 (c23 H)
  · exfalso; apply digit_in_region h H.b.col6 (c59 H)

lemma c41 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 41 = 1 := by
  cases h: f 41
  · rfl
  · exfalso; apply digit_in_region h H.b.col6 (c14 H)
  · exfalso; apply digit_in_region h H.b.col6 (c32 H)
  · exfalso; apply digit_in_region h H.b.col6 (c77 H)
  · exfalso; apply digit_in_region h H.b.col6 (c68 H)
  · exfalso; apply digit_in_region h H.b.col6 (c5 H)
  · exfalso; apply digit_in_region h H.b.col6 (c50 H)
  · exfalso; apply digit_in_region h H.b.col6 (c23 H)
  · exfalso; apply digit_in_region h H.b.col6 (c59 H)

lemma c3 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 3 = 3 := by
  cases h: f 3
  · exfalso; apply digit_in_region h H.b.box2 (c13 H)
  · exfalso; apply digit_in_region h H.b.box2 (c14 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.box2 (c4 H)
  · exfalso; apply digit_in_region h H.b.box2 (c21 H)
  · exfalso; apply digit_in_region h H.b.box2 (c5 H)
  · exfalso; apply digit_in_region h H.b.box2 (c22 H)
  · exfalso; apply digit_in_region h H.b.box2 (c23 H)
  · exfalso; apply digit_in_region h H.b.box2 (c12 H)

lemma c8 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 8 = 2 := by
  replace h := (c8c17pair H)
  locked_maps_cases h 8
  · exact h
  · exfalso; apply digit_in_region h H.b.row1 (c3 H)

lemma c17 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 17 = 3 := by
  apply locked_set_single
  simpa using locked_set_reducton (c8c17pair H) (c8 H)


lemma c30min4 {f: Nat -> Symbols9} (H: ThermoSudoku f): 4 ≤ f 30 := by
  cases h: f 30 <;> try decide
  · exfalso; apply digit_in_region h H.b.row4 (c28 H)
  · exfalso; apply digit_in_region h H.b.row4 (c29 H)
  · exfalso; apply digit_in_region h H.b.col4 (c3 H)

lemma c39 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 39 = 8 := by
  cases h: f 39 <;> try exfalso; apply digit_less_than_thermo_min h H.thermo5 0 (by decide) (c30min4 H) 1
  · exfalso; apply digit_in_region h H.b.col4 (c21 H)
  · exfalso; apply digit_in_region h H.b.col4 (c57 H)
  · exfalso; apply digit_in_region h H.b.col4 (c75 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col4 (c12 H)

lemma c30 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 30 = 4 := by
  cases h: f 30
  · exfalso; apply digit_in_region h H.b.col4 (c66 H)
  · exfalso; apply digit_in_region h H.b.row4 (c29 H)
  · exfalso; apply digit_in_region h H.b.col4 (c3 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col4 (c21 H)
  · exfalso; apply digit_in_region h H.b.col4 (c57 H)
  · exfalso; apply digit_in_region h H.b.col4 (c75 H)
  · exfalso; apply digit_in_region h H.b.col4 (c39 H)
  · exfalso; apply digit_in_region h H.b.col4 (c12 H)

lemma c48 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 48 = 2 := by
  cases h: f 48
  · exfalso; apply digit_in_region h H.b.col4 (c66 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col4 (c3 H)
  · exfalso; apply digit_in_region h H.b.col4 (c30 H)
  · exfalso; apply digit_in_region h H.b.col4 (c21 H)
  · exfalso; apply digit_in_region h H.b.col4 (c57 H)
  · exfalso; apply digit_in_region h H.b.col4 (c75 H)
  · exfalso; apply digit_in_region h H.b.col4 (c39 H)
  · exfalso; apply digit_in_region h H.b.col4 (c12 H)

lemma c27 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 27 = 5 := by
  cases h: f 27 <;> try exfalso; apply digit_greater_than_thermo_max h H.thermo1 3 (by decide) (c10 H).le 0
  · exfalso; apply digit_in_region h H.b.row4 (c28 H)
  · exfalso; apply digit_in_region h H.b.row4 (c29 H)
  · exfalso; apply digit_in_region h H.b.row4 (c32 H)
  · exfalso; apply digit_in_region h H.b.row4 (c30 H)
  · rfl


lemma c33c51pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {33,51} {8,9} := by
  -- by min
  apply locked_set_from_naked_set (H.b.box6)
  intro c hc
  rcases hc with rfl | rfl
  · cases h: f 33
    · exfalso; apply digit_in_region h H.b.row4 (c28 H)
    · exfalso; apply digit_in_region h H.b.row4 (c29 H)
    · exfalso; apply digit_in_region h H.b.row4 (c32 H)
    · exfalso; apply digit_in_region h H.b.row4 (c30 H)
    · exfalso; apply digit_in_region h H.b.col7 (c15 H)
    · exfalso; apply digit_in_region h H.b.col7 (c69 H)
    · exfalso; apply digit_in_region h H.b.col7 (c6 H)
    · decide
    · decide
  · cases h: f 51 <;> try exfalso; apply digit_less_than_thermo_min h H.thermo7 2 (by decide) (c50 H).symm.le 3
    · decide
    · decide

lemma c24 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 24 = 1 := by
  cases h: f 24
  · rfl
  · exfalso; apply digit_in_region h H.b.box3 (c8 H)
  · exfalso; apply digit_in_region h H.b.col7 (c78 H)
  · exfalso; apply digit_in_region h H.b.col7 (c60 H)
  · exfalso; apply digit_in_region h H.b.col7 (c15 H)
  · exfalso; apply digit_in_region h H.b.col7 (c69 H)
  · exfalso; apply digit_in_region h H.b.col7 (c6 H)
  · exfalso; apply locked_set_in_region h H.b.col7 (c33c51pair H)
  · exfalso; apply locked_set_in_region h H.b.col7 (c33c51pair H)

lemma c25c26pair {f: Nat -> Symbols9} (H: ThermoSudoku f): LockedSet f {25,26} {4,9} := by
  simpa using locked_set_reducton (c24c25c26triple H) (c24 H)


lemma c25 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 25 = 4 := by
  replace h := (c25c26pair H)
  locked_maps_cases h 25
  · exact h
  · exfalso; apply digit_in_region h H.b.col8 (c70 H)

lemma c26 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 26 = 9 := by
  apply locked_set_single
  simpa using locked_set_reducton (c25c26pair H) (c25 H)


lemma c42 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 42 = 2 := by
  cases h: f 42
  · exfalso; apply digit_in_region h H.b.col7 (c24 H)
  · rfl
  · exfalso; exact digit_in_region h H.b.col7 (c78 H)
  · exfalso; exact digit_in_region h H.b.col7 (c60 H)
  · exfalso; exact digit_in_region h H.b.col7 (c15 H)
  · exfalso; exact digit_in_region h H.b.col7 (c69 H)
  · exfalso; exact digit_in_region h H.b.col7 (c6 H)
  · exfalso; exact locked_set_in_region h H.b.col7 (c33c51pair H)
  · exfalso; exact locked_set_in_region h H.b.col7 (c33c51pair H)

lemma c53 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 53 = 4 := by
  cases h: f 53
  · exfalso; exact digit_in_region h H.b.col9 (c80 H)
  · exfalso; exact digit_in_region h H.b.col9 (c8 H)
  · exfalso; exact digit_in_region h H.b.col9 (c17 H)
  · rfl
  · exfalso; exact digit_in_region h H.b.row6 (c49 H)
  · exfalso; exact digit_in_region h H.b.row6 (c46 H)
  · exfalso; exact digit_in_region h H.b.col9 (c62 H)
  · exfalso; exact digit_in_region h H.b.col9 (c71 H)
  · exfalso; exact digit_in_region h H.b.col9 (c26 H)

lemma c35 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 35 = 6 := by
  cases h: f 35
  · exfalso; exact digit_in_region h H.b.col9 (c80 H)
  · exfalso; exact digit_in_region h H.b.col9 (c8 H)
  · exfalso; exact digit_in_region h H.b.col9 (c17 H)
  · exfalso; exact digit_in_region h H.b.col9 (c53 H)
  · exfalso; exact digit_in_region h H.b.row4 (c27 H)
  · rfl
  · exfalso; exact digit_in_region h H.b.col9 (c62 H)
  · exfalso; exact digit_in_region h H.b.col9 (c71 H)
  · exfalso; exact digit_in_region h H.b.col9 (c26 H)

lemma c44 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 44 = 5 := by
  cases h: f 44
  · exfalso; apply digit_in_region h H.b.col9 (c80 H)
  · exfalso; apply digit_in_region h H.b.col9 (c8 H)
  · exfalso; apply digit_in_region h H.b.col9 (c17 H)
  · exfalso; apply digit_in_region h H.b.col9 (c53 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col9 (c35 H)
  · exfalso; apply digit_in_region h H.b.col9 (c62 H)
  · exfalso; apply digit_in_region h H.b.col9 (c71 H)
  · exfalso; apply digit_in_region h H.b.col9 (c26 H)

lemma c43 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 43 = 3 := by
  cases h: f 43
  · exfalso; apply digit_in_region h H.b.row5 (c41 H)
  · exfalso; apply digit_in_region h H.b.col8 (c79 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col8 (c25 H)
  · exfalso; apply digit_in_region h H.b.col8 (c61 H)
  · exfalso; apply digit_in_region h H.b.col8 (c16 H)
  · exfalso; apply digit_in_region h H.b.row5 (c37 H)
  · exfalso; apply digit_in_region h H.b.col8 (c7 H)
  · exfalso; apply digit_in_region h H.b.col8 (c70 H)

lemma c52 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 52 = 1 := by
  cases h: f 52
  · rfl
  · exfalso; apply digit_in_region h H.b.col8 (c79 H)
  · exfalso; apply digit_in_region h H.b.col8 (c43 H)
  · exfalso; apply digit_in_region h H.b.col8 (c25 H)
  · exfalso; apply digit_in_region h H.b.col8 (c61 H)
  · exfalso; apply digit_in_region h H.b.col8 (c16 H)
  · exfalso; apply digit_in_region h H.b.row6 (c50 H)
  · exfalso; apply digit_in_region h H.b.col8 (c7 H)
  · exfalso; apply digit_in_region h H.b.col8 (c70 H)

lemma c34 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 34 = 7 := by
  cases h: f 34
  · exfalso; apply digit_in_region h H.b.col8 (c52 H)
  · exfalso; apply digit_in_region h H.b.col8 (c79 H)
  · exfalso; apply digit_in_region h H.b.col8 (c43 H)
  · exfalso; apply digit_in_region h H.b.col8 (c25 H)
  · exfalso; apply digit_in_region h H.b.col8 (c61 H)
  · exfalso; apply digit_in_region h H.b.col8 (c16 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col8 (c7 H)
  · exfalso; apply digit_in_region h H.b.col8 (c70 H)

lemma c31 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 31 = 9 := by
  cases h: f 31
  · exfalso; apply digit_in_region h H.b.row4 (c28 H)
  · exfalso; apply digit_in_region h H.b.row4 (c29 H)
  · exfalso; apply digit_in_region h H.b.row4 (c32 H)
  · exfalso; apply digit_in_region h H.b.row4 (c30 H)
  · exfalso; apply digit_in_region h H.b.row4 (c27 H)
  · exfalso; apply digit_in_region h H.b.row4 (c35 H)
  · exfalso; apply digit_in_region h H.b.row4 (c34 H)
  · exfalso; apply digit_in_region h H.b.box5 (c39 H)
  · rfl

lemma c40 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 40 = 6 := by
  cases h: f 40
  · exfalso; apply digit_in_region h H.b.col5 (c13 H)
  · exfalso; apply digit_in_region h H.b.col5 (c58 H)
  · exfalso; apply digit_in_region h H.b.col5 (c67 H)
  · exfalso; apply digit_in_region h H.b.col5 (c4 H)
  · exfalso; apply digit_in_region h H.b.col5 (c49 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col5 (c22 H)
  · exfalso; apply digit_in_region h H.b.col5 (c76 H)
  · exfalso; apply digit_in_region h H.b.col5 (c31 H)

lemma c33 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 33 = 8 := by
  replace h := (c33c51pair H)
  locked_maps_cases h 33
  · assumption
  · exfalso; apply digit_in_region h H.b.row4 (c31 H)

lemma c51 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 51 = 9 := by
  apply locked_set_single
  simpa using locked_set_reducton (c33c51pair H) (c33 H)


lemma c47 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 47 = 8 := by
  apply locked_set_single
  simpa using locked_set_reducton (c47c51pair H) (c51 H)


lemma c38 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 38 = 9 := by
  apply locked_set_single
  simpa using locked_set_reducton (c38c47pair H) (c47 H)


lemma c36 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 36 = 4 := by
  cases h: f 36
  · exfalso; apply digit_in_region h H.b.col1 (c0 H)
  · exfalso; apply digit_in_region h H.b.col1 (c63 H)
  · exfalso; apply digit_in_region h H.b.row5 (c43 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col1 (c27 H)
  · exfalso; apply digit_in_region h H.b.col1 (c18 H)
  · exfalso; apply digit_in_region h H.b.col1 (c9 H)
  · exfalso; apply digit_in_region h H.b.col1 (c54 H)
  · exfalso; apply digit_in_region h H.b.col1 (c72 H)

lemma c45 {f: Nat -> Symbols9} (H: ThermoSudoku f): f 45 = 3 := by
  cases h: f 45
  · exfalso; apply digit_in_region h H.b.col1 (c0 H)
  · exfalso; apply digit_in_region h H.b.col1 (c63 H)
  · rfl
  · exfalso; apply digit_in_region h H.b.col1 (c36 H)
  · exfalso; apply digit_in_region h H.b.col1 (c27 H)
  · exfalso; apply digit_in_region h H.b.col1 (c18 H)
  · exfalso; apply digit_in_region h H.b.col1 (c9 H)
  · exfalso; apply digit_in_region h H.b.col1 (c54 H)
  · exfalso; apply digit_in_region h H.b.col1 (c72 H)


theorem SolveThermoSudoku {S : Set (Nat → Symbols9)} (H : ∀ f, f ∈ S ↔ ThermoSudoku f):
  ∃! (g: Nat -> Symbols9), g ∈ S := by
  let digits: Array Symbols9 :=
    #[1,9,5,3,4,6,7,8,2,
      7,8,4,9,1,2,5,6,3,
      6,2,3,5,7,8,1,4,9,
      5,1,2,4,9,3,8,7,6,
      4,7,9,8,6,1,2,3,5,
      3,6,8,2,5,7,9,1,4,
      8,3,1,6,2,9,4,5,7,
      2,4,7,1,3,5,6,9,8,
      9,5,6,7,8,4,3,2,1]
  -- asserts that you have the right number of cells in the array (used for later calculation)
  have len: digits.size = 81 := by decide
  -- this is the solution function
  let g : Nat → Symbols9 := fun x => digits[x]? |>.getD 1
  use g
  constructor
  · simp only
    apply (H g).mpr
    -- prove that g obeys all the constraints of the puzzle
    constructor
      -- regions are unique, by checking that the size of the mapped set is the same
    · constructor
      iterate 27 apply injOn_by_card; decide
    iterate 9 {constructor <;> decide}
    -- and outside the grid (this is required)
    intro n hn
    unfold g
    conv =>
      enter [1, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  -- prove that forall h in S, h = g
  intro h hh
  replace H := (H h).mp hh
  ext x
  -- if you have shown above that every cell has one fill, then fill in the proofs here
  by_cases xin: x < 81
  · interval_cases x
    · exact (c0 H)
    · exact (c1 H)
    · exact (c2 H)
    · exact (c3 H)
    · exact (c4 H)
    · exact (c5 H)
    · exact (c6 H)
    · exact (c7 H)
    · exact (c8 H)
    · exact (c9 H)
    · exact (c10 H)
    · exact (c11 H)
    · exact (c12 H)
    · exact (c13 H)
    · exact (c14 H)
    · exact (c15 H)
    · exact (c16 H)
    · exact (c17 H)
    · exact (c18 H)
    · exact (c19 H)
    · exact (c20 H)
    · exact (c21 H)
    · exact (c22 H)
    · exact (c23 H)
    · exact (c24 H)
    · exact (c25 H)
    · exact (c26 H)
    · exact (c27 H)
    · exact (c28 H)
    · exact (c29 H)
    · exact (c30 H)
    · exact (c31 H)
    · exact (c32 H)
    · exact (c33 H)
    · exact (c34 H)
    · exact (c35 H)
    · exact (c36 H)
    · exact (c37 H)
    · exact (c38 H)
    · exact (c39 H)
    · exact (c40 H)
    · exact (c41 H)
    · exact (c42 H)
    · exact (c43 H)
    · exact (c44 H)
    · exact (c45 H)
    · exact (c46 H)
    · exact (c47 H)
    · exact (c48 H)
    · exact (c49 H)
    · exact (c50 H)
    · exact (c51 H)
    · exact (c52 H)
    · exact (c53 H)
    · exact (c54 H)
    · exact (c55 H)
    · exact (c56 H)
    · exact (c57 H)
    · exact (c58 H)
    · exact (c59 H)
    · exact (c60 H)
    · exact (c61 H)
    · exact (c62 H)
    · exact (c63 H)
    · exact (c64 H)
    · exact (c65 H)
    · exact (c66 H)
    · exact (c67 H)
    · exact (c68 H)
    · exact (c69 H)
    · exact (c70 H)
    · exact (c71 H)
    · exact (c72 H)
    · exact (c73 H)
    · exact (c74 H)
    · exact (c75 H)
    · exact (c76 H)
    · exact (c77 H)
    · exact (c78 H)
    · exact (c79 H)
    · exact (c80 H)
  -- again need to show the outside the grid holds
  rw [H.outside_grid]
  · unfold g
    simp at xin
    conv =>
      enter [2, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  push_neg at xin
  apply xin
