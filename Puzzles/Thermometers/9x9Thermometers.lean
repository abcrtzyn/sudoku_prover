import SudokuLean.Basic
import SudokuLean.Symbols9
import SudokuLean.Thermometer
import SudokuLean.BaselineConstraints

set_option linter.style.whitespace false

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



  outside_grid: ∀ x, x ≥ 16 -> solution x = Symbols9.one

theorem SolveThermoSudoku {S : Set (Nat → Symbols9)} (H : ∀ f, f ∈ S ↔ ThermoSudoku f):
  ∃! (g: Nat -> Symbols9), g ∈ S := by
  -- there is a set of 8s and 9s in box 9 pointing in row 8
  have row8point8: ∀ f (hf: f ∈ S), SupportSet f {69,70,71} 8 := by
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 8)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 0; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 2; simp at this; rw [h] at this; contradiction
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 0; simp at this; rw [h] at this; contradiction
  have row8point9: ∀ f (hf: f ∈ S), SupportSet f {69,70} 9 := by
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 9)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 0; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 2; simp at this; rw [h] at this; contradiction
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 3; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 0; simp at this; rw [h] at this; contradiction
  -- hidden triple 789 in row 9. allows a hidden pointing pair 6
  have

  -- these
  have c74c77_6: ∀ f ∈ S, f 74 = 6 ∨ f 77 = 6 := by
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.row9 (by simp) 6
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    have c68max7: f 68 ≤ 7 := by
      cases h: f 68 <;> try decide
      · exfalso; exact PointingSet.in_region h H.b.row8 (row8point8 f hf)
      · exfalso; exact PointingSet.in_region h H.b.row8 (row8point9 f hf)
    have this1: [80, 79, 78, 77, 68] <:+: [80, 79, 78, 77, 68,69] := by decide
    let thermoA := sub_cont_thermo H.thermo9 this1
    split_disjunctive_9 h
    · exfalso; sorry
    · exfalso;
      have c65max7: f 65 ≤ 7 := by
        cases h: f 65 <;> try decide
        · exfalso; exact PointingSet.in_region h H.b.row8 (row8point8 f hf)
        · exfalso; exact PointingSet.in_region h H.b.row8 (row8point9 f hf)
      let this := thermometer_maxs H.thermo6 c65max7 2; simp at this; rw [h] at this; contradiction
    · left; assumption
    · exfalso; sorry
    · exfalso; sorry
    · right; assumption
    · exfalso; let this := thermometer_maxs thermoA c68max7 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs thermoA c68max7 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs thermoA c68max7 0; simp at this; rw [h] at this; contradiction
  have row8point7: ∀ f (hf: f ∈ S), PointingSet (((H f).mp hf).b.row8) {65,68} 7 := by
    intro f hf
    replace H := (H f).mp hf
    constructor
    · simp
    · simp
      cases c74c77_6
      ·






  _
  -- once every digit is solved, fill in the solution below, remove the underscore above
  --
  let digits: Array Symbols9 :=
    #[,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,
      ,,,,,,,,,]
  -- asserts that you have the right number of cells in the array (used for later calculation)
  have len: digits.size = 16 := by decide
  -- this is the solution function
  let g : Nat → Symbols4 := fun x => digits[x]? |>.getD 1
  use g
  constructor
  · simp only
    apply (H g).mpr
    -- prove that g obeys all the constraints of the puzzle
    constructor
    -- regions are unique, by checking that the size of the mapped set is the same
    iterate 12 apply injOn_by_card; decide
    -- givens, easy to check
    iterate 3 decide
    -- less thans
    iterate 5 decide
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
  by_cases xin: x < 16
  · interval_cases x
    · exact c0 h hh
    · exact c1 h hh
    · exact H.given2
    · exact c3 h hh
    · exact c4 h hh
    · exact c5 h hh
    · exact c6 h hh
    · exact c7 h hh
    · exact c8 h hh
    · exact c9 h hh
    · exact c10 h hh
    · exact H.given11
    · exact c12 h hh
    · exact H.given13
    · exact c14 h hh
    · exact c15 h hh
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


/-
Less than theorems
the smallest symbol is never allowed to be on the greater than side of an lt
similarly for the largest symbol

-/
