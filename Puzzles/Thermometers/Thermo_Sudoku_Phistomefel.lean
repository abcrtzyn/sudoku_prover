import SudokuLean.Basic
import SudokuLean.Symbols9
import SudokuLean.Thermometer
import SudokuLean.Tactics
import SudokuLean.BaselineConstraints

set_option linter.style.whitespace false
set_option linter.style.longLine false

-- if this is false, will freeze all the proofs under freeze tactic
def freeze_flag : Bool := true

syntax "freeze" tacticSeq : tactic

macro_rules
  | `(tactic| freeze $t:tacticSeq) =>
    if freeze_flag then
      -- The key is wrapping the sequence in a block tactic
      `(tactic| · $t)
    else
      `(tactic| sorry)


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

set_option maxHeartbeats 600000 in
-- because its a long proof, look at it
theorem SolveThermoSudoku {S : Set (Nat → Symbols9)} (H : ∀ f, f ∈ S ↔ ThermoSudoku f):
  ∃! (g: Nat -> Symbols9), g ∈ S := by
  have k : IsSound S [] := by intro c d h; cases h
  -- there is a set of 8s and 9s in box 9 pointing in row 8
  have row8point8: ∀ f ∈ S, SupportSet f {69,70,71} 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 8)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 2
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 0
  }
  have row8point9: ∀ f ∈ S, SupportSet f {69,70} 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 9)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 2
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 3
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 5 (by decide) le_top 0
  }
  have c65max7: ∀ f ∈ S, f 65 ≤ 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 65 <;> try decide
    · exfalso; exact SupportSet.in_region h H.b.row8 (row8point8 f hf)
    · exfalso; exact SupportSet.in_region h H.b.row8 (row8point9 f hf)
  }
  have c68max7: ∀ f ∈ S, f 68 ≤ 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 68 <;> try decide
    · exfalso; exact SupportSet.in_region h H.b.row8 (row8point8 f hf)
    · exfalso; exact SupportSet.in_region h H.b.row8 (row8point9 f hf)
  }
  -- hidden triple 789 in row 9. allows a hidden pointing pair 6
  have c72c75c76triple: ∀ f ∈ S, Set.BijOn f {72,75,76} {7,8,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_hidden_set (H.b.row9)
    intro d ds
    let region_bij := (region_full_set_bijective H.b.row9)
    let h := region_bij.surjOn (Set.mem_univ d)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 f hf) 2 (h3 := by {rcases ds with rfl | rfl | rfl <;> decide})
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 f hf) 3 (h3 := by {rcases ds with rfl | rfl | rfl <;> decide})
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 3 (h3 := by {rcases ds with rfl | rfl | rfl <;> decide})
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 2 (h3 := by {rcases ds with rfl | rfl | rfl <;> decide})
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 1 (h3 := by {rcases ds with rfl | rfl | rfl <;> decide})
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 0 (h3 := by {rcases ds with rfl | rfl | rfl <;> decide})
  }
  have row9point6: ∀ f ∈ S, SupportSet f {74, 77} 6 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.row9).surjOn (Set.mem_univ 6)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; exact locked_set_in_cell h (c72c75c76triple f hf)
    · exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) (c65max7 f hf) 2
    · exact ⟨_, by simp, h⟩
    · exfalso; exact locked_set_in_cell h (c72c75c76triple f hf)
    · exfalso; exact locked_set_in_cell h (c72c75c76triple f hf)
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 0
  }
  have row8point7: ∀ f (hf: f ∈ S), SupportSet f {65,68} 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (row9point6 f hf)
    simp only [SupportSet, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
      ↓existsAndEq, true_and] at h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq, true_and]
    cases h with
    | inl h =>
      left
      apply ToNat.toNat_injective (fill_thermo H.thermo6 3 (by decide) h.symm.le 4 (by decide) (c65max7 f hf) (by decide) 4)
    | inr h =>
      right
      apply ToNat.toNat_injective (fill_thermo H.thermo9 3 (by decide) h.symm.le 4 (by decide) (c68max7 f hf) (by decide) 4)
  }
  replace k := add_fact k 62 7 (by freeze {
    -- hidden single in box 9
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 7)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo8 4 (by decide) le_top 1
    · exact h
    · exfalso; apply SupportSet.in_region h H.b.row8 (row8point7 f hf)
    · exfalso; apply SupportSet.in_region h H.b.row8 (row8point7 f hf)
    · exfalso; apply SupportSet.in_region h H.b.row8 (row8point7 f hf)
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo9 4 (by decide) (c68max7 f hf) 0
  })
  replace k := add_fact k 71 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo8 2 (by decide) ((get_d k 62 7) f hf).symm.le 4 (by decide) le_top (by decide) 3)
  })
  replace k := add_fact k 70 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo8 2 (by decide) ((get_d k 62 7) f hf).symm.le 4 (by decide) le_top (by decide) 4)
  })
  replace k := add_fact k 69 6 (by freeze {
    -- naked single
    intro f hf
    replace H := (H f).mp hf
    cases h: f 69 <;> try exfalso; apply digit_less_than_thermo_min h H.thermo9 0 (by decide) bot_le 5
    · rfl
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 62 7) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 71 8) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 70 9) f hf)
  })
  -- fill thermo9
  replace k := add_fact k 80 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) ((get_d k 69 6) f hf).le (by decide) 0)
  })
  replace k := add_fact k 79 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) ((get_d k 69 6) f hf).le (by decide) 1)
  })
  replace k := add_fact k 78 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) ((get_d k 69 6) f hf).le (by decide) 2)
  })
  replace k := add_fact k 77 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) ((get_d k 69 6) f hf).le (by decide) 3)
  })
  replace k := add_fact k 68 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 0 (by decide) bot_le 5 (by decide) ((get_d k 69 6) f hf).le (by decide) 4)
  })
  have c73min5: ∀ f ∈ S, 5 ≤ f 73 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 73 <;> try decide
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 80 1) f hf)
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 79 2) f hf)
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 78 3) f hf)
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 77 4) f hf)
  }
  replace k := add_fact k 73 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo6 2 (by decide) (c73min5 f hf) 4 (by decide) (c65max7 f hf) (by decide) 2)
  })
  replace k := add_fact k 74 6 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo6 2 (by decide) (c73min5 f hf) 4 (by decide) (c65max7 f hf) (by decide) 3)
  })
  replace k := add_fact k 65 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo6 2 (by decide) (c73min5 f hf) 4 (by decide) (c65max7 f hf) (by decide) 4)
  })
  -- lets clean up some pencil marks
  clear row8point7 row8point8 row8point9 c65max7 c68max7 row9point6 c73min5
  have c60min4: ∀ f ∈ S, 4 ≤ f 60 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 60 <;> try decide
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 80 1) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 79 2) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 78 3) f hf)
  }
  have c61max5: ∀ f ∈ S, f 61 ≤ 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 61 <;> try decide
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 69 6) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 62 7) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 71 8) f hf)
    · exfalso; apply digit_in_region h H.b.box9 ((get_d k 70 9) f hf)
  }
  replace k := add_fact k 60 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo8 0 (by decide) (c60min4 f hf) 1 (by decide) (c61max5 f hf) (by decide) 0)
  })
  replace k := add_fact k 61 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo8 0 (by decide) (c60min4 f hf) 1 (by decide) (c61max5 f hf) (by decide) 1)
  })
  clear c60min4 c61max5
  have row3point1: ∀ f ∈ S, SupportSet f {24,25} 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.box3).surjOn (Set.mem_univ 1)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply bottom_is_only_first h H.thermo3
    · exfalso; apply bottom_is_only_first h H.thermo3
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 80 1) f hf)
    · exfalso; apply bottom_is_only_first h H.thermo4
    · exfalso; apply bottom_is_only_first h H.thermo4
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 80 1) f hf)
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 80 1) f hf)
  }
  replace k := add_fact k 0 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 1)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · assumption
    · exfalso; apply bottom_is_only_first h H.thermo2
    · exfalso; apply bottom_is_only_first h H.thermo2
    · exfalso; apply bottom_is_only_first h H.thermo1
    · exfalso; apply bottom_is_only_first h H.thermo1
    · exfalso; apply bottom_is_only_first h H.thermo2
    · exfalso; apply bottom_is_only_first h H.thermo1
    · exfalso; apply SupportSet.in_region h H.b.row3 (row3point1 f hf)
    · exfalso; apply bottom_is_only_first h H.thermo2
  })
  have c27min2: ∀ f ∈ S, 2 ≤ f 27 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 27 <;> try decide
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 0 1) f hf)
  }
  replace k := add_fact k 19 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 2)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h ((get_d k 0 1) f hf)
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 5
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 4
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min2 f hf) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min2 f hf) 3
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 3
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min2 f hf) 1
    · exact h
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 2
  })
  have c11max5: ∀ f ∈ S, f 11 ≤ 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 11 <;> first | decide | exfalso; apply digit_greater_than_thermo_max h H.thermo2 5 (by decide) le_top 3 | exfalso
    · exfalso; apply digit_in_region h H.b.col3 ((get_d k 74 6) f hf)
    · exfalso; apply digit_in_region h H.b.col3 ((get_d k 65 7) f hf)
  }
  replace k := add_fact k 28 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    -- set up upper bound of 2 for this cell
    cases h: f 28 <;> try exfalso; apply digit_greater_than_thermo_max h H.thermo2 3 (by decide) (c11max5 f hf) 0
    · rfl
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 19 2) f hf)
  })
  replace k := add_fact k 55 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    -- set up upper bound of 3 for this cell
    cases h: f 55 <;> try exfalso; apply digit_greater_than_thermo_max h H.thermo6 4 (by decide) ((get_d k 65 7) f hf).le 0
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 19 2) f hf)
    · rfl
  })
  replace k := add_fact k 64 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo6 0 (by decide) (((get_d k 55 3) f hf).symm.le) 4 (by decide) (((get_d k 65 7) f hf).le) (by decide) 1)
  })
  replace k := add_fact k 63 2 (by freeze {
    -- naked single
    intro f hf
    replace H := (H f).mp hf
    cases h: f 63
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 0 1) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.box7 ((get_d k 55 3) f hf)
    · exfalso; apply digit_in_region h H.b.box7 ((get_d k 64 4) f hf)
    · exfalso; apply digit_in_region h H.b.box7 ((get_d k 73 5) f hf)
    · exfalso; apply digit_in_region h H.b.box7 ((get_d k 74 6) f hf)
    · exfalso; apply digit_in_region h H.b.box7 ((get_d k 65 7) f hf)
    · exfalso; apply digit_in_region h H.b.row8 ((get_d k 71 8) f hf)
    · exfalso; apply digit_in_region h H.b.row8 ((get_d k 70 9) f hf)
  })
  have c27min3: ∀ f ∈ S, 3 ≤ f 27 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 27 <;> try decide
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 63 2) f hf)
  }
  clear c27min2
  replace k := add_fact k 20 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 3)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h ((get_d k 0 1) f hf)
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 5
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 4
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 f hf) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 f hf) 3
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 3
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 f hf) 1
    · exfalso; apply digit_in_cell h ((get_d k 19 2) f hf)
    · exact h
  })
  replace k := add_fact k 29 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo2 0 (by decide) (((get_d k 28 1) f hf).symm.le) 2 (by decide) (((get_d k 20 3) f hf).le) (by decide) 1 (by decide))
  })
  clear c11max5
  have c6min5: ∀ f ∈ S, 5 ≤ f 6 := by freeze {
    -- thermo3 min is 4, 4 in column
    intro f hf
    replace H := (H f).mp hf
    cases h: f 6 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo3 0 (by decide) bot_le 3 | exfalso
    · apply digit_in_region h H.b.col7 ((get_d k 60 4) f hf)
  }
  have c15min5: ∀ f ∈ S, 5 ≤ f 15 := by freeze {
    -- thermo4 min is 3, 3 and 4 in column
    intro f hf
    replace H := (H f).mp hf
    cases h: f 15 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo4 0 (by decide) bot_le 2 | exfalso
    · apply digit_in_region h H.b.col7 ((get_d k 78 3) f hf)
    · apply digit_in_region h H.b.col7 ((get_d k 60 4) f hf)
  }
  have c7max8: ∀ f ∈ S, f 7 ≤ 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 <;> first | decide | exfalso
    · apply digit_in_region h H.b.col8 ((get_d k 70 9) f hf)
  }
  have c16max8: ∀ f ∈ S, f 16 ≤ 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 16 <;> first | decide | exfalso
    · apply digit_in_region h H.b.col8 ((get_d k 70 9) f hf)
  }
  have c6c15pair: ∀ f ∈ S, Set.BijOn f {6,15} {5,7} := by freeze {
    -- by min max, and 6 in col
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box3)
    intro c h
    rcases h with rfl | rfl
    · cases h: f 6 <;> first | decide | absurd (c6min5 f hf); rw [h]; decide | exfalso
      · apply digit_in_region h H.b.col7 ((get_d k 69 6) f hf)
      · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 f hf) 3
      · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 f hf) 3
    · cases h: f 15 <;> first | decide | absurd (c15min5 f hf); rw [h]; decide | exfalso
      · apply digit_in_region h H.b.col7 ((get_d k 69 6) f hf)
      · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) (c16max8 f hf) 2
      · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) (c16max8 f hf) 2
  }
  have c7c16pair: ∀ f ∈ S, Set.BijOn f {7,16} {6,8} := by freeze {
    -- by min max, and 7 in box
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box3)
    intro c h
    rcases h with rfl | rfl
    · cases h: f 7 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo3 3 (by decide) (c6min5 f hf) 4 | exfalso
      · apply locked_set_in_region h H.b.box3 (c6c15pair f hf)
      · absurd (c7max8 f hf); rw [h]; decide
    · cases h: f 16 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo4 2 (by decide) (c15min5 f hf) 3 | exfalso
      · apply locked_set_in_region h H.b.box3 (c6c15pair f hf)
      · absurd (c16max8 f hf); rw [h]; decide
  }
  have c8c17pair: ∀ f ∈ S, Set.BijOn f {8,17} {2,3} := by freeze {
    -- hidden in box using thermo mins
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_hidden_set (H.b.box3)
    intro d this
    let region_bij := (region_full_set_bijective H.b.box3)
    rcases this with rfl | rfl
    · let h := region_bij.surjOn (Set.mem_univ 2)
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
        exists_eq_or_imp, ↓existsAndEq, true_and] at h
      split_disjunctive_9 h
      · exfalso; apply locked_set_in_cell h (c6c15pair f hf)
      · exfalso; apply locked_set_in_cell h (c7c16pair f hf)
      · exact ⟨_, by simp, h⟩
      · exfalso; apply locked_set_in_cell h (c6c15pair f hf)
      · exfalso; apply locked_set_in_cell h (c7c16pair f hf)
      · exact ⟨_, by simp, h⟩
      · exfalso; apply digit_in_region h H.b.row3 ((get_d k 19 2) f hf)
      · exfalso; apply digit_in_region h H.b.row3 ((get_d k 19 2) f hf)
      · exfalso; apply digit_in_region h H.b.row3 ((get_d k 19 2) f hf)
    · let h := region_bij.surjOn (Set.mem_univ 3)
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
        exists_eq_or_imp, ↓existsAndEq, true_and] at h
      split_disjunctive_9 h
      · exfalso; apply locked_set_in_cell h (c6c15pair f hf)
      · exfalso; apply locked_set_in_cell h (c7c16pair f hf)
      · exact ⟨_, by simp, h⟩
      · exfalso; apply locked_set_in_cell h (c6c15pair f hf)
      · exfalso; apply locked_set_in_cell h (c7c16pair f hf)
      · exact ⟨_, by simp, h⟩
      · exfalso; apply digit_in_region h H.b.row3 ((get_d k 20 3) f hf)
      · exfalso; apply digit_in_region h H.b.row3 ((get_d k 20 3) f hf)
      · exfalso; apply digit_in_region h H.b.row3 ((get_d k 20 3) f hf)
  }
  have c24c25c26triple: ∀ f ∈ S, Set.BijOn f {24,25,26} {1,4,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box3)
    intro c ch
    cases h: f c
    · decide
    · exfalso; refine locked_set_in_region h H.b.box3 (c8c17pair f hf) (by simp [Set.subset_def]) (by decide) ?_ ?_
      rcases ch with rfl | rfl | rfl <;> decide
      rcases ch with rfl | rfl | rfl <;> decide
    · exfalso; refine locked_set_in_region h H.b.box3 (c8c17pair f hf) (by simp [Set.subset_def]) (by decide) ?_ ?_
      rcases ch with rfl | rfl | rfl <;> decide
      rcases ch with rfl | rfl | rfl <;> decide
    · decide
    · exfalso; refine locked_set_in_region h H.b.box3 (c6c15pair f hf) (by simp [Set.subset_def]) (by decide) ?_ ?_
      rcases ch with rfl | rfl | rfl <;> decide
      rcases ch with rfl | rfl | rfl <;> decide
    · exfalso; refine locked_set_in_region h H.b.box3 (c7c16pair f hf) (by simp [Set.subset_def]) (by decide) ?_ ?_
      rcases ch with rfl | rfl | rfl <;> decide
      rcases ch with rfl | rfl | rfl <;> decide
    · exfalso; refine locked_set_in_region h H.b.box3 (c6c15pair f hf) (by simp [Set.subset_def]) (by decide) ?_ ?_
      rcases ch with rfl | rfl | rfl <;> decide
      rcases ch with rfl | rfl | rfl <;> decide
    · exfalso; refine locked_set_in_region h H.b.box3 (c7c16pair f hf) (by simp [Set.subset_def]) (by decide) ?_ ?_
      rcases ch with rfl | rfl | rfl <;> decide
      rcases ch with rfl | rfl | rfl <;> decide
    · decide
  }
  have c18min5: ∀ f ∈ S, 5 ≤ f 18 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 18 <;> first | decide | exfalso; apply digit_less_than_thermo_min h H.thermo1 0 (by decide) (c27min3 f hf) 1 | exfalso
    · apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  replace k := add_fact k 11 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 4)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h ((get_d k 0 1) f hf)
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 5
    · exfalso; apply digit_less_than_thermo_min h H.thermo2 0 (by decide) bot_le 4
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (c18min5 f hf) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (c18min5 f hf) 3
    · exact h
    · exfalso; absurd (c18min5 f hf); rw [h]; decide
    · exfalso; apply digit_in_cell h ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 20 3) f hf)
  })
  have c66c67pair: ∀ f ∈ S, Set.BijOn f {66,67} {1,3} := by freeze {
    -- naked pair
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.row8
    intro c ch
    cases h: f c
    · simp
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 63 2) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · simp
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 64 4) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 68 5) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 69 6) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 65 7) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 71 8) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 ((get_d k 70 9) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  }
  replace k := add_fact k 56 1 (by freeze {
    -- hidden single in col3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.col3).surjOn (Set.mem_univ 1)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.box1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.box1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.box1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.box4 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.box4 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.box4 ((get_d k 28 1) f hf)
    · exact h
    · exfalso; apply digit_in_cell h ((get_d k 65 7) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 74 6) f hf)
  })
  have c54c72pair: ∀ f ∈ S, Set.BijOn f {54,72} {8,9} := by freeze {
    -- naked pair in box7
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.box7
    intro c ch
    cases h: f c
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 56 1) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 63 2) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 55 3) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 64 4) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 73 5) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 74 6) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 ((get_d k 65 7) f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · simp
    · simp
  }
  have c5c14_6: ∀ f ∈ S, SupportSet f {5, 14} 6 := by freeze {
    -- complicated logic
    -- c5 is currently either a 3 or 6
    -- if it is a 3, the thermometer forces 2 into c4
    -- c14 is currently 2 3 or 6, it can only be 6
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
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
      · exfalso; apply digit_in_region h1 H.b.col6 ((get_d k 77 4) f hf)
      · exfalso; apply digit_in_region h1 H.b.col6 ((get_d k 68 5) f hf)
      · exact ⟨_, by simp, h1⟩
      -- · exfalso; apply digit_greater_than_thermo_max H.thermo4 (c16max8 f hf) 1; simp at this; rw [h1] at this; contradiction
      · exfalso; apply digit_greater_than_thermo_max h1 H.thermo4 3 (by decide) (c16max8 f hf) 1
      · exfalso; apply digit_greater_than_thermo_max h1 H.thermo4 3 (by decide) (c16max8 f hf) 1
      · exfalso; apply digit_greater_than_thermo_max h1 H.thermo4 3 (by decide) (c16max8 f hf) 1
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 77 4) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 68 5) f hf)
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 f hf) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 f hf) 2
    · exfalso; apply digit_greater_than_thermo_max h H.thermo3 4 (by decide) (c7max8 f hf) 2
  }
  replace k := add_fact k 18 6 (by freeze {
    -- hidden single in row 3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.row3).surjOn (Set.mem_univ 6)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · apply h
    · exfalso; apply digit_in_cell h ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 20 3) f hf)
    · exfalso; apply SupportSet.in_region h H.b.box2 (c5c14_6 f hf)
    · exfalso; apply SupportSet.in_region h H.b.box2 (c5c14_6 f hf)
    · exfalso; apply SupportSet.in_region h H.b.box2 (c5c14_6 f hf)
    · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair f hf)
    · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair f hf)
    · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair f hf)
  })
  clear c18min5
  replace k := add_fact k 9 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 9
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 2
    · rfl
    · exfalso; apply locked_set_in_region h H.b.col1 (c54c72pair f hf)
    · exfalso; apply locked_set_in_region h H.b.col1 (c54c72pair f hf)
  })
  replace k := add_fact k 2 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 5)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 73 5) f hf)
    · exact h
    · exfalso; apply digit_in_cell h ((get_d k 9 7) f hf)
    · exfalso; apply digit_less_than_thermo_min h H.thermo1 1 (by decide) (((get_d k 18 6) f hf).symm.le) 3
    · exfalso; apply digit_in_cell h ((get_d k 11 4) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 18 6) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 20 3) f hf)
  })
  have c1c10pair: ∀ f ∈ S, Set.BijOn f {1,10} {8,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.box1
    intro c hc
    cases h: f c
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 0 1) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 19 2) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 20 3) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 11 4) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 2 5) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 18 6) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 ((get_d k 9 7) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · decide
    · decide
  }
  replace k := add_fact k 6 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c6c15pair f hf).mapsTo (x := 6) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.row1 ((get_d k 2 5) f hf)
    | inr h => exact h
  })
  replace k := add_fact k 15 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c6c15pair f hf) ((get_d k 6 7) f hf)
  })
  clear c6c15pair
  replace k := add_fact k 7 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c7c16pair f hf).mapsTo (x := 7) (by simp)
    cases h with
    | inl h => exfalso; apply digit_less_than_thermo_min h H.thermo3 3 (by decide) (((get_d k 6 7) f hf).symm.le) 4
    | inr h => exact h
  })
  replace k := add_fact k 16 6 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c7c16pair f hf) ((get_d k 7 8) f hf)
  })
  clear c7c16pair
  replace k := add_fact k 5 6 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c5c14_6 f hf)
    simp only [SupportSet, Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp,
      ↓existsAndEq, true_and] at h
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.row2 ((get_d k 16 6) f hf)
  })
  clear c5c14_6
  replace k := add_fact k 1 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c1c10pair f hf).mapsTo (x := 1) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.row1 ((get_d k 7 8) f hf)
    | inr h => exact h
  })
  replace k := add_fact k 10 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c1c10pair f hf) ((get_d k 1 9) f hf)
  })
  clear c1c10pair
  replace k := add_fact k 12 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box2).surjOn (Set.mem_univ 9)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 1 9) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 1 9) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 1 9) f hf)
    · exact h
    · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) le_top 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo4 3 (by decide) le_top 1
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  })
  replace k := add_fact k 13 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box2).surjOn (Set.mem_univ 1)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 12 9) f hf)
    · exact h
    · exfalso; apply digit_less_than_thermo_min h H.thermo4 0 (by decide) bot_le 1
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  })
  replace k := add_fact k 67 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c66c67pair f hf).mapsTo (x := 67) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.col5 ((get_d k 13 1) f hf)
    | inr h => exact h
  })
  replace k := add_fact k 66 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c66c67pair f hf) ((get_d k 67 3) f hf)
  })
  clear c66c67pair
  have c38c47pair: ∀ f ∈ S, Set.BijOn f {38,47} {8,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.col3
    intro c hc
    cases h: f c
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 56 1) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 29 2) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 20 3) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 11 4) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 2 5) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 74 6) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 ((get_d k 65 7) f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · decide
    · decide
  }
  have c47c51pair: ∀ f ∈ S, Set.BijOn f {47,51} {8,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.row6
    intro c ch
    cases ch with
    | inl h => rw [h]; apply (c38c47pair f hf).mapsTo (by decide)
    | inr h =>
      rw [h]
      cases h: f 51
      · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) bot_le 3
      · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) bot_le 3
      · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) bot_le 3
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 60 4) f hf)
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 15 5) f hf)
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 69 6) f hf)
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 6 7) f hf)
      · decide
      · decide
  }
  have c58min2: ∀ f ∈ S, 2 ≤ f 58 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 58 <;> try decide
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 56 1) f hf)
  }
  replace k := add_fact k 50 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 50
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58min2 f hf) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58min2 f hf) 2
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) (c58min2 f hf) 2
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 77 4) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 68 5) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 5 6) f hf)
    · rfl
    · exfalso; apply locked_set_in_region h H.b.row6 (c47c51pair f hf)
    · exfalso; apply locked_set_in_region h H.b.row6 (c47c51pair f hf)
  })
  replace k := add_fact k 46 6 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 46
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 55 3) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 64 4) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 73 5) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row6 ((get_d k 50 7) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 10 8) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 1 9) f hf)
  })
  replace k := add_fact k 37 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 37
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 55 3) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 64 4) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 73 5) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 46 6) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 10 8) f hf)
    · exfalso; apply digit_in_region h H.b.col2 ((get_d k 1 9) f hf)
  })
  clear c27min3 c6min5 c15min5 c7max8 c16max8
  replace k := add_fact k 58 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 58
    · exfalso; apply digit_in_region h H.b.box8 ((get_d k 66 1) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.box8 ((get_d k 67 3) f hf)
    · exfalso; apply digit_in_region h H.b.box8 ((get_d k 77 4) f hf)
    · exfalso; apply digit_in_region h H.b.box8 ((get_d k 68 5) f hf)
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 0
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 0
  })
  replace k := add_fact k 4 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 4
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 58 2) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 67 3) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 2 5) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 5 6) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 6 7) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 7 8) f hf)
    · exfalso; apply digit_in_region h H.b.row1 ((get_d k 1 9) f hf)
  })
  replace k := add_fact k 49 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 49
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) ((get_d k 58 2) f hf).symm.le 1
    · exfalso; apply digit_less_than_thermo_min h H.thermo7 0 (by decide) ((get_d k 58 2) f hf).symm.le 1
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 67 3) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 4 4) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row6 ((get_d k 46 6) f hf)
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 1
    · exfalso; apply digit_greater_than_thermo_max h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).le 1
  })
  replace k := add_fact k 23 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 23
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 20 3) f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 68 5) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 18 6) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 50 7) f hf)
    · rfl
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  })
  replace k := add_fact k 22 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 22
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 20 3) f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 49 5) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 18 6) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 23 8) f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  })
  replace k := add_fact k 21 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 21
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 19 2) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 20 3) f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 18 6) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 22 7) f hf)
    · exfalso; apply digit_in_region h H.b.row3 ((get_d k 23 8) f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  })
  replace k := add_fact k 57 6 (by freeze {
    -- hidden single in box 8
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box8).surjOn (Set.mem_univ 6)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exact h
    · exfalso; apply digit_in_cell h ((get_d k 58 2) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 5 6) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 66 1) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 67 3) f hf)
    · exfalso; apply digit_in_cell h ((get_d k 68 5) f hf)
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 74 6) f hf)
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 74 6) f hf)
    · exfalso; apply digit_in_region h H.b.row9 ((get_d k 74 6) f hf)
  })
  replace k := add_fact k 59 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 59
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 56 1) f hf)
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 58 2) f hf)
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 55 3) f hf)
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 60 4) f hf)
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 61 5) f hf)
    · exfalso; apply digit_in_region h H.b.row7 ((get_d k 57 6) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 50 7) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 23 8 ) f hf)
    · rfl
  })
  replace k := add_fact k 54 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c54c72pair f hf).mapsTo (x := 54) (by simp)
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.row7 ((get_d k 59 9) f hf)
  })
  replace k := add_fact k 72 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c54c72pair f hf) ((get_d k 54 8) f hf)
  })
  clear c54c72pair
  have c75c76pair: ∀ f ∈ S, Set.BijOn f {75,76} {7,8} := by freeze {
    intro f hf
    replace H := (H f).mp hf
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
    simpa [this1] using locked_set_reducton (c72c75c76triple f hf) ((get_d k 72 9) f hf)
  }
  clear c72c75c76triple
  replace k := add_fact k 76 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c75c76pair f hf).mapsTo (x := 76) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.col5 ((get_d k 22 7 ) f hf)
    | inr h => exact h
  })
  replace k := add_fact k 75 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c75c76pair f hf) ((get_d k 76 8) f hf)
  })
  clear c75c76pair
  replace k := add_fact k 32 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 32
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 29 2) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 77 4) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 68 5) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 5 6) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 50 7) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 23 8 ) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 59 9) f hf)
  })
  replace k := add_fact k 14 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 14
    · exfalso; apply digit_in_region h H.b.row2 ((get_d k 13 1) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 32 3) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 77 4) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 68 5) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 5 6) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 50 7) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 23 8 ) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 59 9) f hf)
  })
  replace k := add_fact k 41 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 41
    · rfl
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 14 2) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 32 3) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 77 4) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 68 5) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 5 6) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 50 7) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 23 8 ) f hf)
    · exfalso; apply digit_in_region h H.b.col6 ((get_d k 59 9) f hf)
  })
  replace k := add_fact k 3 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 3
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 13 1) f hf)
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 14 2) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 4 4) f hf)
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 21 5) f hf)
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 5 6) f hf)
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 22 7 ) f hf)
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 23 8 ) f hf)
    · exfalso; apply digit_in_region h H.b.box2 ((get_d k 12 9) f hf)
  })
  replace k := add_fact k 8 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c8c17pair f hf).mapsTo (x := 8) (by simp)
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.row1 ((get_d k 3 3) f hf)
  })
  replace k := add_fact k 17 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c8c17pair f hf) ((get_d k 8 2) f hf)
  })
  clear c8c17pair
  have c30min4: ∀ f ∈ S, 4 ≤ f 30 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 30 <;> try decide
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 29 2) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 3 3) f hf)
  }
  replace k := add_fact k 39 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 39 <;> try exfalso; apply digit_less_than_thermo_min h H.thermo5 0 (by decide) (c30min4 f hf) 1
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 21 5) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 57 6) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 75 7) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 12 9) f hf)
  })
  replace k := add_fact k 30 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 30
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 66 1) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 29 2) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 3 3) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 21 5) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 57 6) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 75 7) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 39 8) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 12 9) f hf)
  })
  replace k := add_fact k 48 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 48
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 66 1) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 3 3) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 30 4) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 21 5) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 57 6) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 75 7) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 39 8) f hf)
    · exfalso; apply digit_in_region h H.b.col4 ((get_d k 12 9) f hf)
  })
  replace k := add_fact k 27 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 27 <;> try exfalso; apply digit_greater_than_thermo_max h H.thermo1 3 (by decide) ((get_d k 10 8) f hf).le 0
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 29 2) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 32 3) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 30 4) f hf)
    · rfl
  })
  clear c30min4 row3point1
  have c33c51pair: ∀ f ∈ S, Set.BijOn f {33,51} {8,9} := by freeze {
    -- by min
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box6)
    intro c hc
    rcases hc with rfl | rfl
    · cases h: f 33
      · exfalso; apply digit_in_region h H.b.row4 ((get_d k 28 1) f hf)
      · exfalso; apply digit_in_region h H.b.row4 ((get_d k 29 2) f hf)
      · exfalso; apply digit_in_region h H.b.row4 ((get_d k 32 3) f hf)
      · exfalso; apply digit_in_region h H.b.row4 ((get_d k 30 4) f hf)
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 15 5) f hf)
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 69 6) f hf)
      · exfalso; apply digit_in_region h H.b.col7 ((get_d k 6 7) f hf)
      · decide
      · decide
    · cases h: f 51 <;> try exfalso; apply digit_less_than_thermo_min h H.thermo7 2 (by decide) ((get_d k 50 7) f hf).symm.le 3
      · decide
      · decide
  }
  replace k := add_fact k 24 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 24
    · rfl
    · exfalso; apply digit_in_region h H.b.box3 ((get_d k 8 2) f hf)
    · exfalso; apply digit_in_region h H.b.col7 ((get_d k 78 3) f hf)
    · exfalso; apply digit_in_region h H.b.col7 ((get_d k 60 4) f hf)
    · exfalso; apply digit_in_region h H.b.col7 ((get_d k 15 5) f hf)
    · exfalso; apply digit_in_region h H.b.col7 ((get_d k 69 6) f hf)
    · exfalso; apply digit_in_region h H.b.col7 ((get_d k 6 7) f hf)
    · exfalso; apply locked_set_in_region h H.b.col7 (c33c51pair f hf)
    · exfalso; apply locked_set_in_region h H.b.col7 (c33c51pair f hf)
  })
  have c25c26pair: ∀ f ∈ S, Set.BijOn f {25,26} {4,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c24c25c26triple f hf) ((get_d k 24 1) f hf)
  }
  clear c24c25c26triple
  replace k := add_fact k 25 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c25c26pair f hf).mapsTo (x := 25) (by simp)
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.col8 ((get_d k 70 9) f hf)
  })
  replace k := add_fact k 26 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c25c26pair f hf) ((get_d k 25 4) f hf)
  })
  clear c25c26pair c58min2
  replace k := add_fact k 42 2 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 42
    · exfalso; apply digit_in_region h H.b.col7 ((get_d k 24 1) f hf)
    · rfl
    · exfalso; exact digit_in_region h H.b.col7 ((get_d k 78 3) f hf)
    · exfalso; exact digit_in_region h H.b.col7 ((get_d k 60 4) f hf)
    · exfalso; exact digit_in_region h H.b.col7 ((get_d k 15 5) f hf)
    · exfalso; exact digit_in_region h H.b.col7 ((get_d k 69 6) f hf)
    · exfalso; exact digit_in_region h H.b.col7 ((get_d k 6 7) f hf)
    · exfalso; exact locked_set_in_region h H.b.col7 (c33c51pair f hf)
    · exfalso; exact locked_set_in_region h H.b.col7 (c33c51pair f hf)
  })
  replace k := add_fact k 53 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 53
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 80 1) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 8 2) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 17 3) f hf)
    · rfl
    · exfalso; exact digit_in_region h H.b.row6 ((get_d k 49 5) f hf)
    · exfalso; exact digit_in_region h H.b.row6 ((get_d k 46 6) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 62 7) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 71 8) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 26 9) f hf)
  })
  replace k := add_fact k 35 6 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 35
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 80 1) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 8 2) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 17 3) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 53 4) f hf)
    · exfalso; exact digit_in_region h H.b.row4 ((get_d k 27 5) f hf)
    · rfl
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 62 7) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 71 8) f hf)
    · exfalso; exact digit_in_region h H.b.col9 ((get_d k 26 9) f hf)
  })
  replace k := add_fact k 44 5 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 44
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 80 1) f hf)
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 8 2) f hf)
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 17 3) f hf)
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 53 4) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 35 6) f hf)
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 62 7) f hf)
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 71 8) f hf)
    · exfalso; apply digit_in_region h H.b.col9 ((get_d k 26 9) f hf)
  })
  replace k := add_fact k 43 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 43
    · exfalso; apply digit_in_region h H.b.row5 ((get_d k 41 1) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 79 2) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 25 4) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 61 5) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 16 6) f hf)
    · exfalso; apply digit_in_region h H.b.row5 ((get_d k 37 7) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 7 8) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 70 9) f hf)
  })
  replace k := add_fact k 52 1 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 52
    · rfl
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 79 2) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 43 3) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 25 4) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 61 5) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 16 6) f hf)
    · exfalso; apply digit_in_region h H.b.row6 ((get_d k 50 7) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 7 8) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 70 9) f hf)
  })
  replace k := add_fact k 34 7 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 34
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 52 1) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 79 2) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 43 3) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 25 4) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 61 5) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 16 6) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 7 8) f hf)
    · exfalso; apply digit_in_region h H.b.col8 ((get_d k 70 9) f hf)
  })
  replace k := add_fact k 31 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 31
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 28 1) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 29 2) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 32 3) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 30 4) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 27 5) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 35 6) f hf)
    · exfalso; apply digit_in_region h H.b.row4 ((get_d k 34 7) f hf)
    · exfalso; apply digit_in_region h H.b.box5 ((get_d k 39 8) f hf)
    · rfl
  })
  replace k := add_fact k 40 6 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 40
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 13 1) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 58 2) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 67 3) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 4 4) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 49 5) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 22 7 ) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 76 8) f hf)
    · exfalso; apply digit_in_region h H.b.col5 ((get_d k 31 9) f hf)
  })
  replace k := add_fact k 33 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c33c51pair f hf).mapsTo (x := 33) (by simp)
    cases h with
    | inl h => assumption
    | inr h => exfalso; apply digit_in_region h H.b.row4 ((get_d k 31 9) f hf)
  })
  replace k := add_fact k 51 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c33c51pair f hf) ((get_d k 33 8) f hf)
  })
  clear c33c51pair
  replace k := add_fact k 47 8 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c47c51pair f hf) ((get_d k 51 9) f hf)
  })
  clear c47c51pair
  replace k := add_fact k 38 9 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c38c47pair f hf) ((get_d k 47 8) f hf)
  })
  clear c38c47pair
  replace k := add_fact k 36 4 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 36
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 63 2) f hf)
    · exfalso; apply digit_in_region h H.b.row5 ((get_d k 43 3) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 27 5) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 18 6) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 9 7) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 54 8) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 72 9) f hf)
  })
  replace k := add_fact k 45 3 (by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 45
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 0 1) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 63 2) f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 36 4) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 27 5) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 18 6) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 9 7) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 54 8) f hf)
    · exfalso; apply digit_in_region h H.b.col1 ((get_d k 72 9) f hf)
  })
  -- once every digit is solved, fill in the solution below, remove the underscore above
  --
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
    · exact (get_d k 0 1) h hh
    · exact (get_d k 1 9) h hh
    · exact (get_d k 2 5) h hh
    · exact (get_d k 3 3) h hh
    · exact (get_d k 4 4) h hh
    · exact (get_d k 5 6) h hh
    · exact (get_d k 6 7) h hh
    · exact (get_d k 7 8) h hh
    · exact (get_d k 8 2) h hh
    · exact (get_d k 9 7) h hh
    · exact (get_d k 10 8) h hh
    · exact (get_d k 11 4) h hh
    · exact (get_d k 12 9) h hh
    · exact (get_d k 13 1) h hh
    · exact (get_d k 14 2) h hh
    · exact (get_d k 15 5) h hh
    · exact (get_d k 16 6) h hh
    · exact (get_d k 17 3) h hh
    · exact (get_d k 18 6) h hh
    · exact (get_d k 19 2) h hh
    · exact (get_d k 20 3) h hh
    · exact (get_d k 21 5) h hh
    · exact (get_d k 22 7) h hh
    · exact (get_d k 23 8) h hh
    · exact (get_d k 24 1) h hh
    · exact (get_d k 25 4) h hh
    · exact (get_d k 26 9) h hh
    · exact (get_d k 27 5) h hh
    · exact (get_d k 28 1) h hh
    · exact (get_d k 29 2) h hh
    · exact (get_d k 30 4) h hh
    · exact (get_d k 31 9) h hh
    · exact (get_d k 32 3) h hh
    · exact (get_d k 33 8) h hh
    · exact (get_d k 34 7) h hh
    · exact (get_d k 35 6) h hh
    · exact (get_d k 36 4) h hh
    · exact (get_d k 37 7) h hh
    · exact (get_d k 38 9) h hh
    · exact (get_d k 39 8) h hh
    · exact (get_d k 40 6) h hh
    · exact (get_d k 41 1) h hh
    · exact (get_d k 42 2) h hh
    · exact (get_d k 43 3) h hh
    · exact (get_d k 44 5) h hh
    · exact (get_d k 45 3) h hh
    · exact (get_d k 46 6) h hh
    · exact (get_d k 47 8) h hh
    · exact (get_d k 48 2) h hh
    · exact (get_d k 49 5) h hh
    · exact (get_d k 50 7) h hh
    · exact (get_d k 51 9) h hh
    · exact (get_d k 52 1) h hh
    · exact (get_d k 53 4) h hh
    · exact (get_d k 54 8) h hh
    · exact (get_d k 55 3) h hh
    · exact (get_d k 56 1) h hh
    · exact (get_d k 57 6) h hh
    · exact (get_d k 58 2) h hh
    · exact (get_d k 59 9) h hh
    · exact (get_d k 60 4) h hh
    · exact (get_d k 61 5) h hh
    · exact (get_d k 62 7) h hh
    · exact (get_d k 63 2) h hh
    · exact (get_d k 64 4) h hh
    · exact (get_d k 65 7) h hh
    · exact (get_d k 66 1) h hh
    · exact (get_d k 67 3) h hh
    · exact (get_d k 68 5) h hh
    · exact (get_d k 69 6) h hh
    · exact (get_d k 70 9) h hh
    · exact (get_d k 71 8) h hh
    · exact (get_d k 72 9) h hh
    · exact (get_d k 73 5) h hh
    · exact (get_d k 74 6) h hh
    · exact (get_d k 75 7) h hh
    · exact (get_d k 76 8) h hh
    · exact (get_d k 77 4) h hh
    · exact (get_d k 78 3) h hh
    · exact (get_d k 79 2) h hh
    · exact (get_d k 80 1) h hh
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
