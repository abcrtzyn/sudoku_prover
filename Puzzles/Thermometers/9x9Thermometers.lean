import SudokuLean.Basic
import SudokuLean.Symbols9
import SudokuLean.Thermometer
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
  -- there is a set of 8s and 9s in box 9 pointing in row 8
  have row8point8: ∀ f ∈ S, SupportSet f {69,70,71} 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 8)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 0
      simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.add_one_sub_one, tsub_zero, h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 1
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, h, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.add_one_sub_one] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 2
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, h, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.add_one_sub_one] at this; contradiction
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 2
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, h, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.add_one_sub_one] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 1
      simp only [List.getElem_cons_succ, List.getElem_cons_zero, h, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, Nat.add_one_sub_one] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo9 le_top 0
      simp only [List.getElem_cons_zero, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd,
        Nat.add_one_sub_one, tsub_zero, h] at this; contradiction
  }
  have row8point9: ∀ f ∈ S, SupportSet f {69,70} 9 := by freeze {
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
  have thermoA: ∀ f ∈ S, Thermometer f [80, 79, 78, 77, 68] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [80, 79, 78, 77, 68] <:+: [80, 79, 78, 77, 68,69] := by decide
    exact sub_cont_thermo H.thermo9 this1
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
    · exfalso; let this := thermometer_maxs H.thermo6 (c65max7 f hf) 2; simp at this; rw [h] at this; rcases ds with rfl | rfl | rfl <;> contradiction
    · exfalso; let this := thermometer_maxs H.thermo6 (c65max7 f hf) 3; simp at this; rw [h] at this; rcases ds with rfl | rfl | rfl <;> contradiction
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 3; simp at this; rw [h] at this; rcases ds with rfl | rfl | rfl <;> contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 2; simp at this; rw [h] at this; rcases ds with rfl | rfl | rfl <;> contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 1; simp at this; rw [h] at this; rcases ds with rfl | rfl | rfl <;> contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 0; simp at this; rw [h] at this; rcases ds with rfl | rfl | rfl <;> contradiction
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
    · exfalso; let this := thermometer_maxs H.thermo6 (c65max7 f hf) 2; simp at this; rw [h] at this; contradiction
    · exact ⟨_, by simp, h⟩
    · exfalso; exact locked_set_in_cell h (c72c75c76triple f hf)
    · exfalso; exact locked_set_in_cell h (c72c75c76triple f hf)
    · exact ⟨_, by simp, h⟩
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 0; simp at this; rw [h] at this; contradiction
  }
  have row8point7: ∀ f (hf: f ∈ S), SupportSet f {65,68} 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    unfold SupportSet
    let h := (row9point6 f hf)
    simp [SupportSet] at h
    simp
    cases h with
    | inl h =>
      left
      have thermoA: Thermometer f [74,65] := by
        have this1: [74,65] <:+: [55,64,73,74,65] := by decide
        exact sub_cont_thermo H.thermo6 this1
      apply ToNat.toNat_injective (fill_thermo thermoA h.symm.le (c65max7 f hf) (by decide) 1 (by decide))
    | inr h =>
      right
      have thermoA: Thermometer f [77,68] := by
        have this1: [77,68] <:+: [80, 79, 78, 77, 68,69] := by decide
        exact sub_cont_thermo H.thermo9 this1
      apply ToNat.toNat_injective (fill_thermo thermoA h.symm.le (c68max7 f hf) (by decide) 1 (by decide))
  }
  have c62: ∀ f ∈ S, f 62 = 7 := by freeze {
    -- hidden single in box 9
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box9).surjOn (Set.mem_univ 7)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 0; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo8 le_top 1; simp at this; rw [h] at this; contradiction
    · exact h
    · exfalso; apply SupportSet.in_region h H.b.row8 (row8point7 f hf)
    · exfalso; apply SupportSet.in_region h H.b.row8 (row8point7 f hf)
    · exfalso; apply SupportSet.in_region h H.b.row8 (row8point7 f hf)
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs (thermoA f hf) (c68max7 f hf) 0; simp at this; rw [h] at this; contradiction
  }
  clear thermoA
  have thermoA: ∀ f ∈ S, Thermometer f [62,71,70] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [62,71,70] <:+: [60,61,62,71,70] := by decide
    exact sub_cont_thermo H.thermo8 this1
  }
  have c71: ∀ f ∈ S, f 71 = 8 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c62 f hf).symm.le le_top (by decide) 1 (by decide))
  }
  have c70: ∀ f ∈ S, f 70 = 9 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c62 f hf).symm.le le_top (by decide) 2 (by decide))
  }
  clear thermoA
  have c69: ∀ f ∈ S, f 69 = 6 := by freeze {
    -- naked single
    intro f hf
    replace H := (H f).mp hf
    let this := thermometer_mins H.thermo9 bot_le 5; simp at this
    cases h: (f 69)
    · rw [h] at this; simp at this; contradiction
    · rw [h] at this; simp at this; contradiction
    · rw [h] at this; simp at this; contradiction
    · rw [h] at this; simp at this; contradiction
    · rw [h] at this; simp at this; contradiction
    · rfl
    · exfalso; apply digit_in_region h H.b.box9 (c62 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c71 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c70 f hf)
  }
  -- fill thermo9
  have c80: ∀ f ∈ S, f 80 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 bot_le (c69 f hf).le (by decide) 0 (by decide))
  }
  have c79: ∀ f ∈ S, f 79 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 bot_le (c69 f hf).le (by decide) 1 (by decide))
  }
  have c78: ∀ f ∈ S, f 78 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 bot_le (c69 f hf).le (by decide) 2 (by decide))
  }
  have c77: ∀ f ∈ S, f 77 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 bot_le (c69 f hf).le (by decide) 3 (by decide))
  }
  have c68: ∀ f ∈ S, f 68 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo9 bot_le (c69 f hf).le (by decide) 4 (by decide))
  }
  have thermoA: ∀ f ∈ S, Thermometer f [73,74,65] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [73,74,65] <:+: [55,64,73,74,65] := by decide
    exact sub_cont_thermo H.thermo6 this1
  }
  have c73min5: ∀ f ∈ S, 5 ≤ f 73 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 73 <;> try decide
    · exfalso; apply digit_in_region h H.b.row9 (c80 f hf)
    · exfalso; apply digit_in_region h H.b.row9 (c79 f hf)
    · exfalso; apply digit_in_region h H.b.row9 (c78 f hf)
    · exfalso; apply digit_in_region h H.b.row9 (c77 f hf)
  }
  have c73: ∀ f ∈ S, f 73 = 5 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c73min5 f hf) (c65max7 f hf) (by decide) 0 (by decide))
  }
  have c74: ∀ f ∈ S, f 74 = 6 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c73min5 f hf) (c65max7 f hf) (by decide) 1 (by decide))
  }
  have c65: ∀ f ∈ S, f 65 = 7 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c73min5 f hf) (c65max7 f hf) (by decide) 2 (by decide))
  -- lets clean up some pencil marks
  }
  clear thermoA row8point7 row8point8 row8point9 c65max7 c68max7 row9point6 c73min5
  have thermoA: ∀ f ∈ S, Thermometer f [60,61] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [60,61] <:+: [60,61,62,71,70] := by decide
    exact sub_cont_thermo H.thermo8 this1
  }
  have c60min4: ∀ f ∈ S, 4 ≤ f 60 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 60 <;> try decide
    · exfalso; apply digit_in_region h H.b.box9 (c80 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c79 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c78 f hf)
  }
  have c61max5: ∀ f ∈ S, f 61 ≤ 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 61 <;> try decide
    · exfalso; apply digit_in_region h H.b.box9 (c69 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c62 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c71 f hf)
    · exfalso; apply digit_in_region h H.b.box9 (c70 f hf)
  }
  have c60: ∀ f ∈ S, f 60 = 4 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c60min4 f hf) (c61max5 f hf) (by decide) 0 (by decide))
  }
  have c61: ∀ f ∈ S, f 61 = 5 := by freeze {
    intro f hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf)
    (c60min4 f hf) (c61max5 f hf) (by decide) 1 (by decide))
  }
  clear thermoA c60min4 c61max5
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
    · exfalso; apply digit_in_region h H.b.col9 (c80 f hf)
    · exfalso; apply bottom_is_only_first h H.thermo4
    · exfalso; apply bottom_is_only_first h H.thermo4
    · exfalso; apply digit_in_region h H.b.col9 (c80 f hf)
    · exact ⟨_, by simp, h⟩
    · exact ⟨_, by simp, h⟩
    · exfalso; apply digit_in_region h H.b.col9 (c80 f hf)
  }
  have c0: ∀ f ∈ S, f 0 = 1 := by freeze {
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
  }
  have c27min2: ∀ f ∈ S, 2 ≤ f 27 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 27 <;> try decide
    · exfalso; apply digit_in_region h H.b.col1 (c0 f hf)
  }
  have c19: ∀ f ∈ S, f 19 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 2)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c0 f hf)
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 5; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 4; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo1 (c27min2 f hf) 2; simp [h] at this
    · exfalso; let this := thermometer_mins H.thermo1 (c27min2 f hf) 3; simp [h] at this
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 3; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo1 (c27min2 f hf) 1; simp [h] at this
    · exact h
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 2; simp [h] at this; contradiction
  }
  have thermoB: ∀ f ∈ S, Thermometer f [28,29,20,11] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [28,29,20,11] <:+: [28,29,20,11,2,1] := by decide
    exact sub_cont_thermo H.thermo2 this1
  }
  have c11max5: ∀ f ∈ S, f 11 ≤ 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let this := thermometer_maxs H.thermo2 le_top 3
    simp at this
    cases h: f 11 <;> rw [h] at this <;> try decide
    · exfalso; apply digit_in_region h H.b.col3 (c74 f hf)
    · exfalso; apply digit_in_region h H.b.col3 (c65 f hf)
    · absurd this; decide
    · absurd this; decide
  }
  have c28: ∀ f ∈ S, f 28 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    -- set up upper bound of 2 for this cell
    let this := thermometer_maxs (thermoB f hf) (c11max5 f hf) 0
    simp at this
    cases h: f 28 <;> try {absurd this; rw [h]; decide}
    · rfl
    · exfalso; apply digit_in_region h H.b.col2 (c19 f hf)
  }
  have c55: ∀ f ∈ S, f 55 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    -- set up upper bound of 3 for this cell
    let this := thermometer_maxs H.thermo6 (c65 f hf).le 0
    simp at this
    cases h: f 55 <;> try {absurd this; rw [h]; decide}
    · exfalso; apply digit_in_region h H.b.col2 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c19 f hf)
    · rfl
  }
  have c64: ∀ f ∈ S, f 64 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo H.thermo6 ((c55 f hf).symm.le) ((c65 f hf).le) (by decide) 1 (by decide))
  }
  have c63: ∀ f ∈ S, f 63 = 2 := by freeze {
    -- naked single
    intro f hf
    replace H := (H f).mp hf
    cases h: f 63
    · exfalso; apply digit_in_region h H.b.col1 (c0 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.box7 (c55 f hf)
    · exfalso; apply digit_in_region h H.b.box7 (c64 f hf)
    · exfalso; apply digit_in_region h H.b.box7 (c73 f hf)
    · exfalso; apply digit_in_region h H.b.box7 (c74 f hf)
    · exfalso; apply digit_in_region h H.b.box7 (c65 f hf)
    · exfalso; apply digit_in_region h H.b.row8 (c71 f hf)
    · exfalso; apply digit_in_region h H.b.row8 (c70 f hf)
  }
  have c27min3: ∀ f ∈ S, 3 ≤ f 27 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 27 <;> try decide
    · exfalso; apply digit_in_region h H.b.col1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c63 f hf)
  }
  clear c27min2
  have c20: ∀ f ∈ S, f 20 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 3)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c0 f hf)
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 5; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 4; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo1 (c27min3 f hf) 2; simp [h] at this
    · exfalso; let this := thermometer_mins H.thermo1 (c27min3 f hf) 3; simp [h] at this
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 3; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo1 (c27min3 f hf) 1; simp [h] at this
    · exfalso; apply digit_in_cell h (c19 f hf)
    · exact h
  }
  have thermoA: ∀ f ∈ S, Thermometer f [28,29,20] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [28,29,20] <:+: [28,29,20,11,2,1] := by decide
    exact sub_cont_thermo H.thermo2 this1
  }
  have c29: ∀ f ∈ S, f 29 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply ToNat.toNat_injective (fill_thermo (thermoA f hf) ((c28 f hf).symm.le) ((c20 f hf).le) (by decide) 1 (by decide))
  }
  clear thermoA thermoB c11max5
  have c6min5: ∀ f ∈ S, 5 ≤ f 6 := by freeze {
    -- thermo3 min is 4, 4 in column
    intro f hf
    replace H := (H f).mp hf
    let this := thermometer_mins H.thermo3 bot_le 3; simp at this
    cases h: f 6 <;> first | decide | absurd this; rw [h]; decide | exfalso
    · apply digit_in_region h H.b.col7 (c60 f hf)
  }
  have c15min5: ∀ f ∈ S, 5 ≤ f 15 := by freeze {
    -- thermo4 min is 3, 3 and 4 in column
    intro f hf
    replace H := (H f).mp hf
    let this := thermometer_mins H.thermo4 bot_le 2; simp at this
    cases h: f 15 <;> first | decide | absurd this; rw [h]; decide | exfalso
    · apply digit_in_region h H.b.col7 (c78 f hf)
    · apply digit_in_region h H.b.col7 (c60 f hf)
  }
  have c7max8: ∀ f ∈ S, f 7 ≤ 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 <;> first | decide | exfalso
    · apply digit_in_region h H.b.col8 (c70 f hf)
  }
  have c16max8: ∀ f ∈ S, f 16 ≤ 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 16 <;> first | decide | exfalso
    · apply digit_in_region h H.b.col8 (c70 f hf)
  }
  have c6c15pair: ∀ f ∈ S, Set.BijOn f {6,15} {5,7} := by freeze {
    -- by min max, and 6 in col
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box3)
    intro c h
    rcases h with rfl | rfl
    · let this := thermometer_maxs H.thermo3 (c7max8 f hf) 3
      simp at this
      cases h: f 6 <;> first | decide | absurd (c6min5 f hf); rw [h]; decide | exfalso
      · apply digit_in_region h H.b.col7 (c69 f hf)
      · absurd this; rw [h]; decide
      · absurd this; rw [h]; decide
    · let this := thermometer_maxs H.thermo4 (c16max8 f hf) 2
      simp at this
      cases h: f 15 <;> first | decide | absurd (c15min5 f hf); rw [h]; decide | exfalso
      · apply digit_in_region h H.b.col7 (c69 f hf)
      · absurd this; rw [h]; decide
      · absurd this; rw [h]; decide
  }
  have thermoA: ∀ f ∈ S, Thermometer f [6,7] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [6,7] <:+: [13,4,5,6,7] := by decide
    exact sub_cont_thermo H.thermo3 this1
  }
  have thermoB: ∀ f ∈ S, Thermometer f [15,16] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [15,16] <:+: [13,14,15,16] := by decide
    exact sub_cont_thermo H.thermo4 this1
  }
  have c7c16pair: ∀ f ∈ S, Set.BijOn f {7,16} {6,8} := by freeze {
    -- by min max, and 7 in box
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box3)
    intro c h
    rcases h with rfl | rfl
    · let this := thermometer_mins (thermoA f hf) (c6min5 f hf) 1
      simp at this
      cases h: f 7 <;> first | decide | absurd this; rw [h]; decide | exfalso
      · apply locked_set_in_region h H.b.box3 (c6c15pair f hf)
      · absurd (c7max8 f hf); rw [h]; decide
    · let this := thermometer_mins (thermoB f hf) (c15min5 f hf) 1
      simp at this
      cases h: f 16 <;> first | decide | absurd this; rw [h]; decide | exfalso
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
      · exfalso; apply digit_in_region h H.b.row3 (c19 f hf)
      · exfalso; apply digit_in_region h H.b.row3 (c19 f hf)
      · exfalso; apply digit_in_region h H.b.row3 (c19 f hf)
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
      · exfalso; apply digit_in_region h H.b.row3 (c20 f hf)
      · exfalso; apply digit_in_region h H.b.row3 (c20 f hf)
      · exfalso; apply digit_in_region h H.b.row3 (c20 f hf)
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
    let this := thermometer_mins H.thermo1 (c27min3 f hf) 1; simp at this
    cases h: f 18 <;> first | decide | absurd this; rw [h]; decide | exfalso
    · apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  have thermoC: ∀ f ∈ S, Thermometer f [18,9,10] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [18,9,10] <:+: [27,18,9,10] := by decide
    exact sub_cont_thermo H.thermo1 this1
  }
  have c11: ∀ f ∈ S, f 11 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 4)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c0 f hf)
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 5; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo2 bot_le 4; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) (c18min5 f hf) 1; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) (c18min5 f hf) 2; simp [h] at this; contradiction
    · exact h
    · exfalso; absurd (c18min5 f hf); rw [h]; decide
    · exfalso; apply digit_in_cell h (c19 f hf)
    · exfalso; apply digit_in_cell h (c20 f hf)
  }
  have c66c67pair: ∀ f ∈ S, Set.BijOn f {66,67} {1,3} := by freeze {
    -- naked pair
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.row8
    intro c ch
    cases h: f c
    · simp
    · exfalso; refine digit_in_region h H.b.row8 (c63 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · simp
    · exfalso; refine digit_in_region h H.b.row8 (c64 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 (c68 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 (c69 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 (c65 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 (c71 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.row8 (c70 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
  }
  have c56: ∀ f ∈ S, f 56 = 1 := by freeze {
    -- hidden single in col3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.col3).surjOn (Set.mem_univ 1)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.box1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.box1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.box1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.box4 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.box4 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.box4 (c28 f hf)
    · exact h
    · exfalso; apply digit_in_cell h (c65 f hf)
    · exfalso; apply digit_in_cell h (c74 f hf)
  }
  have c54c72pair: ∀ f ∈ S, Set.BijOn f {54,72} {8,9} := by freeze {
    -- naked pair in box7
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.box7
    intro c ch
    cases h: f c
    · exfalso; refine digit_in_region h H.b.box7 (c56 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 (c63 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 (c55 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 (c64 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 (c73 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 (c74 f hf) (by contrapose ch; rw [ch]; decide)
        (by cases ch <;> expose_names <;> rw [h_1] <;> decide)
    · exfalso; refine digit_in_region h H.b.box7 (c65 f hf) (by contrapose ch; rw [ch]; decide)
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
    · exfalso; let this := thermometer_mins H.thermo3 bot_le 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo3 bot_le 2; simp at this; rw [h] at this; contradiction
    · -- the complicated case
      have thermoD: Thermometer f [13,4,5] := by
        have this1: [13,4,5] <:+: [13,4,5,6,7] := by decide
        exact sub_cont_thermo H.thermo3 this1
      have c4: f 4 = 2 := by
        apply ToNat.toNat_injective
        simpa using fill_thermo thermoD bot_le h.le (by decide) 1
      cases h1: f 14
      · exfalso; let this := thermometer_mins H.thermo4 bot_le 1; simp at this; rw [h1] at this; contradiction
      · exfalso; apply digit_in_region h1 H.b.box2 c4
      · exfalso; apply digit_in_region h1 H.b.box2 h
      · exfalso; apply digit_in_region h1 H.b.col6 (c77 f hf)
      · exfalso; apply digit_in_region h1 H.b.col6 (c68 f hf)
      · exact ⟨_, by simp, h1⟩
      · exfalso; let this := thermometer_maxs H.thermo4 (c16max8 f hf) 1; simp at this; rw [h1] at this; contradiction
      · exfalso; let this := thermometer_maxs H.thermo4 (c16max8 f hf) 1; simp at this; rw [h1] at this; contradiction
      · exfalso; let this := thermometer_maxs H.thermo4 (c16max8 f hf) 1; simp at this; rw [h1] at this; contradiction
    · exfalso; apply digit_in_region h H.b.col6 (c77 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c68 f hf)
    · exact ⟨_, by simp, h⟩
    · exfalso; let this := thermometer_maxs H.thermo3 (c7max8 f hf) 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo3 (c7max8 f hf) 2; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo3 (c7max8 f hf) 2; simp at this; rw [h] at this; contradiction
  }
  have c18: ∀ f ∈ S, f 18 = 6 := by freeze {
    -- hidden single in row 3
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.row3).surjOn (Set.mem_univ 6)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · apply h
    · exfalso; apply digit_in_cell h (c19 f hf)
    · exfalso; apply digit_in_cell h (c20 f hf)
    · exfalso; apply SupportSet.in_region h H.b.box2 (c5c14_6 f hf)
    · exfalso; apply SupportSet.in_region h H.b.box2 (c5c14_6 f hf)
    · exfalso; apply SupportSet.in_region h H.b.box2 (c5c14_6 f hf)
    · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair f hf)
    · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair f hf)
    · exfalso; apply locked_set_in_region h H.b.box3 (c7c16pair f hf)
  }
  clear c18min5
  have c9: ∀ f ∈ S, f 9 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 9
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 1; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 1; simp at this; rw [h] at this; contradiction
    · rfl
    · exfalso; apply locked_set_in_region h H.b.col1 (c54c72pair f hf)
    · exfalso; apply locked_set_in_region h H.b.col1 (c54c72pair f hf)
  }
  have c2: ∀ f ∈ S, f 2 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box1).surjOn (Set.mem_univ 5)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c0 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c73 f hf)
    · exact h
    · exfalso; apply digit_in_cell h (c9 f hf)
    · exfalso; let this := thermometer_mins (thermoC f hf) ((c18 f hf).symm.le) 2; simp at this; rw [h] at this; contradiction
    · exfalso; apply digit_in_cell h (c11 f hf)
    · exfalso; apply digit_in_cell h (c18 f hf)
    · exfalso; apply digit_in_cell h (c19 f hf)
    · exfalso; apply digit_in_cell h (c20 f hf)
  }
  have c1c10pair: ∀ f ∈ S, Set.BijOn f {1,10} {8,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.box1
    intro c hc
    cases h: f c
    · exfalso; refine digit_in_region h H.b.box1 (c0 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 (c19 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 (c20 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 (c11 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 (c2 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 (c18 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.box1 (c9 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · decide
    · decide
  }
  have c6: ∀ f ∈ S, f 6 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c6c15pair f hf).mapsTo (x := 6) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.row1 (c2 f hf)
    | inr h => exact h
  }
  have c15: ∀ f ∈ S, f 15 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c6c15pair f hf) (c6 f hf)
  }
  clear c6c15pair
  have c7: ∀ f ∈ S, f 7 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c7c16pair f hf).mapsTo (x := 7) (by simp)
    cases h with
    | inl h => exfalso; let this := thermometer_mins (thermoA f hf) (c6 f hf).symm.le 1; simp at this; rw [h] at this; contradiction
    | inr h => exact h
  }
  have c16: ∀ f ∈ S, f 16 = 6 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c7c16pair f hf) (c7 f hf)
  }
  clear c7c16pair
  have c5: ∀ f ∈ S, f 5 = 6 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c5c14_6 f hf)
    simp [SupportSet] at h
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.row2 (c16 f hf)
  }
  clear c5c14_6
  have c1: ∀ f ∈ S, f 1 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c1c10pair f hf).mapsTo (x := 1) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.row1 (c7 f hf)
    | inr h => exact h
  }
  have c10: ∀ f ∈ S, f 10 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c1c10pair f hf) (c1 f hf)
  }
  clear c1c10pair
  have c12: ∀ f ∈ S, f 12 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box2).surjOn (Set.mem_univ 9)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.row1 (c1 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c1 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c1 f hf)
    · exact h
    · exfalso; let this := thermometer_maxs H.thermo4 le_top 0; simp at this; rw [h] at this; contradiction
    · exfalso; let this := thermometer_maxs H.thermo4 le_top 1; simp at this; rw [h] at this; contradiction
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  have c13: ∀ f ∈ S, f 13 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box2).surjOn (Set.mem_univ 1)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.row1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c0 f hf)
    · exfalso; apply digit_in_cell h (c12 f hf)
    · exact h
    · exfalso; let this := thermometer_mins H.thermo4 bot_le 1; simp [h] at this; contradiction
    · exfalso; exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  have c67: ∀ f ∈ S, f 67 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c66c67pair f hf).mapsTo (x := 67) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.col5 (c13 f hf)
    | inr h => exact h
  }
  have c66: ∀ f ∈ S, f 66 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c66c67pair f hf) (c67 f hf)
  }
  clear c66c67pair
  have c38c47pair: ∀ f ∈ S, Set.BijOn f {38,47} {8,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set H.b.col3
    intro c hc
    cases h: f c
    · exfalso; refine digit_in_region h H.b.col3 (c56 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 (c29 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 (c20 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 (c11 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 (c2 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 (c74 f hf) ?_ ?_
      · contrapose hc; rw [hc]; decide
      · rcases hc with rfl | rfl <;> decide
    · exfalso; refine digit_in_region h H.b.col3 (c65 f hf) ?_ ?_
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
      let this := thermometer_mins H.thermo7 bot_le 3
      simp at this
      rw [h]
      cases h: f 51 <;> rw [h] at this <;> try contradiction
      · exfalso; apply digit_in_region h H.b.col7 (c60 f hf)
      · exfalso; apply digit_in_region h H.b.col7 (c15 f hf)
      · exfalso; apply digit_in_region h H.b.col7 (c69 f hf)
      · exfalso; apply digit_in_region h H.b.col7 (c6 f hf)
      · decide
      · decide
  }
  have c58min2: ∀ f ∈ S, 2 ≤ f 58 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 58 <;> try decide
    · exfalso; apply digit_in_region h H.b.row7 (c56 f hf)
  }
  have c50: ∀ f ∈ S, f 50 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 50
    · exfalso; let this := thermometer_mins H.thermo7 (c58min2 f hf) 2; simp [h] at this; contradiction
    · exfalso; let this := thermometer_mins H.thermo7 (c58min2 f hf) 2; simp [h] at this
    · exfalso; let this := thermometer_mins H.thermo7 (c58min2 f hf) 2; simp [h] at this; contradiction
    · exfalso; apply digit_in_region h H.b.col6 (c77 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c68 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c5 f hf)
    · rfl
    · exfalso; apply locked_set_in_region h H.b.row6 (c47c51pair f hf)
    · exfalso; apply locked_set_in_region h H.b.row6 (c47c51pair f hf)
  }
  have c46: ∀ f ∈ S, f 46 = 6 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 46
    · exfalso; apply digit_in_region h H.b.col2 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c19 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c55 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c64 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c73 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row6 (c50 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c10 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c1 f hf)
  }
  have c37: ∀ f ∈ S, f 37 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 37
    · exfalso; apply digit_in_region h H.b.col2 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c19 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c55 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c64 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c73 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c46 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col2 (c10 f hf)
    · exfalso; apply digit_in_region h H.b.col2 (c1 f hf)
  }
  clear thermoC c27min3 c6min5 c15min5 c7max8 c16max8 thermoA thermoB
  have thermoA: ∀ f ∈ S, Thermometer f [58,49,50] := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: [58,49,50] <:+: [58,49,50,51] := by decide
    exact sub_cont_thermo H.thermo7 this1
  }
  have c58: ∀ f ∈ S, f 58 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let this := thermometer_maxs (thermoA f hf) (c50 f hf).le 0
    simp at this
    cases h: f 58
    · exfalso; apply digit_in_region h H.b.box8 (c66 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.box8 (c67 f hf)
    · exfalso; apply digit_in_region h H.b.box8 (c77 f hf)
    · exfalso; apply digit_in_region h H.b.box8 (c68 f hf)
    · exfalso; rw [h] at this; contradiction
    · exfalso; rw [h] at this; contradiction
    · exfalso; rw [h] at this; contradiction
    · exfalso; rw [h] at this; contradiction
  }
  have c4: ∀ f ∈ S, f 4 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 4
    · exfalso; apply digit_in_region h H.b.row1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c58 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c67 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row1 (c2 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c5 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c6 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c7 f hf)
    · exfalso; apply digit_in_region h H.b.row1 (c1 f hf)
  }
  have c49: ∀ f ∈ S, f 49 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    let this1 := thermometer_mins (thermoA f hf) (c58 f hf).symm.le 1
    let this2 := thermometer_maxs (thermoA f hf) (c50 f hf).le 1
    simp at this1
    simp at this2
    cases h: f 49
    · exfalso; rw [h] at this1; contradiction
    · exfalso; rw [h] at this1; contradiction
    · exfalso; apply digit_in_region h H.b.col5 (c67 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c4 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row6 (c46 f hf)
    · exfalso; rw [h] at this2; contradiction
    · exfalso; rw [h] at this2; contradiction
    · exfalso; rw [h] at this2; contradiction
  }
  have c23: ∀ f ∈ S, f 23 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 23
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c19 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c20 f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c68 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c18 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c50 f hf)
    · rfl
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  have c22: ∀ f ∈ S, f 22 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 22
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c19 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c20 f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c49 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c18 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row3 (c23 f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  have c21: ∀ f ∈ S, f 21 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 21
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c19 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c20 f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.row3 (c18 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c22 f hf)
    · exfalso; apply digit_in_region h H.b.row3 (c23 f hf)
    · exfalso; apply locked_set_in_region h H.b.row3 (c24c25c26triple f hf)
  }
  have c57: ∀ f ∈ S, f 57 = 6 := by freeze {
    -- hidden single in box 8
    intro f hf
    replace H := (H f).mp hf
    let h := (region_full_set_bijective H.b.box8).surjOn (Set.mem_univ 6)
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff,
      exists_eq_or_imp, ↓existsAndEq, true_and] at h
    split_disjunctive_9 h
    · exact h
    · exfalso; apply digit_in_cell h (c58 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c5 f hf)
    · exfalso; apply digit_in_cell h (c66 f hf)
    · exfalso; apply digit_in_cell h (c67 f hf)
    · exfalso; apply digit_in_cell h (c68 f hf)
    · exfalso; apply digit_in_region h H.b.row9 (c74 f hf)
    · exfalso; apply digit_in_region h H.b.row9 (c74 f hf)
    · exfalso; apply digit_in_region h H.b.row9 (c74 f hf)
  }
  have c59: ∀ f ∈ S, f 59 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 59
    · exfalso; apply digit_in_region h H.b.row7 (c56 f hf)
    · exfalso; apply digit_in_region h H.b.row7 (c58 f hf)
    · exfalso; apply digit_in_region h H.b.row7 (c55 f hf)
    · exfalso; apply digit_in_region h H.b.row7 (c60 f hf)
    · exfalso; apply digit_in_region h H.b.row7 (c61 f hf)
    · exfalso; apply digit_in_region h H.b.row7 (c57 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c50 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c23 f hf)
    · rfl
  }
  have c54: ∀ f ∈ S, f 54 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c54c72pair f hf).mapsTo (x := 54) (by simp)
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.row7 (c59 f hf)
  }
  have c72: ∀ f ∈ S, f 72 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c54c72pair f hf) (c54 f hf)
  }
  clear c54c72pair
  have c75c76pair: ∀ f ∈ S, Set.BijOn f {75,76} {7,8} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    have this1: ({7, 8, 9} \ {9}: Set Symbols9) = {7, 8} := by
      ext x
      simp
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
    simpa [this1] using locked_set_reducton (c72c75c76triple f hf) (c72 f hf)
  }
  clear c72c75c76triple
  have c76: ∀ f ∈ S, f 76 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c75c76pair f hf).mapsTo (x := 76) (by simp)
    cases h with
    | inl h => exfalso; apply digit_in_region h H.b.col5 (c22 f hf)
    | inr h => exact h
  }
  have c75: ∀ f ∈ S, f 75 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c75c76pair f hf) (c76 f hf)
  }
  clear c75c76pair
  have c32: ∀ f ∈ S, f 32 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 32
    · exfalso; apply digit_in_region h H.b.row4 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c29 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col6 (c77 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c68 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c5 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c50 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c23 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c59 f hf)
  }
  have c14: ∀ f ∈ S, f 14 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 14
    · exfalso; apply digit_in_region h H.b.row2 (c13 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col6 (c32 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c77 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c68 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c5 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c50 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c23 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c59 f hf)
  }
  have c41: ∀ f ∈ S, f 41 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 41
    · rfl
    · exfalso; apply digit_in_region h H.b.col6 (c14 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c32 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c77 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c68 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c5 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c50 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c23 f hf)
    · exfalso; apply digit_in_region h H.b.col6 (c59 f hf)
  }
  have c3: ∀ f ∈ S, f 3 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 3
    · exfalso; apply digit_in_region h H.b.box2 (c13 f hf)
    · exfalso; apply digit_in_region h H.b.box2 (c14 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.box2 (c4 f hf)
    · exfalso; apply digit_in_region h H.b.box2 (c21 f hf)
    · exfalso; apply digit_in_region h H.b.box2 (c5 f hf)
    · exfalso; apply digit_in_region h H.b.box2 (c22 f hf)
    · exfalso; apply digit_in_region h H.b.box2 (c23 f hf)
    · exfalso; apply digit_in_region h H.b.box2 (c12 f hf)
  }
  have c8: ∀ f ∈ S, f 8 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c8c17pair f hf).mapsTo (x := 8) (by simp)
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.row1 (c3 f hf)
  }
  have c17: ∀ f ∈ S, f 17 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c8c17pair f hf) (c8 f hf)
  }
  clear c8c17pair
  have c30min4: ∀ f ∈ S, 4 ≤ f 30 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 30 <;> try decide
    · exfalso; apply digit_in_region h H.b.row4 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c29 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c3 f hf)
  }
  have c39: ∀ f ∈ S, f 39 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 39 <;> try {
      exfalso; let this := thermometer_mins H.thermo5 (c30min4 f hf) 1; simp [h] at this; try contradiction
    }
    · exfalso; apply digit_in_region h H.b.col4 (c21 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c57 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c75 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col4 (c12 f hf)
  }
  have c30: ∀ f ∈ S, f 30 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 30
    · exfalso; apply digit_in_region h H.b.col4 (c66 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c29 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c3 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col4 (c21 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c57 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c75 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c39 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c12 f hf)
  }
  have c48: ∀ f ∈ S, f 48 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 48
    · exfalso; apply digit_in_region h H.b.col4 (c66 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col4 (c3 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c30 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c21 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c57 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c75 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c39 f hf)
    · exfalso; apply digit_in_region h H.b.col4 (c12 f hf)
  }
  have c27: ∀ f ∈ S, f 27 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf

    cases h: f 27 <;> try {
      exfalso; let this := thermometer_maxs H.thermo1 (c10 f hf).le 0; simp [h] at this; try contradiction
    }
    · exfalso; apply digit_in_region h H.b.row4 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c29 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c32 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c30 f hf)
    · rfl
  }
  clear c30min4 row3point1
  have c33c51pair: ∀ f ∈ S, Set.BijOn f {33,51} {8,9} := by freeze {
    -- by min
    intro f hf
    replace H := (H f).mp hf
    apply locked_set_from_naked_set (H.b.box6)
    intro c hc
    rcases hc with rfl | rfl
    · cases h: f 33
      · exfalso; apply digit_in_region h H.b.row4 (c28 f hf)
      · exfalso; apply digit_in_region h H.b.row4 (c29 f hf)
      · exfalso; apply digit_in_region h H.b.row4 (c32 f hf)
      · exfalso; apply digit_in_region h H.b.row4 (c30 f hf)
      · exfalso; apply digit_in_region h H.b.col7 (c15 f hf)
      · exfalso; apply digit_in_region h H.b.col7 (c69 f hf)
      · exfalso; apply digit_in_region h H.b.col7 (c6 f hf)
      · decide
      · decide
    · have thermoA: Thermometer f [50,51] := by
        have this1: [50,51] <:+: [58,49,50,51] := by decide
        exact sub_cont_thermo H.thermo7 this1
      let this := thermometer_mins thermoA (c50 f hf).symm.le 1
      simp at this
      cases h: f 51 <;> try {rw [h] at this; contradiction}
      · decide
      · decide
  }
  have c24: ∀ f ∈ S, f 24 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 24
    · rfl
    · exfalso; apply digit_in_region h H.b.box3 (c8 f hf)
    · exfalso; apply digit_in_region h H.b.col7 (c78 f hf)
    · exfalso; apply digit_in_region h H.b.col7 (c60 f hf)
    · exfalso; apply digit_in_region h H.b.col7 (c15 f hf)
    · exfalso; apply digit_in_region h H.b.col7 (c69 f hf)
    · exfalso; apply digit_in_region h H.b.col7 (c6 f hf)
    · exfalso; apply locked_set_in_region h H.b.col7 (c33c51pair f hf)
    · exfalso; apply locked_set_in_region h H.b.col7 (c33c51pair f hf)
  }
  have c25c26pair: ∀ f ∈ S, Set.BijOn f {25,26} {4,9} := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c24c25c26triple f hf) (c24 f hf)
  }
  clear c24c25c26triple
  have c25: ∀ f ∈ S, f 25 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c25c26pair f hf).mapsTo (x := 25) (by simp)
    cases h with
    | inl h => exact h
    | inr h => exfalso; apply digit_in_region h H.b.col8 (c70 f hf)
  }
  have c26: ∀ f ∈ S, f 26 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c25c26pair f hf) (c25 f hf)
  }
  clear c25c26pair thermoA c58min2
  have c42: ∀ f ∈ S, f 42 = 2 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 42
    · exfalso; apply digit_in_region h H.b.col7 (c24 f hf)
    · rfl
    · exfalso; exact digit_in_region h H.b.col7 (c78 f hf)
    · exfalso; exact digit_in_region h H.b.col7 (c60 f hf)
    · exfalso; exact digit_in_region h H.b.col7 (c15 f hf)
    · exfalso; exact digit_in_region h H.b.col7 (c69 f hf)
    · exfalso; exact digit_in_region h H.b.col7 (c6 f hf)
    · exfalso; exact locked_set_in_region h H.b.col7 (c33c51pair f hf)
    · exfalso; exact locked_set_in_region h H.b.col7 (c33c51pair f hf)
  }
  have c53: ∀ f ∈ S, f 53 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 53
    · exfalso; exact digit_in_region h H.b.col9 (c80 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c8 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c17 f hf)
    · rfl
    · exfalso; exact digit_in_region h H.b.row6 (c49 f hf)
    · exfalso; exact digit_in_region h H.b.row6 (c46 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c62 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c71 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c26 f hf)
  }
  have c35: ∀ f ∈ S, f 35 = 6 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 35
    · exfalso; exact digit_in_region h H.b.col9 (c80 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c8 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c17 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c53 f hf)
    · exfalso; exact digit_in_region h H.b.row4 (c27 f hf)
    · rfl
    · exfalso; exact digit_in_region h H.b.col9 (c62 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c71 f hf)
    · exfalso; exact digit_in_region h H.b.col9 (c26 f hf)
  }
  have c44: ∀ f ∈ S, f 44 = 5 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 44
    · exfalso; apply digit_in_region h H.b.col9 (c80 f hf)
    · exfalso; apply digit_in_region h H.b.col9 (c8 f hf)
    · exfalso; apply digit_in_region h H.b.col9 (c17 f hf)
    · exfalso; apply digit_in_region h H.b.col9 (c53 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col9 (c35 f hf)
    · exfalso; apply digit_in_region h H.b.col9 (c62 f hf)
    · exfalso; apply digit_in_region h H.b.col9 (c71 f hf)
    · exfalso; apply digit_in_region h H.b.col9 (c26 f hf)
  }
  have c43: ∀ f ∈ S, f 43 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 43
    · exfalso; apply digit_in_region h H.b.row5 (c41 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c79 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col8 (c25 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c61 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c16 f hf)
    · exfalso; apply digit_in_region h H.b.row5 (c37 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c7 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c70 f hf)
  }
  have c52: ∀ f ∈ S, f 52 = 1 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 52
    · rfl
    · exfalso; apply digit_in_region h H.b.col8 (c79 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c43 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c25 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c61 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c16 f hf)
    · exfalso; apply digit_in_region h H.b.row6 (c50 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c7 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c70 f hf)
  }
  have c34: ∀ f ∈ S, f 34 = 7 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 34
    · exfalso; apply digit_in_region h H.b.col8 (c52 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c79 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c43 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c25 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c61 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c16 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col8 (c7 f hf)
    · exfalso; apply digit_in_region h H.b.col8 (c70 f hf)
  }
  have c31: ∀ f ∈ S, f 31 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 31
    · exfalso; apply digit_in_region h H.b.row4 (c28 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c29 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c32 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c30 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c27 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c35 f hf)
    · exfalso; apply digit_in_region h H.b.row4 (c34 f hf)
    · exfalso; apply digit_in_region h H.b.box5 (c39 f hf)
    · rfl
  }
  have c40: ∀ f ∈ S, f 40 = 6 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 40
    · exfalso; apply digit_in_region h H.b.col5 (c13 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c58 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c67 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c4 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c49 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col5 (c22 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c76 f hf)
    · exfalso; apply digit_in_region h H.b.col5 (c31 f hf)
  }
  have c33: ∀ f ∈ S, f 33 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    replace h := (c33c51pair f hf).mapsTo (x := 33) (by simp)
    cases h with
    | inl h => assumption
    | inr h => exfalso; apply digit_in_region h H.b.row4 (c31 f hf)
  }
  have c51: ∀ f ∈ S, f 51 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c33c51pair f hf) (c33 f hf)
  }
  clear c33c51pair
  have c47: ∀ f ∈ S, f 47 = 8 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c47c51pair f hf) (c51 f hf)
  }
  clear c47c51pair
  have c38: ∀ f ∈ S, f 38 = 9 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    simpa using locked_set_reducton (c38c47pair f hf) (c47 f hf)
  }
  clear c38c47pair
  have c36: ∀ f ∈ S, f 36 = 4 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 36
    · exfalso; apply digit_in_region h H.b.col1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c63 f hf)
    · exfalso; apply digit_in_region h H.b.row5 (c43 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col1 (c27 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c18 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c9 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c54 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c72 f hf)
  }
  have c45: ∀ f ∈ S, f 45 = 3 := by freeze {
    intro f hf
    replace H := (H f).mp hf
    cases h: f 45
    · exfalso; apply digit_in_region h H.b.col1 (c0 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c63 f hf)
    · rfl
    · exfalso; apply digit_in_region h H.b.col1 (c36 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c27 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c18 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c9 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c54 f hf)
    · exfalso; apply digit_in_region h H.b.col1 (c72 f hf)
  }
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
    · exact c0 h hh
    · exact c1 h hh
    · exact c2 h hh
    · exact c3 h hh
    · exact c4 h hh
    · exact c5 h hh
    · exact c6 h hh
    · exact c7 h hh
    · exact c8 h hh
    · exact c9 h hh
    · exact c10 h hh
    · exact c11 h hh
    · exact c12 h hh
    · exact c13 h hh
    · exact c14 h hh
    · exact c15 h hh
    · exact c16 h hh
    · exact c17 h hh
    · exact c18 h hh
    · exact c19 h hh
    · exact c20 h hh
    · exact c21 h hh
    · exact c22 h hh
    · exact c23 h hh
    · exact c24 h hh
    · exact c25 h hh
    · exact c26 h hh
    · exact c27 h hh
    · exact c28 h hh
    · exact c29 h hh
    · exact c30 h hh
    · exact c31 h hh
    · exact c32 h hh
    · exact c33 h hh
    · exact c34 h hh
    · exact c35 h hh
    · exact c36 h hh
    · exact c37 h hh
    · exact c38 h hh
    · exact c39 h hh
    · exact c40 h hh
    · exact c41 h hh
    · exact c42 h hh
    · exact c43 h hh
    · exact c44 h hh
    · exact c45 h hh
    · exact c46 h hh
    · exact c47 h hh
    · exact c48 h hh
    · exact c49 h hh
    · exact c50 h hh
    · exact c51 h hh
    · exact c52 h hh
    · exact c53 h hh
    · exact c54 h hh
    · exact c55 h hh
    · exact c56 h hh
    · exact c57 h hh
    · exact c58 h hh
    · exact c59 h hh
    · exact c60 h hh
    · exact c61 h hh
    · exact c62 h hh
    · exact c63 h hh
    · exact c64 h hh
    · exact c65 h hh
    · exact c66 h hh
    · exact c67 h hh
    · exact c68 h hh
    · exact c69 h hh
    · exact c70 h hh
    · exact c71 h hh
    · exact c72 h hh
    · exact c73 h hh
    · exact c74 h hh
    · exact c75 h hh
    · exact c76 h hh
    · exact c77 h hh
    · exact c78 h hh
    · exact c79 h hh
    · exact c80 h hh
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
