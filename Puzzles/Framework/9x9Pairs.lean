import SudokuLean.Basic
import SudokuLean.BaselineConstraints
import SudokuLean.Symbols9

set_option linter.style.whitespace false


-- this is the 18 clue tough from Andrew Stuart Sudoku Wiki
structure TestPuzzle2 (solution: Nat -> Symbols9) where
  b: NormalSudoku solution
  given1:  solution  1 = Symbols9.three
  given5:  solution  5 = Symbols9.seven
  given10: solution 10 = Symbols9.six
  given11: solution 11 = Symbols9.seven
  given12: solution 12 = Symbols9.one
  given15: solution 15 = Symbols9.three
  given16: solution 16 = Symbols9.five
  given19: solution 19 = Symbols9.one
  given20: solution 20 = Symbols9.nine
  given27: solution 27 = Symbols9.five
  given35: solution 35 = Symbols9.seven
  given37: solution 37 = Symbols9.seven
  given39: solution 39 = Symbols9.two
  given41: solution 41 = Symbols9.three
  given43: solution 43 = Symbols9.one
  given45: solution 45 = Symbols9.nine
  given53: solution 53 = Symbols9.eight
  given60: solution 60 = Symbols9.six
  given61: solution 61 = Symbols9.eight
  given64: solution 64 = Symbols9.eight
  given65: solution 65 = Symbols9.six
  given68: solution 68 = Symbols9.two
  given69: solution 69 = Symbols9.nine
  given70: solution 70 = Symbols9.seven
  given75: solution 75 = Symbols9.seven
  given79: solution 79 = Symbols9.four
  outside_grid: ∀ x, x ≥ 81 -> solution x = Symbols9.one -- just need something to call default




theorem SolveTestPuzzle2 {S : Set (Nat → Symbols9)} (H : ∀ f, f ∈ S ↔ TestPuzzle2 f):
  ∃! (g: Nat -> Symbols9), g ∈ S := by
  have c2: ∀ f ∈ S, f 2 = 5 := by
    -- hidden single in box 1
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box1 (by simp) 5
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.col1 H.given27
    · exfalso; apply digit_in_cell h H.given1
    · assumption
    · exfalso; apply digit_in_region h H.b.col1 H.given27
    · exfalso; apply digit_in_cell h H.given10
    · exfalso; apply digit_in_cell h H.given11
    · exfalso; apply digit_in_region h H.b.col1 H.given27
    · exfalso; apply digit_in_cell h H.given19
    · exfalso; apply digit_in_cell h H.given20
  have c24: ∀ f ∈ S, f 24 = 7 := by
    -- hidden single in box 3
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box3 (by simp) 7
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.row1 H.given5
    · exfalso; apply digit_in_region h H.b.row1 H.given5
    · exfalso; apply digit_in_region h H.b.row1 H.given5
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_cell h H.given16
    · exfalso; apply digit_in_region h H.b.col9 H.given35
    · assumption
    · exfalso; apply digit_in_region h H.b.col8 H.given70
    · exfalso; apply digit_in_region h H.b.col9 H.given35
  have c36: ∀ f ∈ S, f 36 = 6 := by
    -- hidden single in box 4
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box4 (by simp) 6
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h H.given27
    · exfalso; apply digit_in_region h H.b.col2 H.given10
    · exfalso; apply digit_in_region h H.b.col3 H.given65
    · assumption
    · exfalso; apply digit_in_region h H.b.col2 H.given10
    · exfalso; apply digit_in_region h H.b.col3 H.given65
    · exfalso; apply digit_in_cell h H.given45
    · exfalso; apply digit_in_region h H.b.col2 H.given10
    · exfalso; apply digit_in_region h H.b.col3 H.given65
  have c49: ∀ f ∈ S, f 49 = 7 := by
    -- hidden single in box 5
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box5 (by simp) 7
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.row4 H.given35
    · exfalso; apply digit_in_region h H.b.row4 H.given35
    · exfalso; apply digit_in_region h H.b.row4 H.given35
    · exfalso; apply digit_in_cell h H.given39
    · exfalso; apply digit_in_region h H.b.row5 H.given37
    · exfalso; apply digit_in_cell h H.given41
    · exfalso; apply digit_in_region h H.b.col4 H.given75
    · assumption
    · exfalso; apply digit_in_region h H.b.col6 H.given5
  have c54: ∀ f ∈ S, f 54 = 7 := by
    -- hidden single in box 7
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box7 (by simp) 7
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · assumption
    · exfalso; apply digit_in_region h H.b.col2 H.given37
    · exfalso; apply digit_in_region h H.b.col3 H.given11
    · exfalso; apply digit_in_region h H.b.row8 H.given70
    · exfalso; apply digit_in_region h H.b.row8 H.given70
    · exfalso; apply digit_in_region h H.b.row8 H.given70
    · exfalso; apply digit_in_region h H.b.row9 H.given75
    · exfalso; apply digit_in_region h H.b.row9 H.given75
    · exfalso; apply digit_in_region h H.b.row9 H.given75
  have c6: ∀ f ∈ S, f 6 = 8 := by
    -- hidden single in box 3
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box3 (by simp) 8
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · assumption
    · exfalso; apply digit_in_region h H.b.col8 H.given61
    · exfalso; apply digit_in_region h H.b.col9 H.given53
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_region h H.b.col8 H.given61
    · exfalso; apply digit_in_region h H.b.col9 H.given53
    · exfalso; apply digit_in_cell h (c24 f hf)
    · exfalso; apply digit_in_region h H.b.col8 H.given61
    · exfalso; apply digit_in_region h H.b.col9 H.given53
  have c8: ∀ f ∈ S, f 8 = 1 := by
    -- hidden single in box 3
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.box3 (by simp) 1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c6 f hf)
    · exfalso; apply digit_in_region h H.b.col8 H.given43
    · assumption
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_cell h H.given16
    · exfalso; apply digit_in_region h H.b.row2 H.given12
    · exfalso; apply digit_in_cell h (c24 f hf)
    · exfalso; apply digit_in_region h H.b.row3 H.given19
    · exfalso; apply digit_in_region h H.b.row3 H.given19
  have c78: ∀ f ∈ S, f 78 = 1 := by
    -- hidden single in column 7
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.col7 (by simp) 1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c6 f hf)
    · exfalso; apply digit_in_cell h H.given15
    · exfalso; apply digit_in_cell h (c24 f hf)
    · exfalso; apply digit_in_region h H.b.box6 H.given43
    · exfalso; apply digit_in_region h H.b.box6 H.given43
    · exfalso; apply digit_in_region h H.b.box6 H.given43
    · exfalso; apply digit_in_cell h H.given60
    · exfalso; apply digit_in_cell h H.given69
    · assumption
  have c26: ∀ f ∈ S, f 26 = 6 := by
    -- hidden single in column 7
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.col9 (by simp) 6
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_cell h (c8 f hf)
    · exfalso; apply digit_in_region h H.b.row2 H.given10
    · assumption
    · exfalso; apply digit_in_cell h H.given35
    · exfalso; apply digit_in_region h H.b.row5 (c36 f hf)
    · exfalso; apply digit_in_cell h H.given53
    · exfalso; apply digit_in_region h H.b.box9 H.given60
    · exfalso; apply digit_in_region h H.b.box9 H.given60
    · exfalso; apply digit_in_region h H.b.box9 H.given60
  have c63: ∀ f ∈ S, f 63 = 1 := by
    -- hidden single in column 1
    intro f hf
    replace H := (H f).mp hf
    let h := unique_region_same_size_surjective H.b.col1 (by simp) 1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
      true_and] at h
    split_disjunctive_9 h
    · exfalso; apply digit_in_region h H.b.box1 H.given19
    · exfalso; apply digit_in_region h H.b.box1 H.given19
    · exfalso; apply digit_in_region h H.b.box1 H.given19
    · exfalso; apply digit_in_cell h H.given27
    · exfalso; apply digit_in_cell h (c36 f hf)
    · exfalso; apply digit_in_cell h H.given45
    · exfalso; apply digit_in_cell h (c54 f hf)
    · assumption
    · exfalso; apply digit_in_region h H.b.row9 (c78 f hf)
  have c25: ∀ f ∈ S, f 25 = 2 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 25 with
    | one => exfalso; exact digit_in_region h H.b.box3 (c8 f hf)
    | two => rfl
    | three => exfalso; exact digit_in_region h H.b.box3 H.given15
    | four => exfalso; exact digit_in_region h H.b.col8 H.given79
    | five => exfalso; exact digit_in_region h H.b.box3 H.given16
    | six => exfalso; exact digit_in_region h H.b.box3 (c26 f hf)
    | seven => exfalso; exact digit_in_region h H.b.box3 (c24 f hf)
    | eight => exfalso; exact digit_in_region h H.b.box3 (c6 f hf)
    | nine => exfalso; exact digit_in_region h H.b.row3 H.given20
  have c7: ∀ f ∈ S, f 7 = 9 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 with
    | one => exfalso; exact digit_in_region h H.b.box3 (c8 f hf)
    | two => exfalso; exact digit_in_region h H.b.box3 (c25 f hf)
    | three => exfalso; exact digit_in_region h H.b.box3 H.given15
    | four => exfalso; exact digit_in_region h H.b.col8 H.given79
    | five => exfalso; exact digit_in_region h H.b.box3 H.given16
    | six => exfalso; exact digit_in_region h H.b.box3 (c26 f hf)
    | seven => exfalso; exact digit_in_region h H.b.box3 (c24 f hf)
    | eight => exfalso; exact digit_in_region h H.b.box3 (c6 f hf)
    | nine => rfl
  have c17: ∀ f ∈ S, f 17 = 4 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 17 with
    | one => exfalso; exact digit_in_region h H.b.box3 (c8 f hf)
    | two => exfalso; exact digit_in_region h H.b.box3 (c25 f hf)
    | three => exfalso; exact digit_in_region h H.b.box3 H.given15
    | four => rfl
    | five => exfalso; exact digit_in_region h H.b.box3 H.given16
    | six => exfalso; exact digit_in_region h H.b.box3 (c26 f hf)
    | seven => exfalso; exact digit_in_region h H.b.box3 (c24 f hf)
    | eight => exfalso; exact digit_in_region h H.b.box3 (c6 f hf)
    | nine => exfalso; exact digit_in_region h H.b.box3 (c7 f hf)
  have c44: ∀ f ∈ S, f 44 = 9 := by sorry
    -- hidden single
  have c72: ∀ f ∈ S, f 72 = 3 := by sorry
    -- hidden single
  have c74: ∀ f ∈ S, f 74 = 2 := by sorry
    -- naked single
  have c56: ∀ f ∈ S, f 56 = 4 := by sorry
    -- naked single
  have c80: ∀ f ∈ S, f 80 = 5 := by sorry
    -- naked single
  have c38: ∀ f ∈ S, f 38 = 8 := by sorry
    -- naked single
  have c71: ∀ f ∈ S, f 71 = 3 := by sorry
    -- naked single
  have c73: ∀ f ∈ S, f 73 = 9 := by sorry
    -- naked single
  have c55: ∀ f ∈ S, f 55 = 5 := by sorry
    -- naked single
  have c62: ∀ f ∈ S, f 62 = 2 := by sorry
    -- naked single
  have c28c33pair: ∀ f (hf:f ∈ S), Pair ((H f).mp hf).b.row4 28 33 2 4 := by
    intro f hf
    replace H := (H f).mp hf
    constructor
    · decide
    · decide
    · decide
    · decide
    · cases h: f 28 with
      | one => exfalso; exact digit_in_region h H.b.col2 H.given19
      | two => simp
      | three => exfalso; exact digit_in_region h H.b.col2 H.given1
      | four => simp
      | five => exfalso; exact digit_in_region h H.b.col2 (c55 f hf)
      | six => exfalso; exact digit_in_region h H.b.col2 H.given10
      | seven => exfalso; exact digit_in_region h H.b.col2 H.given37
      | eight => exfalso; exact digit_in_region h H.b.col2 H.given64
      | nine => exfalso; exact digit_in_region h H.b.col2 (c73 f hf)
    · cases h: f 33 with
      | one => exfalso; exact digit_in_region h H.b.col7 (c78 f hf)
      | two => simp
      | three => exfalso; exact digit_in_region h H.b.col7 H.given15
      | four => simp
      | five => exfalso; exact digit_in_region h H.b.row4 H.given27
      | six => exfalso; exact digit_in_region h H.b.col7 H.given60
      | seven => exfalso; exact digit_in_region h H.b.col7 (c24 f hf)
      | eight => exfalso; exact digit_in_region h H.b.col7 (c6 f hf)
      | nine => exfalso; exact digit_in_region h H.b.col7 H.given69
  have c40c67pair: ∀ f (hf:f ∈ S), Pair ((H f).mp hf).b.col5 40 67 4 5 := by
    intro f hf
    replace H := (H f).mp hf
    constructor
    repeat decide
    · cases h: f 40 with
      | one => exfalso; exact digit_in_region h H.b.row5 H.given43
      | two => exfalso; exact digit_in_region h H.b.row5 H.given39
      | three => exfalso; exact digit_in_region h H.b.row5 H.given41
      | four => simp
      | five => simp
      | six => exfalso; exact digit_in_region h H.b.row5 (c36 f hf)
      | seven => exfalso; exact digit_in_region h H.b.row5 H.given37
      | eight => exfalso; exact digit_in_region h H.b.row5 (c38 f hf)
      | nine => exfalso; exact digit_in_region h H.b.row5 (c44 f hf)
    · cases h: f 67 with
      | one => exfalso; exact digit_in_region h H.b.row8 (c63 f hf)
      | two => exfalso; exact digit_in_region h H.b.row8 H.given68
      | three => exfalso; exact digit_in_region h H.b.row8 (c71 f hf)
      | four => simp
      | five => simp
      | six => exfalso; exact digit_in_region h H.b.row8 H.given65
      | seven => exfalso; exact digit_in_region h H.b.row8 H.given70
      | eight => exfalso; exact digit_in_region h H.b.row8 H.given64
      | nine => exfalso; exact digit_in_region h H.b.row8 H.given69
  have c23c50pair: ∀ f (hf:f ∈ S), Pair ((H f).mp hf).b.col6 23 50 4 5 := by
    -- hidden pair in col 6
    intro f hf
    replace H := (H f).mp hf
    apply create_hidden_pair H.b.col6
    constructor
    · let h := unique_region_same_size_surjective H.b.col6 (by simp) 4
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
        true_and] at h
      split_disjunctive_9 h
      · exfalso; exact digit_in_cell h H.given5
      · exfalso; exact digit_in_region h H.b.row2 (c17 f hf)
      · left; assumption
        -- first instance of using a pair to cross out a candidate
      · exfalso; refine Pair.in_region h H.b.row4 (c28c33pair f hf)
      · exfalso; exact digit_in_cell h H.given41
      · right; assumption
      · exfalso; exact digit_in_region h H.b.row7 (c56 f hf)
      · exfalso; exact digit_in_cell h H.given68
      · exfalso; exact digit_in_region h H.b.row9 H.given79
    · let h := unique_region_same_size_surjective H.b.col6 (by simp) 5
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq,
        true_and] at h
      split_disjunctive_9 h
      · exfalso; exact digit_in_cell h H.given5
      · exfalso; exact digit_in_region h H.b.row2 H.given16
      · left; assumption
      · exfalso; refine digit_in_region h H.b.row4 H.given27
      · exfalso; exact digit_in_cell h H.given41
      · right; assumption
      · exfalso; exact digit_in_region h H.b.row7 (c55 f hf)
      · exfalso; exact digit_in_cell h H.given68
      · exfalso; exact digit_in_region h H.b.row9 (c80 f hf)
  have c47: ∀ f ∈ S, f 47 = 1 := by sorry
    -- hidden single
  have c29: ∀ f ∈ S, f 29 = 3 := by sorry
    -- naked single
  have c34: ∀ f ∈ S, f 34 = 6 := by sorry
  have c52: ∀ f ∈ S, f 52 = 3 := by sorry
    -- naked single
  have c48: ∀ f ∈ S, f 48 = 6 := by sorry
    -- hidden single
  have c77: ∀ f ∈ S, f 77 = 6 := by sorry
    -- hidden single
  have c76: ∀ f ∈ S, f 76 = 8 := by sorry
    -- naked single
  have c3: ∀ f ∈ S, f 3 = 4 := by sorry
    -- naked single
  have c0: ∀ f ∈ S, f 0 = 2 := by sorry
    -- hidden single ↓
  have c22: ∀ f ∈ S, f 22 = 3 := by sorry
  have c23: ∀ f ∈ S, f 23 = 5 := by
    intro f hf
    replace H := (H f).mp hf
    cases (c23c50pair f hf).c1_possible with
    | inl h => exfalso; exact digit_in_region h H.b.box2 (c3 f hf)
    | inr h => assumption
  have c50: ∀ f ∈ S, f 50 = 4 := by
    -- resolve pair c23c50
    intro f hf
    replace H := (H f).mp hf
    exact (c23c50pair f hf).resolve_with_c1_e (c23 f hf)

  clear c23c50pair
  have c66: ∀ f ∈ S, f 66 = 5 := by sorry
  have c4: ∀ f ∈ S, f 4 = 6 := by sorry
    -- naked single ↓
  have c9: ∀ f ∈ S, f 9 = 8 := by sorry
  have c21: ∀ f ∈ S, f 21 = 8 := by sorry
  have c67: ∀ f ∈ S, f 67 = 4 := by sorry
  have c40: ∀ f ∈ S, f 40 = 5 := by sorry
  have c14: ∀ f ∈ S, f 14 = 9 := by sorry
  have c18: ∀ f ∈ S, f 18 = 4 := by sorry
  have c30: ∀ f ∈ S, f 30 = 9 := by sorry
  have c46: ∀ f ∈ S, f 46 = 2 := by sorry
  have c13: ∀ f ∈ S, f 13 = 2 := by sorry
  have c28: ∀ f ∈ S, f 28 = 4 := by sorry
  have c33: ∀ f ∈ S, f 33 = 2 := by sorry
  have c31: ∀ f ∈ S, f 31 = 1 := by sorry
  have c42: ∀ f ∈ S, f 42 = 4 := by sorry
  have c51: ∀ f ∈ S, f 51 = 5 := by sorry
  have c57: ∀ f ∈ S, f 57 = 3 := by sorry
  have c59: ∀ f ∈ S, f 59 = 1 := by sorry
  have c32: ∀ f ∈ S, f 32 = 8 := by sorry
  have c58: ∀ f ∈ S, f 58 = 9 := by sorry
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
    · exact c0 h hh
    · exact H.given1
    · exact c2 h hh
    · exact c3 h hh
    · exact c4 h hh
    · exact H.given5
    · exact c6 h hh
    · exact c7 h hh
    · exact c8 h hh
    · exact c9 h hh
    · exact H.given10
    · exact H.given11
    · exact H.given12
    · exact c13 h hh
    · exact c14 h hh
    · exact H.given15
    · exact H.given16
    · exact c17 h hh
    · exact c18 h hh
    · exact H.given19
    · exact H.given20
    · exact c21 h hh
    · exact c22 h hh
    · exact c23 h hh
    · exact c24 h hh
    · exact c25 h hh
    · exact c26 h hh
    · exact H.given27
    · exact c28 h hh
    · exact c29 h hh
    · exact c30 h hh
    · exact c31 h hh
    · exact c32 h hh
    · exact c33 h hh
    · exact c34 h hh
    · exact H.given35
    · exact c36 h hh
    · exact H.given37
    · exact c38 h hh
    · exact H.given39
    · exact c40 h hh
    · exact H.given41
    · exact c42 h hh
    · exact H.given43
    · exact c44 h hh
    · exact H.given45
    · exact c46 h hh
    · exact c47 h hh
    · exact c48 h hh
    · exact c49 h hh
    · exact c50 h hh
    · exact c51 h hh
    · exact c52 h hh
    · exact H.given53
    · exact c54 h hh
    · exact c55 h hh
    · exact c56 h hh
    · exact c57 h hh
    · exact c58 h hh
    · exact c59 h hh
    · exact H.given60
    · exact H.given61
    · exact c62 h hh
    · exact c63 h hh
    · exact H.given64
    · exact H.given65
    · exact c66 h hh
    · exact c67 h hh
    · exact H.given68
    · exact H.given69
    · exact H.given70
    · exact c71 h hh
    · exact c72 h hh
    · exact c73 h hh
    · exact c74 h hh
    · exact H.given75
    · exact c76 h hh
    · exact c77 h hh
    · exact c78 h hh
    · exact H.given79
    · exact c80 h hh
  rw [H.outside_grid]
  · unfold g
    simp at xin
    conv =>
      enter [2, 1]
      apply Array.getElem?_eq_none (by {rw [len]; assumption})
    simp
  push_neg at xin
  apply xin
