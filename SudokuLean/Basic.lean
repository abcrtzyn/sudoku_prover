import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import SudokuLean.Symbols4
import SudokuLean.Symbols9
-- import MathLib.Data.Finset.Defs
-- import Mathlib.Data.Finset.Dedup

set_option linter.style.whitespace false
set_option linter.style.longLine false



-- ∃ F(c) k
-- s.t. for all c, F(c) ∈ powerset digits - {∅}
-- all cages sum to k
-- ∃ a way to pick from F to satisfy the constraints
-- ->
-- ∃! solution f(c) k₀
-- s.t for all c, f(c) in F(c)
-- C(f) is true
-- all cages sum to k₀
-- forall cells |F(c)| = 1

-- schrodinger cells, rather than a unique f(c), prove that every f(c) works or contradicts
-- and that for the unresolved cells, it has the largest set possible to still be valid
-- I think Ill hold off on this for a long while


-- chaos construction
-- partition of the grid, look it up from discrete structures
-- connected by graphs, fun stuff
-- regions are 9 cells
-- hypothesis there exists a partition...
-- conclusion there exists a unique partition ...




-- Unique Region says that each digit in that region is different
-- Regions are allowed to be smaller than the size of the grid
def UniqueRegion {α} (f: Nat -> α) (r: Set Nat) :=  Set.InjOn f r

-- any unique region that is the same size as the digits is bijective, not just injective
-- theorem unique_region_same_bijection (f: Nat -> Symbols4) (r: Set Nat) (h: UniqueRegion f r) (hs: r.ncard = 4): Set.BijOn f r Set.univ := by
--   constructor
--   · simp [Set.MapsTo]
--   constructor
--   · apply h

--   apply Set.toFinset
--   apply Finset.surjOn_of_injOn_of_card_le

--   -- simp [Set.SurjOn, Set.image]
--   -- ext x
--   -- simp


-- when you hypothesize that f x = d and f y = d, where x and y are in the same region
-- this proves that false
theorem digit_in_region {α} {f: Nat -> α} {r: Set Nat} {d: α} (unique_region: UniqueRegion f r) {target: Nat} {conflict: Nat} (d_target: f target = d) (d_conflict: f conflict = d) (h4: target ≠ conflict := by decide) (h0: target ∈ r := by decide) (h1: conflict ∈ r := by decide): False := by
  absurd d_target
  rw [<- d_conflict]
  apply unique_region.ne <;> assumption







structure TestPuzzle (solution: Nat -> Symbols4) where
  row1: UniqueRegion solution { 0, 1, 2, 3}
  row2: UniqueRegion solution { 4, 5, 6, 7}
  row3: UniqueRegion solution { 8, 9,10,11}
  row4: UniqueRegion solution {12,13,14,15}
  col1: UniqueRegion solution { 0, 4, 8,12}
  col2: UniqueRegion solution { 1, 5, 9,13}
  col3: UniqueRegion solution { 2, 6,10,14}
  col4: UniqueRegion solution { 3, 7,11,15}
  box1: UniqueRegion solution { 0, 1, 4, 5}
  box2: UniqueRegion solution { 2, 3, 6, 7}
  box3: UniqueRegion solution { 8, 9,12,13}
  box4: UniqueRegion solution {10,11,14,15}
  given2: solution 2 = 4
  given4: solution 4 = 4
  given6: solution 6 = 3
  given9: solution 9 = 4
  given11: solution 11 = 3
  given13: solution 13 = 1
  outside_grid: ∀ x, x > 15 -> solution x = Symbols4.one -- just need something to call default

-- 1 3 4 2
-- 4 2 3 1
-- 2 4 1 3
-- 3 1 2 4

theorem SolveTestPuzzle {S : Set (Nat → Symbols4)} (H : ∀ f, f ∈ S ↔ TestPuzzle f): ∃! (g: Nat -> Symbols4), g ∈ S := by
  -- have c6n4: ∀ f ∈ S, f 6 ≠ Symbols4.four := by
  --   intro f hf
  --   specialize H f hf
  --   rw [<- H.given5]
  --   apply H.row2.ne <;> simp
  have c5: ∀ f ∈ S, f 5 = 2 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 5 with
    | two => rfl
    | one => exfalso; exact digit_in_region H.col2 h H.given13
    | three => exfalso; exact digit_in_region H.row2 h H.given6
    | four => exfalso; exact digit_in_region H.box1 h H.given4
  have c1: ∀ f ∈ S, f 1 = 3 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 1 with
    | three => rfl
    | one => exfalso; exact digit_in_region H.col2 h H.given13
    | two => exfalso; exact digit_in_region H.col2 h (c5 f hf)
    | four => exfalso; exact digit_in_region H.col2 h H.given9
  have c0: ∀ f ∈ S, f 0 = 1 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 0 with
    | one => rfl
    | two => exfalso; exact digit_in_region H.box1 h (c5 f hf)
    | three => exfalso; exact digit_in_region H.box1 h (c1 f hf)
    | four => exfalso; exact digit_in_region H.box1 h H.given4
  have c3: ∀ f ∈ S, f 3 = 2 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 3 with
    | two => rfl
    | one => exfalso; exact digit_in_region H.row1 h (c0 f hf)
    | three => exfalso; exact digit_in_region H.row1 h (c1 f hf)
    | four => exfalso; exact digit_in_region H.row1 h H.given2
  have c7: ∀ f ∈ S, f 7 = 1 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 with
    | one => rfl
    | two => exfalso; exact digit_in_region H.row2 h (c5 f hf)
    | three => exfalso; exact digit_in_region H.row2 h H.given6
    | four => exfalso; exact digit_in_region H.row2 h H.given4
  have c15: ∀ f ∈ S, f 15 = 4 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 15 with
    | four => rfl
    | one => exfalso; exact digit_in_region H.col4 h (c7 f hf)
    | two => exfalso; exact digit_in_region H.col4 h (c3 f hf)
    | three => exfalso; exact digit_in_region H.col4 h H.given11
  have c14: ∀ f ∈ S, f 14 = 2 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 14 with
    | two => rfl
    | one => exfalso; exact digit_in_region H.row4 h H.given13
    | three => exfalso; exact digit_in_region H.box4 h H.given11
    | four => exfalso; exact digit_in_region H.row4 h (c15 f hf)
  have c10: ∀ f ∈ S, f 10 = 1 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 10 with
    | one => rfl
    | two => exfalso; exact digit_in_region H.box4 h (c14 f hf)
    | three => exfalso; exact digit_in_region H.box4 h H.given11
    | four => exfalso; exact digit_in_region H.box4 h (c15 f hf)
  have c8: ∀ f ∈ S, f 8 = 2 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 8 with
    | two => rfl
    | one => exfalso; exact digit_in_region H.row3 h (c10 f hf)
    | three => exfalso; exact digit_in_region H.row3 h H.given11
    | four => exfalso; exact digit_in_region H.row3 h H.given9
  have c12: ∀ f ∈ S, f 12 = 3 := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 12 with
    | three => rfl
    | one => exfalso; exact digit_in_region H.box3 h H.given13
    | two => exfalso; exact digit_in_region H.box3 h (c8 f hf)
    | four => exfalso; exact digit_in_region H.box3 h H.given9
  -- create th function g and use it
  let g : Nat → Symbols4 := fun x =>
  match x with
  | 0 => Symbols4.one
  | 1 => Symbols4.three
  | 2 => Symbols4.four
  | 3 => Symbols4.two
  | 4 => Symbols4.four
  | 5 => Symbols4.two
  | 6 => Symbols4.three
  | 7 => Symbols4.one
  | 8 => Symbols4.two
  | 9 => Symbols4.four
  | 10 => Symbols4.one
  | 11 => Symbols4.three
  | 12 => Symbols4.three
  | 13 => Symbols4.one
  | 14 => Symbols4.two
  | 15 => Symbols4.four
  | _ => Symbols4.one -- here is the default
  use g
  constructor
  · simp only
    apply (H g).mpr
    -- prove that g obeys the constraints of the puzzle
    constructor
    iterate 12 simp [UniqueRegion, Set.InjOn] -- all the unique regions
    iterate 6 simp [g] -- all the given digits
    -- and outside the grid
    intro n hn
    unfold g
    split <;> try simp only [reduceCtorEq] <;> (absurd hn; decide)
  -- prove that forall h, h = g
  intro h hh
  replace H := (H h).mp hh
  ext x
  by_cases xin: x < 16
  · interval_cases x
    · exact c0 h hh
    · exact c1 h hh
    · exact H.given2
    · exact c3 h hh
    · exact H.given4
    · exact c5 h hh
    · exact H.given6
    · exact c7 h hh
    · exact c8 h hh
    · exact H.given9
    · exact c10 h hh
    · exact H.given11
    · exact c12 h hh
    · exact H.given13
    · exact c14 h hh
    · exact c15 h hh
  rw [H.outside_grid]
  · unfold g
    split <;> try simp only [reduceCtorEq] <;> (absurd xin; decide)
  push_neg at xin
  apply xin
