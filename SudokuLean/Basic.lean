import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
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





inductive Symbols
| one
| two
| three
| four


-- instance: Fintype Symbols where
-- elems := {Symbols.one, Symbols.two, Symbols.three, Symbols.four}
-- complete := by sorry

-- lemma card_symbols: Fintype.card Symbols = 4 := sorry

-- Unique Region says that each digit in that region is different
-- Regions are allowed to be smaller than the width of the grid
def UniqueRegion (f: Nat -> Symbols) (r: Set Nat) :=  Set.InjOn f r

-- any unique region that is the same size as the digits is bijective, not just injective
-- theorem unique_region_same_bijection (f: Nat -> Symbols) (r: Set Nat) (h: UniqueRegion f r) (hs: r.ncard = 4): Set.BijOn f r Set.univ := by
--   constructor
--   · simp [Set.MapsTo]
--   constructor
--   · apply h
--   let g : ∀ a ∈ r, Symbols := λ x _ => f x
--   have hg: ∀ a ha, g a ha ∈ Set.univ := by simp
--   have h1: ∀ (d: Symbols), d ∈ Set.univ -> ∃ x ∈ r, d = g x (x ∈ r) := by

--     intro d
--     apply Set.surj_on_of_inj_on_of_ncard_le g hg _ _ _ d _

--   simp [Set.SurjOn, Set.image]




structure TestPuzzle (solution: Nat -> Symbols) where
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
  given2: solution 2 = Symbols.four
  given4: solution 4 = Symbols.four
  given6: solution 6 = Symbols.three
  given9: solution 9 = Symbols.four
  given11: solution 11 = Symbols.three
  given13: solution 13 = Symbols.one
  outside_grid: ∀ x, x > 15 -> solution x = Symbols.one -- just need something to call default

-- 1 3 4 2
-- 4 2 3 1
-- 2 4 1 3
-- 3 1 2 4

theorem Solve {S : Set (Nat → Symbols)} (H : ∀ f, f ∈ S ↔ TestPuzzle f): ∃! (g: Nat -> Symbols), g ∈ S := by
  -- have c6n4: ∀ f ∈ S, f 6 ≠ Symbols.four := by
  --   intro f hf
  --   specialize H f hf
  --   rw [<- H.given5]
  --   apply H.row2.ne <;> simp
  have c5: ∀ f ∈ S, f 5 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 5 with
    | two => rfl
    | one => absurd h; rw [<- H.given13]; apply H.col2.ne <;> simp
    | three => absurd h; rw [<- H.given6]; apply H.row2.ne <;> simp
    | four => absurd h; rw [<- H.given4]; apply H.box1.ne <;> simp
  have c1: ∀ f ∈ S, f 1 = Symbols.three := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 1 with
    | three => rfl
    | one => absurd h; rw [<- H.given13]; apply H.col2.ne <;> simp
    | two => absurd h; rw [<- (c5 f hf)]; apply H.col2.ne <;> simp
    | four => absurd h; rw [<- H.given9]; apply H.col2.ne <;> simp
  have c0: ∀ f ∈ S, f 0 = Symbols.one := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 0 with
    | one => rfl
    | two => absurd h; rw [<- (c5 f hf)]; apply H.box1.ne <;> simp
    | three => absurd h; rw [<- (c1 f hf)]; apply H.box1.ne <;> simp
    | four => absurd h; rw [<- H.given4]; apply H.box1.ne <;> simp
  have c3: ∀ f ∈ S, f 3 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 3 with
    | two => rfl
    | one => absurd h; rw [<- (c0 f hf)]; apply H.row1.ne <;> simp
    | three => absurd h; rw [<- (c1 f hf)]; apply H.row1.ne <;> simp
    | four => absurd h; rw [<- H.given2]; apply H.row1.ne <;> simp
  have c7: ∀ f ∈ S, f 7 = Symbols.one := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 7 with
    | one => rfl
    | two => absurd h; rw [<- (c5 f hf)]; apply H.row2.ne <;> simp
    | three => absurd h; rw [<- H.given6]; apply H.row2.ne <;> simp
    | four => absurd h; rw [<- H.given4]; apply H.row2.ne <;> simp
  have c15: ∀ f ∈ S, f 15 = Symbols.four := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 15 with
    | four => rfl
    | one => absurd h; rw [<- (c7 f hf)]; apply H.col4.ne <;> simp
    | two => absurd h; rw [<- (c3 f hf)]; apply H.col4.ne <;> simp
    | three => absurd h; rw [<- H.given11]; apply H.col4.ne <;> simp
  have c14: ∀ f ∈ S, f 14 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 14 with
    | two => rfl
    | one => absurd h; rw [<- H.given13]; apply H.row4.ne <;> simp
    | three => absurd h; rw [<- H.given11]; apply H.box4.ne <;> simp
    | four => absurd h; rw [<- (c15 f hf)]; apply H.row4.ne <;> simp
  have c10: ∀ f ∈ S, f 10 = Symbols.one := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 10 with
    | one => rfl
    | two => absurd h; rw [<- (c14 f hf)]; apply H.box4.ne <;> simp
    | three => absurd h; rw [<- H.given11]; apply H.box4.ne <;> simp
    | four => absurd h; rw [<- (c15 f hf)]; apply H.box4.ne <;> simp
  have c8: ∀ f ∈ S, f 8 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 8 with
    | two => rfl
    | one => absurd h; rw [<- (c10 f hf)]; apply H.row3.ne <;> simp
    | three => absurd h; rw [<- H.given11]; apply H.row3.ne <;> simp
    | four => absurd h; rw [<- H.given9]; apply H.row3.ne <;> simp
  have c12: ∀ f ∈ S, f 12 = Symbols.three := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 12 with
    | three => rfl
    | one => absurd h; rw [<- H.given13]; apply H.box3.ne <;> simp
    | two => absurd h; rw [<- (c8 f hf)]; apply H.box3.ne <;> simp
    | four => absurd h; rw [<- H.given9]; apply H.box3.ne <;> simp
  -- create th function g and use it
  let g : Nat → Symbols := fun x =>
  match x with
  | 0 => Symbols.one
  | 1 => Symbols.three
  | 2 => Symbols.four
  | 3 => Symbols.two
  | 4 => Symbols.four
  | 5 => Symbols.two
  | 6 => Symbols.three
  | 7 => Symbols.one
  | 8 => Symbols.two
  | 9 => Symbols.four
  | 10 => Symbols.one
  | 11 => Symbols.three
  | 12 => Symbols.three
  | 13 => Symbols.one
  | 14 => Symbols.two
  | 15 => Symbols.four
  | _ => Symbols.one -- here is the default
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
