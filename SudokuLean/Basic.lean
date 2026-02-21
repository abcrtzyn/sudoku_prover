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






-- from Gemini
/- import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite

-- Index and Digit are the numbers 0-8
def Index := Fin 9
def Digit := Fin 9

-- A Grid is a total function where every cell is assigned exactly one Digit.
def Grid := Index → Index → Digit

-- A 'Unit' is a set of 9 coordinate pairs (a row, column, or box).
def Unit := Set (Index × Index)

-- The key constraint: a Unit is valid if the Grid's values over those
-- 9 cells form a Bijection with the set of all possible Digits.
def IsValidUnit (g : Grid) (u : Unit) : Prop :=
  ∀ d : Digit, ∃! cell : Index × Index, cell ∈ u ∧ g cell.1 cell.2 = d

-- Defining the shapes
def Row (i : Index) : Unit := { cell | cell.1 = i }
def Col (j : Index) : Unit := { cell | cell.2 = j }
def Block (bi bj : Fin 3) : Unit :=
  { cell | cell.1 / 3 = bi ∧ cell.2 / 3 = bj }

-- SatisfiesSudoku is the conjunction of all 27 unit constraints.
def SatisfiesSudoku (g : Grid) : Prop :=
  (∀ i, IsValidUnit g (Row i)) ∧
  (∀ j, IsValidUnit g (Col j)) ∧
  (∀ bi bj, IsValidUnit g (Block bi bj))



-- def Mapping := Index → Index → Set Digit

-- def Satisfiable (F : Mapping) : Prop :=
-- ∃ g : Grid, (∀ r c, g r c ∈ F r c) ∧ SatisfiesSudoku g


-- theorem Sudoku_Collapse (F : Mapping) :
  -- HYPOTHESIS:
  -- (Satisfiable F ∧ My17Clues F) →

  -- CONCLUSION:
  -- ∃! f : Grid, (∀ r c, f r c ∈ F r c) ∧ SatisfiesSudoku f

-- A Reduction Rule takes a mapping and returns a new mapping.
def ReductionRule := Mapping → Mapping

-- The "Preservation" property:
-- Any valid grid g that was in F must still be in F' after the rule is applied.
def IsValidReduction (rule : ReductionRule) : Prop :=
  ∀ (F : Mapping) (g : Grid),
    (∀ r c, g r c ∈ F r c) ∧ SatisfiesSudoku g →
    (∀ r c, g r c ∈ (rule F) r c)

def pruneNakedSingle (F : Mapping) (r c : Index) (digit : Digit) : Mapping :=
  if F r c = {digit} then
    λ r' c' =>
      if (r', c') = (r, c) then {digit}
      else if InSameUnit (r, c) (r', c') then (F r' c') \ {digit}
      else F r' c'
  else F

theorem SolveWithReduction (F_start : Mapping) :
  let F_final := applyAllRules F_start
  (∀ r c, ∃! d, d ∈ F_final r c) →
  (∀ g h, g ∈ F_final → h ∈ F_final → g = h)


  -/


-- theorem x ∈ S ->

macro "intro_spec" h:ident : tactic =>
  `(tactic| (intro f hf; specialize $h f hf))


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
  row1: UniqueRegion solution { 1, 2, 3, 4}
  row2: UniqueRegion solution { 5, 6, 7, 8}
  row3: UniqueRegion solution { 9,10,11,12}
  row4: UniqueRegion solution {13,14,15,16}
  col1: UniqueRegion solution { 1, 5, 9,13}
  col2: UniqueRegion solution { 2, 6,10,14}
  col3: UniqueRegion solution { 3, 7,11,15}
  col4: UniqueRegion solution { 4, 8,12,16}
  box1: UniqueRegion solution { 1, 2, 5, 6}
  box2: UniqueRegion solution { 3, 4, 7, 8}
  box3: UniqueRegion solution { 9,10,13,14}
  box4: UniqueRegion solution {11,12,15,16}
  given3: solution 3 = Symbols.four
  given5: solution 5 = Symbols.four
  given7: solution 7 = Symbols.three
  given10: solution 10 = Symbols.four
  given12: solution 12 = Symbols.three
  given14: solution 14 = Symbols.one
  outside_grid: ∀ x, x = 0 ∨ x > 16 -> solution x = Symbols.one -- just need something to call default

-- 1 3 4 2
-- 4 2 3 1
-- 2 4 1 3
-- 3 1 2 4

theorem Solve
  {S : Set (Nat → Symbols)}
  (H : ∀ f, f ∈ S ↔ TestPuzzle f)     -- Hypothesis: All f in S are valid
  -- (H_bounds : ∀ f ∈ S, ∀ x, f x ∈ F x)  -- Hypothesis: S is a subset of what F allows
  -- (H_collapsed : ∀ x, ∃! d, d ∈ F x)    -- Hypothesis: F is fully solved (singletons)
  : ∃! (g: Nat -> Symbols), g ∈ S := by
  -- have c6n4: ∀ f ∈ S, f 6 ≠ Symbols.four := by
  --   intro f hf
  --   specialize H f hf
  --   rw [<- H.given5]
  --   apply H.row2.ne <;> simp
  have c6: ∀ f ∈ S, f 6 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 6 with
    | two => rfl
    | one => absurd h; rw [<- H.given14]; apply H.col2.ne <;> simp
    | three => absurd h; rw [<- H.given7]; apply H.row2.ne <;> simp
    | four => absurd h; rw [<- H.given5]; apply H.box1.ne <;> simp
  have c2: ∀ f ∈ S, f 2 = Symbols.three := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 2 with
    | three => rfl
    | one => absurd h; rw [<- H.given14]; apply H.col2.ne <;> simp
    | two => absurd h; rw [<- (c6 f hf)]; apply H.col2.ne <;> simp
    | four => absurd h; rw [<- H.given10]; apply H.col2.ne <;> simp
  have c1: ∀ f ∈ S, f 1 = Symbols.one := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 1 with
    | one => rfl
    | two => absurd h; rw [<- (c6 f hf)]; apply H.box1.ne <;> simp
    | three => absurd h; rw [<- (c2 f hf)]; apply H.box1.ne <;> simp
    | four => absurd h; rw [<- H.given5]; apply H.box1.ne <;> simp
  have c4: ∀ f ∈ S, f 4 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 4 with
    | two => rfl
    | one => absurd h; rw [<- (c1 f hf)]; apply H.row1.ne <;> simp
    | three => absurd h; rw [<- (c2 f hf)]; apply H.row1.ne <;> simp
    | four => absurd h; rw [<- H.given3]; apply H.row1.ne <;> simp
  have c8: ∀ f ∈ S, f 8 = Symbols.one := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 8 with
    | one => rfl
    | two => absurd h; rw [<- (c6 f hf)]; apply H.row2.ne <;> simp
    | three => absurd h; rw [<- H.given7]; apply H.row2.ne <;> simp
    | four => absurd h; rw [<- H.given5]; apply H.row2.ne <;> simp
  have c16: ∀ f ∈ S, f 16 = Symbols.four := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 16 with
    | four => rfl
    | one => absurd h; rw [<- (c8 f hf)]; apply H.col4.ne <;> simp
    | two => absurd h; rw [<- (c4 f hf)]; apply H.col4.ne <;> simp
    | three => absurd h; rw [<- H.given12]; apply H.col4.ne <;> simp
  have c15: ∀ f ∈ S, f 15 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 15 with
    | two => rfl
    | one => absurd h; rw [<- H.given14]; apply H.row4.ne <;> simp
    | three => absurd h; rw [<- H.given12]; apply H.box4.ne <;> simp
    | four => absurd h; rw [<- (c16 f hf)]; apply H.row4.ne <;> simp
  have c11: ∀ f ∈ S, f 11 = Symbols.one := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 11 with
    | one => rfl
    | two => absurd h; rw [<- (c15 f hf)]; apply H.box4.ne <;> simp
    | three => absurd h; rw [<- H.given12]; apply H.box4.ne <;> simp
    | four => absurd h; rw [<- (c16 f hf)]; apply H.box4.ne <;> simp
  have c9: ∀ f ∈ S, f 9 = Symbols.two := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 9 with
    | two => rfl
    | one => absurd h; rw [<- (c11 f hf)]; apply H.row3.ne <;> simp
    | three => absurd h; rw [<- H.given12]; apply H.row3.ne <;> simp
    | four => absurd h; rw [<- H.given10]; apply H.row3.ne <;> simp
  have c13: ∀ f ∈ S, f 13 = Symbols.three := by
    intro f hf
    replace H := (H f).mp hf
    cases h: f 13 with
    | three => rfl
    | one => absurd h; rw [<- H.given14]; apply H.box3.ne <;> simp
    | two => absurd h; rw [<- (c9 f hf)]; apply H.box3.ne <;> simp
    | four => absurd h; rw [<- H.given10]; apply H.box3.ne <;> simp
  let g : Nat → Symbols := fun x =>
  match x with
  | 1 => Symbols.one
  | 2 => Symbols.three
  | 3 => Symbols.four
  | 4 => Symbols.two
  | 5 => Symbols.four
  | 6 => Symbols.two
  | 7 => Symbols.three
  | 8 => Symbols.one
  | 9 => Symbols.two
  | 10 => Symbols.four
  | 11 => Symbols.one
  | 12 => Symbols.three
  | 13 => Symbols.three
  | 14 => Symbols.one
  | 15 => Symbols.two
  | 16 => Symbols.four
  | _ => Symbols.one -- here is the default
  use g
  constructor
  · simp only
    apply (H g).mpr
    constructor
    iterate 12 simp [UniqueRegion, Set.InjOn]
    iterate 6 simp [g]
    intro n hn
    unfold g
    split <;> try simp only [reduceCtorEq] <;> (absurd hn; decide)
  intro h hh
  ext x
  by_cases xin: x ∈ ({1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16}: Set Nat)
  · match x with
    | 1 => exact c1 h hh
    | 2 => exact c2 h hh
    | 3 => exact ((H h).mp hh).given3
    | 4 => exact c4 h hh
    | 5 => exact ((H h).mp hh).given5
    | 6 => exact c6 h hh
    | 7 => exact ((H h).mp hh).given7
    | 8 => exact c8 h hh
    | 9 => exact c9 h hh
    | 10 => exact ((H h).mp hh).given10
    | 11 => exact c11 h hh
    | 12 => exact ((H h).mp hh).given12
    | 13 => exact c13 h hh
    | 14 => exact ((H h).mp hh).given14
    | 15 => exact c15 h hh
    | 16 => exact c16 h hh
  replace H := (H h).mp hh
  rw [H.outside_grid]
  · unfold g
    split <;> try simp only [reduceCtorEq] <;> (absurd xin; decide)
  contrapose xin
  push_neg at xin
  cases xin
  interval_cases x
  · contradiction
  iterate 16 decide
