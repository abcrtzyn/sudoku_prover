import Mathlib.Data.Set.Defs
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Fincases
import Mathlib.Data.List.Nodup
import SudokuLean.Symbols4
import SudokuLean.Symbols9
-- import MathLib.Data.Finset.Defs
-- import Mathlib.Data.Finset.Dedup

set_option linter.style.whitespace false
set_option linter.style.longLine false


macro "split_disjunctive_4" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h)
macro "split_disjunctive_9" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h | $h | $h | $h)




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
theorem unique_region_same_bijection {α} [fa: Fintype α] {f: Nat -> α} {r: Set Nat} (h: UniqueRegion f r) (hs: r.ncard = Fintype.card α): Set.BijOn f r Set.univ := by
  constructor
  · simp [Set.MapsTo]
  constructor
  · apply h
  sorry


theorem injOn_by_card {α β} [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] :
  (s.toFinset.image f).card = s.toFinset.card → Set.InjOn f s := by
  intro h
  let h123 := Finset.card_image_iff.mp h
  simp only [Set.coe_toFinset] at h123
  exact h123



-- this theorem does some of the heavy lifting to use the above theorem
theorem unique_region_same_size_surjective {α} [Fintype α] {r: Set Nat} {f: Nat -> α} (unique_region: UniqueRegion f r) (card_same: r.ncard = Fintype.card α := by simp) (d: α): ∃ x ∈ r, f x = d := by
  have h: Set.SurjOn f r Set.univ := by
    apply Set.BijOn.surjOn
    refine unique_region_same_bijection unique_region ?_
    assumption
  unfold Set.SurjOn at h
  have h1: d ∈ f '' r := by
    apply h
    simp
  simp at h1
  assumption



-- when you hypothesize that f x = d and f y = d, where x and y are in the same region
-- this proves that false
theorem digit_in_region {α} {f: Nat -> α} {r: Set Nat} {d: α} {target: Nat} {conflict: Nat}
  (d_target: f target = d) (unique_region: UniqueRegion f r) (d_conflict: f conflict = d)
  (h4: target ≠ conflict := by decide) (h0: target ∈ r := by decide) (h1: conflict ∈ r := by decide): False := by
  absurd d_target
  rw [<- d_conflict]
  apply unique_region.ne <;> assumption

-- when you hypothesize that f x = d and f x = e, where d ≠ e
-- this proves that false
theorem digit_in_cell {α} {f: Nat -> α} {target: Nat} {d: α} {e: α}
  (target_d: f target = d) (target_e: f target = e) (h4: d ≠ e := by decide): False := by
  rw [target_d] at target_e
  contradiction

-- when there are two cells in region with the same candidates,
-- this is a structure to store that information
-- to make your life easier, keep c1 a lower index than c2 and d a lower symbols that e
structure Pair {α} {f: Nat -> α} {region: Set Nat} (unique_region: UniqueRegion f region)
  (c1 c2: Nat) (d e: α) where
  c1nc2: c1 ≠ c2
  c1_in_region: c1 ∈ region
  c2_in_region: c2 ∈ region
  dne: d ≠ e
  c1_possible: f c1 ∈ ({d,e}: Set α)
  c2_possible: f c2 ∈ ({d,e}: Set α)

-- if there is a pair in a region looking at a target cell in the region, the digit d is not in target.
-- useful theorem in order to not go through all the cases.
theorem Pair.in_region {α} {f: Nat -> α} {r} {c1 c2: Nat} {d e: α} {target: Nat} {s: α} (target_d: f target = s) (ur: UniqueRegion f r) (p: Pair ur c1 c2 d e)
  (target_r: target ∈ r := by decide) (target_n_c1: target ≠ c1 := by decide)
  (target_n_c2: target ≠ c2 := by decide) (s_is_in_pair: s ∈ ({d,e}: Set α):= by simp): False := by
  -- basically just have to show each of the cases.
  -- example in comments d = 1, e = 2
  cases s_is_in_pair with
  | inl td =>
    -- if target is 1
    rw [td] at target_d
    cases p.c1_possible with
    -- c1 can not be 1
    | inl c1d => refine digit_in_region target_d ur c1d target_n_c1 target_r p.c1_in_region
    -- c1 must be 2
    | inr c1e =>
      -- but then c2 must be 1
      have c2d: f c2 = d := by
        cases p.c2_possible with
        | inl c2d => assumption
        | inr c2e => exfalso; refine digit_in_region c1e ur c2e p.c1nc2 p.c1_in_region p.c2_in_region
      -- which doesn't work either
      refine digit_in_region target_d ur c2d target_n_c2 target_r p.c2_in_region
  | inr te =>
    -- if target is 2
    rw [te] at target_d
    cases p.c1_possible with
    -- c1 can not be 2
    | inr c1e => refine digit_in_region target_d ur c1e target_n_c1 target_r p.c1_in_region
    -- c1 must be 1
    | inl c1d =>
      -- but then c2 must be 2
      have c2d: f c2 = e := by
        cases p.c2_possible with
        | inr c2e => assumption
        | inl c2d => exfalso; refine digit_in_region c1d ur c2d p.c1nc2 p.c1_in_region p.c2_in_region
      -- which doesn't work either
      refine digit_in_region target_d ur c2d target_n_c2 target_r p.c2_in_region

-- the following are used to resolve pairs when you figure out one of the digits
-- there are 4 cases
theorem Pair.resolve_with_c1_d {α} {f: Nat -> α} {r: Set Nat} {c1 c2: Nat} {d e: α} {ur: UniqueRegion f r}:
  Pair ur c1 c2 d e -> f c1 = d -> f c2 = e := by
  intro p h1
  cases p.c2_possible with
  | inl h => exfalso; exact digit_in_region h1 ur h p.c1nc2 p.c1_in_region p.c2_in_region
  | inr h => assumption

theorem Pair.resolve_with_c1_e {α} {f: Nat -> α} {r: Set Nat} {c1 c2: Nat} {d e: α} {ur: UniqueRegion f r}:
  Pair ur c1 c2 d e -> f c1 = e -> f c2 = d := by
  intro p h1
  cases p.c2_possible with
  | inr h => exfalso; exact digit_in_region h1 ur h p.c1nc2 p.c1_in_region p.c2_in_region
  | inl h => assumption

theorem Pair.resolve_with_c2_d {α} {f: Nat -> α} {r: Set Nat} {c1 c2: Nat} {d e: α} {ur: UniqueRegion f r}:
  Pair ur c1 c2 d e -> f c2 = d -> f c1 = e := by
  intro p h1
  cases p.c1_possible with
  | inl h => exfalso; exact digit_in_region h ur h1 p.c1nc2 p.c1_in_region p.c2_in_region
  | inr h => assumption

theorem Pair.resolve_with_c2_e {α} {f: Nat -> α} {r: Set Nat} {c1 c2: Nat} {d e: α} {ur: UniqueRegion f r}:
  Pair ur c1 c2 d e -> f c2 = e -> f c1 = d := by
  intro p h1
  cases p.c1_possible with
  | inr h => exfalso; exact digit_in_region h ur h1 p.c1nc2 p.c1_in_region p.c2_in_region
  | inl h => assumption


theorem create_hidden_pair {α} {f: Nat -> α} {c1 c2: Nat} {d e: α} {r} (ur: UniqueRegion f r)
  (c1nc2: c1 ≠ c2 := by decide) (c1_in_region: c1 ∈ r := by decide) (c2_in_region: c2 ∈ r := by decide) (dne: d ≠ e := by decide):
  (f c1 = d ∨ f c2 = d) ∧ (f c1 = e ∨ f c2 = e) -> Pair ur c1 c2 d e := by
  intro h
  -- we have to take the hypothesis h and twist it
  have h1: (f c1 = d ∨ f c1 = e) ∧ (f c2 = d ∨ f c2 = e) := by
    -- the only way to do that is by trying all the cases
    -- yes, you could prove the conjunction seperately, but you would have to do the same cases both ways.
    cases h with | intro hd he
    cases hd with
    | inl c1d => cases he with
      | inl c1e => exfalso; exact digit_in_cell c1d c1e dne
      | inr c2e =>
        constructor
        · left; assumption
        · right; assumption
    | inr c2d => cases he with
      | inr c2e => exfalso; exact digit_in_cell c2d c2e dne
      | inl c1e =>
        constructor
        · right; assumption
        · left; assumption
  clear h
  cases h1 with | intro c1v c2v
  constructor
  repeat assumption

-- pointing pairs (box to line)
-- box/line reduction (line to box)
-- these occur where 2 or 3 cells in a region can be a value and the 2 cells are also in another region
-- example is best
-- c1 c2 are in box4 and row6,
-- in box4 the only places for D to go is in c1 or c2
-- then every cell in row6 that is not c1 or c2 is not D
-- pointing pair is the same as doing outer snyder marks

-- structure PointingPair {α} {f: Nat -> α} {region1: Set Nat} {region2: Set Nat}
--   (unique_region1: UniqueRegion f region1) (unique_region2: UniqueRegion f region2)
--   (c1 c2: Nat) (d: α) where
--   c1nc2: c1 ≠ c2
--   c1_in_region1: c1 ∈ region1
--   c2_in_region1: c2 ∈ region1
--   c1_in_region2: c1 ∈ region2
--   c2_in_region2: c2 ∈ region2
--   property: f c1 = d ∨ f c2 = d
