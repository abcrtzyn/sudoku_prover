import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

set_option linter.style.whitespace false
set_option linter.style.longLine false


-- This file contains definitions of common solving techniques and constraints
-- UniqueSet: f is an injection from {cells}
-- SupportSet: f is a surjection from {cells} to {digits}
-- LockedSet: f is a bijection from {cells} to {digits}


-- TODO there are lots of naming conventions I am not following and could easily be following
-- I need to get on those before my puzzles get more prevalent.


-- Unique Region says that each digit in that region is different
-- Regions are allowed to be smaller than the size of the grid
def UniqueSet {α} (f: Nat -> α) (r: Set Nat) :=  Set.InjOn f r




-- used to prove unique regions at the end of the puzzle.
-- if the cardinality of the f image and set are the same, then injectivity is true.
theorem injOn_by_card {α β} [DecidableEq β] (f : α → β) (s : Set α) [Fintype s] :
  (s.toFinset.image f).card = s.toFinset.card → Set.InjOn f s := by
  intro h
  let h123 := Finset.card_image_iff.mp h
  simp only [Set.coe_toFinset] at h123
  exact h123



-- when you hypothesize that f x = d and f y = d, where x and y are in the same region
-- this proves that false
theorem digit_in_region {α} {f: Nat -> α} {r: Set Nat} {d: α} {target: Nat} {conflict: Nat}
  (d_target: f target = d) (unique_region: UniqueSet f r) (d_conflict: f conflict = d)
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



-- pointing pairs (box to line)
-- box/line reduction (line to box)
-- these occur where 2 or 3 cells in a region can be a value and the 2 cells are also in another region
-- example is best
-- c1 c2 are in box4 and row6,
-- in box4 the only places for D to go is in c1 or c2
-- then every cell in row6 that is not c1 or c2 is not D
-- pointing pair is the same as doing outer snyder marks
-- any to cells can be a pointing pair, as long as you prove the property

def SupportSet {α} (f: Nat -> α) (cells: Set Nat) (d: α) := Set.SurjOn f cells {d}

-- a theorem to show that the pair is in the support set
theorem in_support_set {α} {f: Nat -> α} {cells: Set Nat} {x: Nat} {d: α}
  (h: f x = d) (h1: x ∈ cells := by decide): SupportSet f cells d := by
  unfold SupportSet; simp only [Set.surjOn_singleton, Set.mem_image]; exact ⟨_, h1, h⟩



-- pointing set in region
-- used to rule out a digit in a cell because a pointing set is in that region
theorem support_set_in_region {α} {f: Nat -> α} {r} {S: Set Nat} {target: Nat} {s: α}
  (target_d: f target = s) (ur: UniqueSet f r) (p: SupportSet f S s) (sr: S ⊆ r := by simp [Set.subset_def])
  (target_r: target ∈ r := by decide) (target_nin_set: target ∉ S := by decide): False := by
  -- not even a cases proof, the power of sets for the win.
  simp! [SupportSet] at p
  rcases p with ⟨c1, ⟨c1S, c1v⟩⟩
  have this: target ≠ c1 := by
    intro h
    rw [h] at target_nin_set
    contradiction
  refine digit_in_region target_d ur c1v this target_r (sr c1S)


-- if f c ≠ d and c in cells, create a new support set without that one
-- I suspect this is not the best way to write this theorem, something that I can apply and then prove target_d is likely preferable
-- target is not required to be in the set cells for the theorem, but it is neccesary to be useful.
theorem support_set_reduce {α} {f: Nat -> α} (cells: Set Nat) (d: α) (p: SupportSet f cells d) {target: Nat}
  (target_d: f target ≠ d): SupportSet f (cells \ {target}) d := by
  simp! [SupportSet] at p
  rcases p with ⟨x,⟨x_cells,h⟩⟩
  simp! [SupportSet]
  exists x
  split_ands
  · exact x_cells
  · contrapose target_d
    rw [<- target_d]; exact h
  · exact h


-- locked set are pairs where 2 cells contain the same 2 candidates in the same region.
-- they can be found by having 2 cells with 2 candidates or support sets on the same cells with different digits.

def LockedSet {α} (f: Nat -> α) (cells: Set Nat) (digits: Set α) := Set.BijOn f cells digits


-- does not matter which region that is used, as long at it has injectivity.
-- We need to know that these 2 cells have to be different for some reason
theorem locked_set_from_naked_set {α} {f: Nat -> α} {cells: Set Nat} {digits: Set α} {region: Set Nat}
  (ur: UniqueSet f region)
  (naked_prop: ∀ c ∈ cells, f c ∈ digits)
  (cells_in_region: cells ⊆ region := by simp [Set.subset_def])
  (sized: cells.ncard = digits.ncard := by simp):
  LockedSet f cells digits := by
  -- we have to use this twice, might as well have it now
  have subinjection: Set.InjOn f cells := Set.InjOn.mono cells_in_region ur
  constructor
  · exact naked_prop
  constructor
  · apply subinjection
  · sorry -- need some lemma that says if magnitudes are the same and injection, good


theorem locked_set_from_hidden_set {α} {f: Nat -> α} {cells: Set Nat} {digits: Set α} {region: Set Nat}
  (ur: UniqueSet f region) (hidden_prop: ∀ d ∈ digits, ∃ c ∈ cells, f c = d)
  (cells_in_region: cells ⊆ region := by simp [Set.subset_def]) (sized: cells.ncard = digits.ncard := by simp):
  LockedSet f cells digits := by
  have subinjection: Set.InjOn f cells := Set.InjOn.mono cells_in_region ur
  sorry


-- in a surrounding region, remove digits from those cells
theorem locked_set_in_region {α} {f: Nat -> α} {cells: Set Nat} {digits: Set α}
  {target: Nat} {s: α}
  (target_s: f target = s)
  {region: Set Nat} (ur: UniqueSet f region)
  (bij: LockedSet f cells digits)
  (cells_in_region: cells ⊆ region := by simp [Set.subset_def])
  (s_in_digits: s ∈ digits := by decide)
  (target_r: target ∈ region := by decide)
  (target_nin_set: target ∉ cells := by decide):
  False := by
  apply bij.surjOn at s_in_digits
  simp only [Set.mem_image] at s_in_digits
  rcases s_in_digits with ⟨x, ⟨xc, xf⟩⟩
  rw [<- target_s] at xf
  apply ur (cells_in_region xc) (target_r) at xf
  rw [xf] at xc
  contradiction

-- in a surrounding region, remove digits from those cells
theorem locked_set_in_cell {α} {f: Nat -> α} {cells: Set Nat} {digits: Set α}
  {target: Nat} {s: α}
  (target_s: f target = s)
  (bij: LockedSet f cells digits)
  (s_nin_digits: s ∉ digits := by decide)
  (target_in_set: target ∈ cells := by decide):
  False := by
  absurd s_nin_digits
  apply (target_s ▸ (bij.mapsTo target_in_set))

theorem locked_set_reducton {α} {f: Nat -> α} {cells: Set Nat} {digits: Set α}
  (bij: LockedSet f cells digits)
  {c: Nat} {d: α}
  (h_found : f c = d)
  (hc: c ∈ cells := by decide):
  LockedSet f (cells \ {c}) (digits \ {d}) := by
  rcases bij with ⟨maps, ⟨inj, surj⟩⟩
  constructor
  · intro x xc
    cases xc with | intro h1 not_c
    constructor
    · apply maps
      apply h1
    · contrapose not_c
      rw [<- h_found] at not_c
      apply inj h1 hc not_c
  constructor
  · intro x1 ⟨x1_cells, x1_notc⟩ x2 ⟨x2_cells, x2_notc⟩
    apply inj x1_cells x2_cells
  · intro y ⟨y_digits, y_notd⟩
    specialize surj y_digits
    simp only [Set.mem_image] at surj
    rcases surj with ⟨x, ⟨xh, xh1⟩⟩
    exists x
    constructor
    · constructor
      · apply xh
      · contrapose y_notd
        rw [<- y_notd] at h_found
        rw [xh1] at h_found
        apply h_found
    · apply xh1

-- @[simp]
theorem locked_set_single {α} {f: Nat -> α} {c: Nat} {d: α}:
  LockedSet f {c} {d} -> f c = d := by
  simp only [LockedSet, Set.bijOn_singleton]
  tauto


theorem support_set_from_locked_set {α} {f: Nat -> α} {cells: Set Nat} {digits: Set α}
  (ls: LockedSet f cells digits) (d: α) (d_in_digits: d ∈ digits := by simp):
  SupportSet f cells d := ls.surjOn.mono (Set.Subset.refl _) (Set.singleton_subset_iff.mpr d_in_digits)

-- this theorem specifically applies the locked set principle to a region that is the full set of digits of 1 to 9
theorem region_full_locked_set {α} [Fintype α] {r: Set Nat} {f: Nat -> α}
  (unique_region: UniqueSet f r) (card_same: r.ncard = Fintype.card α := by simp):
  LockedSet f r Set.univ := by
  refine locked_set_from_naked_set unique_region ?_ ?_ ?_
  · simp only [Set.mem_univ, implies_true]
  · simp only [subset_refl]
  · simp only [Set.ncard_univ, Nat.card_eq_fintype_card]
    assumption


-- this section is fishy...as in x wings, swordfish, jellyfish
-- multi-support sets.
-- for a digit d, given a support set in region A and region B (A and B are disjoint),
-- if all cells in all support sets are in regions C, it creates support sets in regions C
-- eventually, I want this to be set logic, but I am starting with numeric cases

-- theorem xwing {α} {f: Nat -> α} (d: α) {B1 B2: Set Nat} {C1 C2: Set Nat}
--   (disjoint: B1 ∩ B2 = ∅)
--   (urb1: UniqueSet f B1) (urb2: UniqueSet f B2)
--   (urc1: UniqueSet f C1) (urc2: UniqueSet f C2)

--   (ss1: SupportSet f cells1 d) (ss1ss: cells1 ⊆ B1)
--   (ss2: SupportSet f cells2 d) (ss2ss: cells2 ⊆ B2)
