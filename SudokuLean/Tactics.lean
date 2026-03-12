import Mathlib.Data.Set.Defs
import Mathlib.Tactic.FinCases
import SudokuLean.Basic

set_option linter.style.whitespace false

macro "split_disjunctive_2" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h)
macro "split_disjunctive_3" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h)
macro "split_disjunctive_4" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h)
macro "split_disjunctive_5" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h)
macro "split_disjunctive_6" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h)
macro "split_disjunctive_7" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h | $h)
macro "split_disjunctive_8" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h | $h | $h)
macro "split_disjunctive_9" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h | $h | $h | $h)
macro "split_disjunctive_10" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h | $h | $h | $h | $h)
macro "split_disjunctive_11" h:ident : tactic =>
  `(tactic| rcases $h:ident with $h | $h | $h | $h | $h | $h | $h | $h | $h | $h | $h)


macro "split_disjunctive_try" h:ident : tactic => `(tactic| (
  first
    | split_disjunctive_11 $h
    | split_disjunctive_10 $h
    | split_disjunctive_9 $h
    | split_disjunctive_8 $h
    | split_disjunctive_7 $h
    | split_disjunctive_6 $h
    | split_disjunctive_5 $h
    | split_disjunctive_4 $h
    | split_disjunctive_3 $h
    | split_disjunctive_2 $h
    | skip -- In case it's a singleton, h is already f x = d
))

macro "support_cases" h:ident : tactic => `(tactic| (
  simp only [SupportSet, Set.SurjOn, Set.singleton_subset_iff, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq, true_and] at $h:ident
  split_disjunctive_try $h
))

macro "locked_support_cases" h:ident n:term : tactic => `(tactic| (
  replace $h := support_set_from_locked_set $h $n
  simp only [SupportSet, Set.SurjOn, Set.singleton_subset_iff, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, exists_eq_or_imp, ↓existsAndEq, true_and] at $h:ident
  split_disjunctive_try $h
))

macro "locked_maps_cases" h:ident n:term : tactic => `(tactic| (
  replace $h := Set.BijOn.mapsTo $h (x:=$n) (by decide)
  split_disjunctive_try $h
))



def IsSound {α} (S : Set (Nat → α)) (facts : List (Nat × α)) : Prop :=
  ∀ (c : Nat) (d : α), (c, d) ∈ facts → ∀ f ∈ S, f c = d


theorem add_fact {α} {S} {facts : List (Nat × α)} (h_sound : IsSound S facts)
  (c : Nat) (d : α) (h_new : ∀ f ∈ S, f c = d) : IsSound S ((c, d) :: facts) := by
  intro c' d' h_mem f hf
  cases h_mem with
  | head => exact h_new f hf
  | tail _ h_old => exact h_sound c' d' h_old f hf

macro "is_in_list" : tactic => `(tactic| (
  repeat (first | apply List.Mem.head | apply List.Mem.tail)
))

theorem get_d {α} {S} {facts: List (Nat × α)}
  (h_sound : IsSound S facts) (c : Nat) (d : α)
  (h_in : (c, d) ∈ facts := by is_in_list) :
  ∀ f ∈ S, f c = d :=
by
  exact h_sound c d h_in
