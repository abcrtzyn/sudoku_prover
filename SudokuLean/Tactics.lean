import Mathlib.Data.Set.Defs

set_option linter.style.whitespace false


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
