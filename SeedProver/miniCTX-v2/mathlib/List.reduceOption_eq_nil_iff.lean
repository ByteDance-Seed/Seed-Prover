-- In mathlib/Mathlib/Data/List/ReduceOption.lean

/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Anthony DeRossi
-/
import Mathlib.Data.List.Basic

/-!
# Properties of `List.reduceOption`

In this file we prove basic lemmas about `List.reduceOption`.
-/

namespace List

variable {α β : Type*}

@[simp]
theorem reduceOption_cons_of_some (x : α) (l : List (Option α)) :
    reduceOption (some x :: l) = x :: l.reduceOption := by
  simp only [reduceOption, filterMap, id, eq_self_iff_true, and_self_iff]

@[simp]
theorem reduceOption_cons_of_none (l : List (Option α)) :
    reduceOption (none :: l) = l.reduceOption := by simp only [reduceOption, filterMap, id]

@[simp]
theorem reduceOption_nil : @reduceOption α [] = [] :=
  rfl

@[simp]
theorem reduceOption_map {l : List (Option α)} {f : α → β} :
    reduceOption (map (Option.map f) l) = map f (reduceOption l) := by
  induction' l with hd tl hl
  · simp only [reduceOption_nil, map_nil]
  · cases hd <;>
      simpa [Option.map_some', map, eq_self_iff_true, reduceOption_cons_of_some] using hl

theorem reduceOption_append (l l' : List (Option α)) :
    (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption :=
  filterMap_append l l' id

@[simp]
theorem reduceOption_replicate_none {n : ℕ} : (replicate n (@none α)).reduceOption = [] := by
  dsimp [reduceOption]
  rw [filterMap_replicate_of_none]
  rfl

/- Start of proof attempt -/
lemma round1_forward_direction (l : List (Option α)) (h : l.reduceOption = []) : ∃ n, l = replicate n none := by
  induction l with
  | nil =>
    refine ⟨0, by simp⟩
  | cons hd tl ih =>
    cases hd with
    | none =>
      have h1 : tl.reduceOption = [] := by simpa using h
      rcases ih h1 with ⟨n, h2⟩
      refine ⟨n + 1, ?_⟩
      simp [h2]
      <;> aesop
    | some x =>
      simp [reduceOption] at h
      <;> aesop

lemma round1_backward_direction (l : List (Option α)) (h : ∃ n, l = replicate n none) : l.reduceOption = [] := by
  rcases h with ⟨n, hn⟩
  have h1 : ∀ n, (replicate n (none : Option α)).reduceOption = [] := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp [replicate, ih, reduceOption_cons_of_none]
      <;> aesop
  rw [hn]
  exact h1 n

theorem reduceOption_eq_nil_iff (l : List (Option α)) :
    l.reduceOption = [] ↔ ∃ n, l = replicate n none  := by

  constructor
  · exact round1_forward_direction l
  · exact round1_backward_direction l
