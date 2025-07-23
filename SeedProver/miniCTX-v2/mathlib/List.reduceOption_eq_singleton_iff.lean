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

theorem reduceOption_eq_nil_iff (l : List (Option α)) :
    l.reduceOption = [] ↔ ∃ n, l = replicate n none := by
  dsimp [reduceOption]
  rw [filterMap_eq_nil_iff]
  constructor
  · intro h
    exact ⟨l.length, eq_replicate_of_mem h⟩
  · intro ⟨_, h⟩
    simp_rw [h, mem_replicate]
    tauto

/- Start of proof attempt -/
lemma round1_backward_direction (l : List (Option α)) (a : α) (m n : ℕ) 
    (h : l = List.replicate m none ++ (some a :: List.replicate n none)) : 
    l.reduceOption = [a] := by
  rw [h]
  simp [List.reduceOption, List.filterMap, List.append_assoc, List.reduceOption_append, 
        List.reduceOption_replicate_none, List.reduceOption_cons_of_some]
  <;> aesop

lemma round1_forward_direction (l : List (Option α)) (a : α) 
    (h : l.reduceOption = [a]) : 
    ∃ m n, l = List.replicate m none ++ (some a :: List.replicate n none) := by
  induction l with
  | nil =>
    simp [List.reduceOption_nil] at h
    <;> contradiction
  | cons hd tl ih =>
    by_cases h2 : hd = none
    · -- Case 1: `hd = none`
      have h21 : hd = none := h2
      have h3 : (hd :: tl).reduceOption = tl.reduceOption := by
        rw [h21]
        simp [List.reduceOption_cons_of_none]
      rw [h3] at h
      have ih' := ih h
      rcases ih' with ⟨m, n, h4⟩
      refine ⟨m + 1, n,?_⟩
      simp [h21, h4, List.replicate_succ, List.cons_append]
      <;> aesop
    · -- Case 2: `hd ≠ none`
      have h22 : ∃ x : α, hd = some x := by
        cases hd with
        | none => contradiction
        | some x => exact ⟨x, rfl⟩
      rcases h22 with ⟨x, hx⟩
      have h3 : (hd :: tl).reduceOption = x :: tl.reduceOption := by
        rw [hx]
        simp [List.reduceOption_cons_of_some]
        <;> aesop
      rw [h3] at h
      have h5 : x = a := by
        simp [List.cons.injEq] at h
        <;> tauto
      have h6 : tl.reduceOption = [] := by
        simp [List.cons.injEq] at h
        <;> tauto
      have h7 : ∃ n, tl = List.replicate n none := by
        rw [List.reduceOption_eq_nil_iff] at h6
        rcases h6 with ⟨n, h6⟩
        refine ⟨n,?_⟩
        tauto
      rcases h7 with ⟨n, h8⟩
      have h9 : hd = some a := by
        rw [hx, h5]
      refine ⟨0, n,?_⟩
      simp [h9, h8]
      <;> aesop

theorem reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) :
    l.reduceOption = [a] ↔ ∃ m n, l = replicate m none ++ some a :: replicate n none  := by

  constructor
  · exact round1_forward_direction l a
  · rintro ⟨m, n, h⟩
    exact round1_backward_direction l a m n h
