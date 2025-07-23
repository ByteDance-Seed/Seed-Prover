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

theorem reduceOption_eq_singleton_iff (l : List (Option α)) (a : α) :
    l.reduceOption = [a] ↔ ∃ m n, l = replicate m none ++ some a :: replicate n none := by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_cons_iff] at h
    obtain ⟨l₁, _, l₂, h, hl₁, ⟨⟩, hl₂⟩ := h
    rw [filterMap_eq_nil_iff] at hl₂
    apply eq_replicate_of_mem at hl₁
    apply eq_replicate_of_mem at hl₂
    rw [h, hl₁, hl₂]
    use l₁.length, l₂.length
  · intro ⟨_, _, h⟩
    simp only [h, filterMap_append, filterMap_cons_some, filterMap_replicate_of_none, id_eq,
      nil_append, Option.some.injEq]

theorem reduceOption_eq_append_iff (l : List (Option α)) (l'₁ l'₂ : List α) :
    l.reduceOption = l'₁ ++ l'₂ ↔
      ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l'₁ ∧ l₂.reduceOption = l'₂ := by
  dsimp [reduceOption]
  constructor
  · intro h
    rw [filterMap_eq_append_iff] at h
    trivial
  · intro ⟨_, _, h, hl₁, hl₂⟩
    rw [h, filterMap_append, hl₁, hl₂]

/- Start of proof attempt -/
lemma round1_forward_direction (l : List (Option α)) (l' : List α) (a : α) (h : l.reduceOption = l'.concat a) :
    ∃ l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = [] := by
  have h1 : l.reduceOption = l' ++ [a] := by simpa [List.concat] using h
  have h2 : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = [a] := by
    rw [reduceOption_eq_append_iff] at h1
    exact h1
  rcases h2 with ⟨l₁, l₂, h21, h22, h23⟩
  have h3 : ∃ m n, l₂ = List.replicate m (none : Option α) ++ some a :: List.replicate n (none : Option α) := by
    have h4 : l₂.reduceOption = [a] := h23
    have h5 : l₂.reduceOption = [a] := h4
    have h6 : ∃ m n, l₂ = List.replicate m (none : Option α) ++ some a :: List.replicate n (none : Option α) := by
      have h7 : l₂.reduceOption = [a] := h5
      have h8 : l₂.reduceOption = [a] := h7
      rw [reduceOption_eq_singleton_iff] at h8
      rcases h8 with ⟨m, n, h9⟩
      refine' ⟨m, n, _⟩
      simpa using h9
    exact h6
  rcases h3 with ⟨m, n, h31⟩
  have h4 : l = (l₁ ++ List.replicate m (none : Option α)) ++ (some a :: List.replicate n (none : Option α)) := by
    calc
      l = l₁ ++ l₂ := h21
      _ = l₁ ++ (List.replicate m (none : Option α) ++ some a :: List.replicate n (none : Option α)) := by rw [h31]
      _ = (l₁ ++ List.replicate m (none : Option α)) ++ (some a :: List.replicate n (none : Option α)) := by
        simp [List.append_assoc]
        <;> aesop
  refine' ⟨l₁ ++ List.replicate m (none : Option α), List.replicate n (none : Option α), _ , _ , _⟩
  · -- Show l = (l₁ ++ List.replicate m (none : Option α)) ++ some a :: List.replicate n (none : Option α)
    have h5 : (l₁ ++ List.replicate m (none : Option α)) ++ (some a :: List.replicate n (none : Option α)) = l := by
      rw [h4]
    have h6 : (l₁ ++ List.replicate m (none : Option α)) ++ some a :: List.replicate n (none : Option α) = (l₁ ++ List.replicate m (none : Option α)) ++ (some a :: List.replicate n (none : Option α)) := by simp [List.append_assoc]
    rw [h6]
    exact h5.symm
  · -- Show (l₁ ++ List.replicate m (none : Option α)).reduceOption = l'
    have h5 : (l₁ ++ List.replicate m (none : Option α)).reduceOption = l₁.reduceOption ++ (List.replicate m (none : Option α)).reduceOption := by
      rw [reduceOption_append]
    have h6 : (List.replicate m (none : Option α)).reduceOption = [] := by
      simp [reduceOption_replicate_none]
    rw [h5, h6, List.append_nil]
    exact h22
  · -- Show (List.replicate n (none : Option α)).reduceOption = []
    simp [reduceOption_replicate_none]

lemma round1_backward_direction (l : List (Option α)) (l' : List α) (a : α) 
    (h : ∃ l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = []) :
    l.reduceOption = l'.concat a := by
  rcases h with ⟨l₁, l₂, h1, h2, h3⟩
  have h4 : l.reduceOption = (l₁ ++ (some a :: l₂)).reduceOption := by rw [h1]
  rw [h4]
  have h5 : (l₁ ++ (some a :: l₂)).reduceOption = l₁.reduceOption ++ (some a :: l₂).reduceOption := by
    rw [reduceOption_append]
  rw [h5]
  have h6 : (some a :: l₂).reduceOption = a :: l₂.reduceOption := by
    simp [reduceOption_cons_of_some]
  rw [h6]
  rw [h2]
  rw [h3]
  simp [List.concat]

theorem reduceOption_eq_concat_iff (l : List (Option α)) (l' : List α) (a : α) :
    l.reduceOption = l'.concat a ↔
      ∃ l₁ l₂, l = l₁ ++ some a :: l₂ ∧ l₁.reduceOption = l' ∧ l₂.reduceOption = []  := by

  constructor
  · exact round1_forward_direction l l' a
  · exact round1_backward_direction l l' a
