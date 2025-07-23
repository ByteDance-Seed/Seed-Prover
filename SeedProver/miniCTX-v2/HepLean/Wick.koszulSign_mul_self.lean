-- In HepLean/HepLean/PerturbationTheory/Koszul/KoszulSign.lean

/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Koszul.KoszulSignInsert
import HepLean.Mathematics.List.InsertionSort
/-!

# Koszul sign

-/

namespace Wick

open HepLean.List
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `- 1` for every fermion-fermion (`q` is `1`) crossing that occurs when sorting
  a list of based on `r`. -/
def koszulSign (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] :
    List 𝓕 → ℂ
  | [] => 1
  | a :: l => koszulSignInsert q le a l * koszulSign q le l

@[simp]
lemma koszulSign_singleton (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    koszulSign q le [φ] = 1 := by
  simp [koszulSign, koszulSignInsert]

/- Start of proof attempt -/
lemma round1_h1 (𝓕 : Type)
  (q : 𝓕 → FieldStatistic)
  (le : 𝓕 → 𝓕 → Prop)
  [DecidableRel le]:
  ∀ (a : 𝓕) (l : List 𝓕), koszulSignInsert q le a l * koszulSignInsert q le a l = 1 := by
  intro a l
  simp [mul_assoc]
  <;>
  (try simp [mul_comm]) <;>
  (try simp [mul_assoc]) <;>
  (try simp [mul_left_comm]) <;>
  aesop

theorem koszulSign_mul_self (l : List 𝓕) : koszulSign q le l * koszulSign q le l = 1  := by

  have h1 : ∀ (a : 𝓕) (l : List 𝓕), koszulSignInsert q le a l * koszulSignInsert q le a l = 1 := by
    exact round1_h1 𝓕 q le
  induction l with
  | nil =>
    simp [koszulSign]
  | cons a l ih =>
    have h2 : koszulSignInsert q le a l * koszulSignInsert q le a l = 1 := h1 a l
    calc
      koszulSign q le (a :: l) * koszulSign q le (a :: l)
        = (koszulSignInsert q le a l * koszulSign q le l) * (koszulSignInsert q le a l * koszulSign q le l) := by
          simp [koszulSign]
      _ = (koszulSignInsert q le a l * koszulSignInsert q le a l) * (koszulSign q le l * koszulSign q le l) := by ring
      _ = 1 * (koszulSign q le l * koszulSign q le l) := by rw [h2]
      _ = 1 := by rw [ih] <;> ring
