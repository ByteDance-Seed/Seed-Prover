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

/- Start of proof attempt -/
lemma round1_koszulSignInsert_empty (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    koszulSignInsert q le φ [] = 1 := by
  simp [koszulSignInsert]

theorem koszulSign_singleton (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    koszulSign q le [φ] = 1  := by

  simp [koszulSign, round1_koszulSignInsert_empty q le φ]
