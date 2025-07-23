-- In HepLean/HepLean/PerturbationTheory/FieldOpFreeAlgebra/Grading.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
/-!

# Grading on the FieldOpFreeAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section

/-- The submodule of `FieldOpFreeAlgebra` spanned by lists of field statistic `f`. -/
def statisticSubmodule (f : FieldStatistic) : Submodule ℂ 𝓕.FieldOpFreeAlgebra :=
  Submodule.span ℂ {a | ∃ φs, a = ofCrAnListF φs ∧ (𝓕 |>ₛ φs) = f}

lemma ofCrAnListF_mem_statisticSubmodule_of (φs : List 𝓕.CrAnFieldOp) (f : FieldStatistic)
    (h : (𝓕 |>ₛ φs) = f) :
    ofCrAnListF φs ∈ statisticSubmodule f := by
  refine Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩

/- Start of proof attempt -/
lemma round1_h1 (𝓕 : FieldSpecification)
  (φs : List 𝓕.CrAnFieldOp):
  (𝓕 |>ₛ φs) = bosonic ∨ (𝓕 |>ₛ φs) = fermionic := by
  have h2 : (𝓕 |>ₛ φs) = bosonic ∨ (𝓕 |>ₛ φs) = fermionic := by
    cases h : (𝓕 |>ₛ φs) <;> simp
  exact h2

theorem ofCrAnListF_bosonic_or_fermionic (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListF φs ∈ statisticSubmodule bosonic ∨
    ofCrAnListF φs ∈ statisticSubmodule fermionic  := by

  have h1 := round1_h1 𝓕 φs
  cases h1 with
  | inl h1 =>
    -- Case 1: (𝓕 |>ₛ φs) = bosonic
    have h2 : ofCrAnListF φs ∈ statisticSubmodule bosonic := by
      exact ofCrAnListF_mem_statisticSubmodule_of φs bosonic h1
    exact Or.inl h2
  | inr h1 =>
    -- Case 2: (𝓕 |>ₛ φs) = fermionic
    have h2 : ofCrAnListF φs ∈ statisticSubmodule fermionic := by
      exact ofCrAnListF_mem_statisticSubmodule_of φs fermionic h1
    exact Or.inr h2
