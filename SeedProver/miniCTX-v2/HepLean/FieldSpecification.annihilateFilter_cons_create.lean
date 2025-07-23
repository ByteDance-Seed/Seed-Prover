-- In HepLean/HepLean/PerturbationTheory/FieldSpecification/Filters.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.CrAnFieldOp
/-!

# Filters of lists of CrAnFieldOp

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-- Given a list of creation and annihilation states, the filtered list only containing
  the creation states. As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1c, φ2c]`.
-/
def createFilter (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.filter (fun φ => 𝓕 |>ᶜ φ = CreateAnnihilate.create) φs

lemma createFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    createFilter (φ :: φs) = φ :: createFilter φs := by
  simp only [createFilter]
  rw [List.filter_cons_of_pos]
  simp [hφ]

lemma createFilter_cons_annihilate {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    createFilter (φ :: φs) = createFilter φs := by
  simp only [createFilter]
  rw [List.filter_cons_of_neg]
  simp [hφ]

lemma createFilter_append (φs φs' : List 𝓕.CrAnFieldOp) :
    createFilter (φs ++ φs') = createFilter φs ++ createFilter φs' := by
  rw [createFilter, List.filter_append]
  rfl

lemma createFilter_singleton_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) :
    createFilter [φ] = [φ] := by
  simp [createFilter, hφ]

lemma createFilter_singleton_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) : createFilter [φ] = [] := by
  simp [createFilter, hφ]

/-- Given a list of creation and annihilation states, the filtered list only containing
  the annihilation states.
  As a schematic example, for the list:
  - `[φ1c, φ1a, φ2c, φ2a]` this will return `[φ1a, φ2a]`.
-/
def annihilateFilter (φs : List 𝓕.CrAnFieldOp) : List 𝓕.CrAnFieldOp :=
  List.filter (fun φ => 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) φs

/- Start of proof attempt -/
lemma round1_annihilateFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φ :: φs) = annihilateFilter φs  := by
  simp only [annihilateFilter]
  simp [List.filter, hφ]
  <;> aesop

theorem annihilateFilter_cons_create {φ : 𝓕.CrAnFieldOp}
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    annihilateFilter (φ :: φs) = annihilateFilter φs  := by

  exact round1_annihilateFilter_cons_create hφ φs
