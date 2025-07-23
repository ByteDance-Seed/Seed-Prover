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

lemma ofCrAnListF_bosonic_or_fermionic (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListF φs ∈ statisticSubmodule bosonic ∨
    ofCrAnListF φs ∈ statisticSubmodule fermionic := by
  by_cases h : (𝓕 |>ₛ φs) = bosonic
  · left
    exact ofCrAnListF_mem_statisticSubmodule_of φs bosonic h
  · right
    exact ofCrAnListF_mem_statisticSubmodule_of φs fermionic (by simpa using h)

lemma ofCrAnOpF_bosonic_or_fermionic (φ : 𝓕.CrAnFieldOp) :
    ofCrAnOpF φ ∈ statisticSubmodule bosonic ∨ ofCrAnOpF φ ∈ statisticSubmodule fermionic := by
  rw [← ofCrAnListF_singleton]
  exact ofCrAnListF_bosonic_or_fermionic [φ]

/-- The projection of an element of `FieldOpFreeAlgebra` onto it's bosonic part. -/
def bosonicProjF : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] statisticSubmodule (𝓕 := 𝓕) bosonic :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  if h : (𝓕 |>ₛ φs) = bosonic then
    ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩
  else
    0

lemma bosonicProjF_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    bosonicProjF (ofCrAnListF φs) = if h : (𝓕 |>ₛ φs) = bosonic then
      ⟨ofCrAnListF φs, Submodule.mem_span.mpr fun _ a => a ⟨φs, ⟨rfl, h⟩⟩⟩ else 0 := by
  conv_lhs =>
    rw [← ofListBasis_eq_ofList, bosonicProjF, Basis.constr_basis]

lemma bosonicProjF_of_mem_bosonic (a : 𝓕.FieldOpFreeAlgebra) (h : a ∈ statisticSubmodule bosonic) :
    bosonicProjF a = ⟨a, h⟩ := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule bosonic) : Prop :=
    bosonicProjF a = ⟨a, hx⟩
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, bosonicProjF_ofCrAnListF, h]
  · simp only [map_zero, p]
    rfl
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

lemma bosonicProjF_of_mem_fermionic (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ statisticSubmodule fermionic) :
    bosonicProjF a = 0 := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (hx : a ∈ statisticSubmodule fermionic) : Prop :=
    bosonicProjF a = 0
  change p a h
  apply Submodule.span_induction
  · intro x hx
    simp only [Set.mem_setOf_eq] at hx
    obtain ⟨φs, rfl, h⟩ := hx
    simp [p, bosonicProjF_ofCrAnListF, h]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
  · intro a x hx hy
    simp_all [p]

@[simp]
lemma bosonicProjF_of_bonosic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProjF (a bosonic) = a bosonic := by
  apply bosonicProjF_of_mem_bosonic

/- Start of proof attempt -/
lemma round1_bosonicProjF_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProjF (a fermionic).1 = 0  := by
  have h1 : (a fermionic).1 ∈ statisticSubmodule fermionic := (a fermionic).2
  exact bosonicProjF_of_mem_fermionic ((a fermionic).1) h1

theorem bosonicProjF_of_fermionic_part
    (a : DirectSum FieldStatistic (fun i => (statisticSubmodule (𝓕 := 𝓕) i))) :
    bosonicProjF (a fermionic).1 = 0  := by

  exact round1_bosonicProjF_of_fermionic_part a
