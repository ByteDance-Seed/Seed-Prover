-- In HepLean/HepLean/PerturbationTheory/WickContraction/Singleton.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.SubContraction
/-!

# Singleton of contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra
open FieldStatistic

/-- The Wick contraction formed from a single ordered pair. -/
def singleton {i j : Fin n} (hij : i < j) : WickContraction n :=
  ⟨{{i, j}}, by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst hi
    rw [@Finset.card_eq_two]
    use i, j
    simp only [ne_eq, and_true]
    omega, by
    intro i hi j hj
    simp_all⟩

lemma mem_singleton {i j : Fin n} (hij : i < j) :
    {i, j} ∈ (singleton hij).1 := by
  simp [singleton]

lemma mem_singleton_iff {i j : Fin n} (hij : i < j) {a : Finset (Fin n)} :
    a ∈ (singleton hij).1 ↔ a = {i, j} := by
  simp [singleton]

/- Start of proof attempt -/
lemma round1_h1 (i j : Fin n)
  (hij : i < j)
  (a : (singleton hij).1):
  a.val = {i, j} := by
  have h2 : a.val ∈ (singleton hij).1 := a.property
  have h3 : a.val = {i, j} := by
    have h4 := (mem_singleton_iff hij).mp h2
    exact h4
  exact h3

theorem of_singleton_eq {i j : Fin n} (hij : i < j) (a : (singleton hij).1) :
    a = ⟨{i, j}, mem_singleton hij⟩  := by

  have h1 : a.val = {i, j} := by
    exact round1_h1 i j hij a
  apply Subtype.ext
  exact h1
