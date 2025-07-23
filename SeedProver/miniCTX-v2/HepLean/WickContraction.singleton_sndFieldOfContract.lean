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

lemma of_singleton_eq {i j : Fin n} (hij : i < j) (a : (singleton hij).1) :
    a = ⟨{i, j}, mem_singleton hij⟩ := by
  have ha2 := a.2
  rw [@mem_singleton_iff] at ha2
  exact Subtype.coe_eq_of_eq_mk ha2

lemma singleton_prod {φs : List 𝓕.FieldOp} {i j : Fin φs.length} (hij : i < j)
    (f : (singleton hij).1 → M) [CommMonoid M] :
    ∏ a, f a = f ⟨{i,j}, mem_singleton hij⟩:= by
  simp [singleton, of_singleton_eq]

@[simp]
lemma singleton_fstFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).fstFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = i := by
  refine eq_fstFieldOfContract_of_mem (singleton hij) ⟨{i, j}, mem_singleton hij⟩ i j ?_ ?_ ?_
  · simp
  · simp
  · exact hij

/- Start of proof attempt -/
lemma round1_singleton_sndFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).sndFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = j  := by
  refine eq_sndFieldOfContract_of_mem (singleton hij) ⟨{i, j}, mem_singleton hij⟩ i j (by simp) (by simp) hij

theorem singleton_sndFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).sndFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = j  := by

  exact round1_singleton_sndFieldOfContract hij
