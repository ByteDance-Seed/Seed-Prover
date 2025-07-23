-- In HepLean/HepLean/PerturbationTheory/FieldOpAlgebra/NormalOrder/Lemmas.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.NormalOrder.Basic
/-!

# Basic properties of normal ordering

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-!

## Properties of normal ordering.

-/

lemma normalOrder_eq_ι_normalOrderF (a : 𝓕.FieldOpFreeAlgebra) :
    𝓝(ι a) = ι 𝓝ᶠ(a) := rfl

lemma normalOrder_ofCrAnList (φs : List 𝓕.CrAnFieldOp) :
    𝓝(ofCrAnList φs) = normalOrderSign φs • ofCrAnList (normalOrderList φs) := by
  rw [ofCrAnList, normalOrder_eq_ι_normalOrderF, normalOrderF_ofCrAnListF]
  rfl

@[simp]
lemma normalOrder_one_eq_one : normalOrder (𝓕 := 𝓕) 1 = 1 := by
  have h1 : 1 = ofCrAnList (𝓕 := 𝓕) [] := by simp [ofCrAnList]
  rw [h1]
  rw [normalOrder_ofCrAnList]
  simp

@[simp]
lemma normalOrder_ofFieldOpList_nil : normalOrder (𝓕 := 𝓕) (ofFieldOpList []) = 1 := by
  rw [ofFieldOpList]
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [ofFieldOpListF_nil]
  change normalOrder (𝓕 := 𝓕) 1 = _
  simp

@[simp]
lemma normalOrder_ofCrAnList_nil : normalOrder (𝓕 := 𝓕) (ofCrAnList []) = 1 := by
  rw [normalOrder_ofCrAnList]
  simp only [normalOrderSign_nil, normalOrderList_nil, one_smul]
  rfl

lemma ofCrAnList_eq_normalOrder (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnList (normalOrderList φs) = normalOrderSign φs • 𝓝(ofCrAnList φs) := by
  rw [normalOrder_ofCrAnList, smul_smul, normalOrderSign, Wick.koszulSign_mul_self,
    one_smul]

lemma normalOrder_normalOrder_mid (a b c : 𝓕.FieldOpAlgebra) :
    𝓝(a * b * c) = 𝓝(a * 𝓝(b) * c) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [← map_mul]
  rw [normalOrder_eq_ι_normalOrderF]
  rw [normalOrderF_normalOrderF_mid]
  rfl

/- Start of proof attempt -/
lemma round1_normalOrder_normalOrder_left (a b : 𝓕.FieldOpAlgebra) :
    𝓝(a * b) = 𝓝(𝓝(a) * b) := by
  have h := normalOrder_normalOrder_mid (1 : 𝓕.FieldOpAlgebra) a b
  simp at h
  exact h

theorem normalOrder_normalOrder_left (a b : 𝓕.FieldOpAlgebra) :
    𝓝(a * b) = 𝓝(𝓝(a) * b)  := by

  exact round1_normalOrder_normalOrder_left a b
