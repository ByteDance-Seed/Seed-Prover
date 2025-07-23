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

lemma normalOrder_normalOrder_left (a b : 𝓕.FieldOpAlgebra) :
    𝓝(a * b) = 𝓝(𝓝(a) * b) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [← map_mul]
  rw [normalOrder_eq_ι_normalOrderF]
  rw [normalOrderF_normalOrderF_left]
  rfl

lemma normalOrder_normalOrder_right (a b : 𝓕.FieldOpAlgebra) :
    𝓝(a * b) = 𝓝(a * 𝓝(b)) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [normalOrder_eq_ι_normalOrderF]
  simp only [← map_mul]
  rw [normalOrder_eq_ι_normalOrderF]
  rw [normalOrderF_normalOrderF_right]
  rfl

lemma normalOrder_normalOrder (a : 𝓕.FieldOpAlgebra) : 𝓝(𝓝(a)) = 𝓝(a) := by
  trans 𝓝(𝓝(a) * 1)
  · simp
  · rw [← normalOrder_normalOrder_left]
    simp

/-!

## mul anpart and crpart
-/

lemma normalOrder_mul_anPart (φ : 𝓕.FieldOp) (a : 𝓕.FieldOpAlgebra) :
    𝓝(a * anPart φ) = 𝓝(a) * anPart φ := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  rw [anPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_mul_anPartF]
  rfl

lemma crPart_mul_normalOrder (φ : 𝓕.FieldOp) (a : 𝓕.FieldOpAlgebra) :
    𝓝(crPart φ * a) = crPart φ * 𝓝(a) := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  rw [crPart, ← map_mul, normalOrder_eq_ι_normalOrderF, normalOrderF_crPartF_mul]
  rfl

/-!

### Normal order and super commutes

-/

/-- For a field specification `𝓕`, and `a` and `b` in `𝓕.FieldOpAlgebra` the normal ordering
  of the super commutator of `a` and `b` vanishes, i.e. `𝓝([a,b]ₛ) = 0`. -/
@[simp]
lemma normalOrder_superCommute_eq_zero (a b : 𝓕.FieldOpAlgebra) :
    𝓝([a, b]ₛ) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [superCommute_eq_ι_superCommuteF, normalOrder_eq_ι_normalOrderF]
  simp

@[simp]
lemma normalOrder_superCommute_left_eq_zero (a b c: 𝓕.FieldOpAlgebra) :
    𝓝([a, b]ₛ * c) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [superCommute_eq_ι_superCommuteF, ← map_mul, normalOrder_eq_ι_normalOrderF]
  simp

@[simp]
lemma normalOrder_superCommute_right_eq_zero (a b c: 𝓕.FieldOpAlgebra) :
    𝓝(c * [a, b]ₛ) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  rw [superCommute_eq_ι_superCommuteF, ← map_mul, normalOrder_eq_ι_normalOrderF]
  simp

@[simp]
lemma normalOrder_superCommute_mid_eq_zero (a b c d : 𝓕.FieldOpAlgebra) :
    𝓝(a * [c, d]ₛ * b) = 0 := by
  obtain ⟨a, rfl⟩ := ι_surjective a
  obtain ⟨b, rfl⟩ := ι_surjective b
  obtain ⟨c, rfl⟩ := ι_surjective c
  obtain ⟨d, rfl⟩ := ι_surjective d
  rw [superCommute_eq_ι_superCommuteF, ← map_mul, ← map_mul, normalOrder_eq_ι_normalOrderF]
  simp

/-!

### Swapping terms in a normal order.

-/

lemma normalOrder_ofFieldOp_ofFieldOp_swap (φ φ' : 𝓕.FieldOp) :
    𝓝(ofFieldOp φ * ofFieldOp φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝(ofFieldOp φ' * ofFieldOp φ) := by
  rw [ofFieldOp_mul_ofFieldOp_eq_superCommute]
  simp

lemma normalOrder_ofCrAnOp_ofCrAnList (φ : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) : 𝓝(ofCrAnOp φ * ofCrAnList φs) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓝(ofCrAnList φs * ofCrAnOp φ) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp

lemma normalOrder_ofCrAnOp_ofFieldOpList_swap (φ : 𝓕.CrAnFieldOp) (φ' : List 𝓕.FieldOp) :
    𝓝(ofCrAnOp φ * ofFieldOpList φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓝(ofFieldOpList φ' * ofCrAnOp φ) := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofFieldOpList_eq_superCommute]
  simp

lemma normalOrder_anPart_ofFieldOpList_swap (φ : 𝓕.FieldOp) (φ' : List 𝓕.FieldOp) :
    𝓝(anPart φ * ofFieldOpList φ') = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝(ofFieldOpList φ' * anPart φ) := by
  match φ with
  | .inAsymp φ =>
    simp
  | .position φ =>
    simp only [anPart_position, instCommGroup.eq_1]
    rw [normalOrder_ofCrAnOp_ofFieldOpList_swap]
    rfl
  | .outAsymp φ =>
    simp only [anPart_posAsymp, instCommGroup.eq_1]
    rw [normalOrder_ofCrAnOp_ofFieldOpList_swap]
    rfl

lemma normalOrder_ofFieldOpList_anPart_swap (φ : 𝓕.FieldOp) (φ' : List 𝓕.FieldOp) :
    𝓝(ofFieldOpList φ' * anPart φ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝(anPart φ * ofFieldOpList φ') := by
  rw [normalOrder_anPart_ofFieldOpList_swap]
  simp [smul_smul, FieldStatistic.exchangeSign_mul_self]

/- Start of proof attempt -/
lemma round1_h1 (𝓕 : FieldSpecification)
  (φ : 𝓕.FieldOp)
  (φs : List 𝓕.FieldOp):
  𝓝(ofFieldOpList φs * anPart φ) = 𝓝(ofFieldOpList φs) * anPart φ := by
  rw [normalOrder_mul_anPart]

lemma round1_h2 (𝓕 : FieldSpecification)
  (φ : 𝓕.FieldOp)
  (φs : List 𝓕.FieldOp):
  𝓝(ofFieldOpList φs * anPart φ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓝(anPart φ * ofFieldOpList φs) := by
  exact?

theorem normalOrder_ofFieldOpList_mul_anPart_swap (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    𝓝(ofFieldOpList φs) * anPart φ = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓝(anPart φ * ofFieldOpList φs)  := by

  have h1 : 𝓝(ofFieldOpList φs * anPart φ) = 𝓝(ofFieldOpList φs) * anPart φ := by
    exact round1_h1 𝓕 φ φs
  have h2 : 𝓝(ofFieldOpList φs * anPart φ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • 𝓝(anPart φ * ofFieldOpList φs) := by
    exact round1_h2 𝓕 φ φs
  rw [h1] at *
  rw [h2]
  <;> simp
