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

/- Start of proof attempt -/
lemma round1_h1 (𝓕 : FieldSpecification)
  (a b : 𝓕.FieldOpAlgebra)
  (a' : 𝓕.FieldOpFreeAlgebra)
  (b' : 𝓕.FieldOpFreeAlgebra)
  (ha' : FieldSpecification.FieldOpAlgebra.ι a' = a)
  (hb' : FieldSpecification.FieldOpAlgebra.ι b' = b):
  [a, b]ₛ = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b') := by
  have h13 : FieldSpecification.FieldOpAlgebra.superCommute (FieldSpecification.FieldOpAlgebra.ι a') (FieldSpecification.FieldOpAlgebra.ι b') = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b') := by
    exact FieldSpecification.FieldOpAlgebra.superCommute_eq_ι_superCommuteF a' b'
  have h14 : FieldSpecification.FieldOpAlgebra.superCommute a b = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b') := by
    have ha1 : a = FieldSpecification.FieldOpAlgebra.ι a' := by rw [ha']
    have hb1 : b = FieldSpecification.FieldOpAlgebra.ι b' := by rw [hb']
    rw [ha1, hb1]
    exact h13
  have h15 : [a, b]ₛ = FieldSpecification.FieldOpAlgebra.superCommute a b := by
    rfl
  rw [h15, h14]
  <;> simp

lemma round1_h2 (𝓕 : FieldSpecification)
  (a b : 𝓕.FieldOpAlgebra)
  (a' : 𝓕.FieldOpFreeAlgebra)
  (b' : 𝓕.FieldOpFreeAlgebra)
  (h1 : [a, b]ₛ = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')):
  𝓝([a, b]ₛ) = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.normalOrderF (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) := by
  have h21 : 𝓝([a, b]ₛ) = 𝓝(FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) := by rw [h1]
  have h22 : 𝓝(FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.normalOrderF (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) := by
    rw [normalOrder_eq_ι_normalOrderF]
    <;> simp
  rw [h21, h22]

lemma round1_h3 (𝓕 : FieldSpecification)
  (a' : 𝓕.FieldOpFreeAlgebra)
  (b' : 𝓕.FieldOpFreeAlgebra):
  FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.normalOrderF (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) = 0 := by
  have h31 := FieldSpecification.FieldOpAlgebra.ι_normalOrderF_superCommuteF_eq_zero (c := b') (d := a')
  exact h31

/-- For a field specification `𝓕`, and `a` and `b` in `𝓕.FieldOpAlgebra` the normal ordering
  of the super commutator of `a` and `b` vanishes, i.e. `𝓝([a,b]ₛ) = 0`. -/
theorem normalOrder_superCommute_eq_zero (a b : 𝓕.FieldOpAlgebra) :
    𝓝([a, b]ₛ) = 0  := by

  have hι_surjective1 : ∃ (a' : 𝓕.FieldOpFreeAlgebra), FieldSpecification.FieldOpAlgebra.ι a' = a := by
    exact?
  have hι_surjective2 : ∃ (b' : 𝓕.FieldOpFreeAlgebra), FieldSpecification.FieldOpAlgebra.ι b' = b := by
    exact?
  obtain ⟨a', ha'⟩ := hι_surjective1
  obtain ⟨b', hb'⟩ := hι_surjective2
  have h1 : [a, b]ₛ = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b') := by
    exact round1_h1 𝓕 a b a' b' ha' hb'
  have h2 : 𝓝([a, b]ₛ) = FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.normalOrderF (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) := by
    exact round1_h2 𝓕 a b a' b' h1
  have h3 : FieldSpecification.FieldOpAlgebra.ι (FieldSpecification.FieldOpFreeAlgebra.normalOrderF (FieldSpecification.FieldOpFreeAlgebra.superCommuteF a' b')) = 0 := by
    exact round1_h3 𝓕 a' b'
  rw [h2, h3]
  <;> simp
