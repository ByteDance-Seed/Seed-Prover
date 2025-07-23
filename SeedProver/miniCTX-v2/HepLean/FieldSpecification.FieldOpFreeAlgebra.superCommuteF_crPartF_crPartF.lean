-- In HepLean/HepLean/PerturbationTheory/FieldOpFreeAlgebra/SuperCommute.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.Basic
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.Grading
/-!

# Super Commute
-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

namespace FieldOpFreeAlgebra

/-!

## The super commutator on the FieldOpFreeAlgebra.

-/

open FieldStatistic

/-- For a field specification `𝓕`, the super commutator `superCommuteF` is defined as the linear
  map `𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra`
  which on the lists `φs` and `φs'` of `𝓕.CrAnFieldOp` gives

  `superCommuteF φs φs' = φs * φs' - 𝓢(φs, φs') • φs' * φs`.

  The notation `[a, b]ₛca` can be used for `superCommuteF a b`. -/
noncomputable def superCommuteF : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra →ₗ[ℂ]
    𝓕.FieldOpFreeAlgebra :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  Basis.constr ofCrAnListFBasis ℂ fun φs' =>
  ofCrAnListF (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnListF (φs' ++ φs)

@[inherit_doc superCommuteF]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "[" φs "," φs' "]ₛca" => superCommuteF φs φs'

/-!

## The super commutator of different types of elements

-/

lemma superCommuteF_ofCrAnListF_ofCrAnListF (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs, ofCrAnListF φs']ₛca =
    ofCrAnListF (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnListF (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommuteF, Basis.constr_basis]

lemma superCommuteF_ofCrAnOpF_ofCrAnOpF (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOpF φ, ofCrAnOpF φ']ₛca =
    ofCrAnOpF φ * ofCrAnOpF φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofCrAnOpF φ' * ofCrAnOpF φ := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rw [superCommuteF_ofCrAnListF_ofCrAnListF, ofCrAnListF_append]
  congr
  rw [ofCrAnListF_append]
  rw [FieldStatistic.ofList_singleton, FieldStatistic.ofList_singleton, smul_mul_assoc]

lemma superCommuteF_ofCrAnListF_ofFieldOpFsList (φcas : List 𝓕.CrAnFieldOp) (φs : List 𝓕.FieldOp) :
    [ofCrAnListF φcas, ofFieldOpListF φs]ₛca = ofCrAnListF φcas * ofFieldOpListF φs -
    𝓢(𝓕 |>ₛ φcas, 𝓕 |>ₛ φs) • ofFieldOpListF φs * ofCrAnListF φcas := by
  conv_lhs => rw [ofFieldOpListF_sum]
  rw [map_sum]
  conv_lhs =>
    enter [2, x]
    rw [superCommuteF_ofCrAnListF_ofCrAnListF, CrAnSection.statistics_eq_state_statistics,
      ofCrAnListF_append, ofCrAnListF_append]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.smul_sum,
    ← Finset.sum_mul, ← ofFieldOpListF_sum]
  simp

lemma superCommuteF_ofFieldOpListF_ofFieldOpFsList (φ : List 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [ofFieldOpListF φ, ofFieldOpListF φs]ₛca = ofFieldOpListF φ * ofFieldOpListF φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpListF φs * ofFieldOpListF φ := by
  conv_lhs => rw [ofFieldOpListF_sum]
  simp only [map_sum, LinearMap.coeFn_sum, Finset.sum_apply, instCommGroup.eq_1,
    Algebra.smul_mul_assoc]
  conv_lhs =>
    enter [2, x]
    rw [superCommuteF_ofCrAnListF_ofFieldOpFsList]
  simp only [instCommGroup.eq_1, CrAnSection.statistics_eq_state_statistics,
    Algebra.smul_mul_assoc, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.smul_sum, ← Finset.mul_sum, ← ofFieldOpListF_sum]

lemma superCommuteF_ofFieldOpF_ofFieldOpFsList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [ofFieldOpF φ, ofFieldOpListF φs]ₛca = ofFieldOpF φ * ofFieldOpListF φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpListF φs * ofFieldOpF φ := by
  rw [← ofFieldOpListF_singleton, superCommuteF_ofFieldOpListF_ofFieldOpFsList,
    ofFieldOpListF_singleton]
  simp

lemma superCommuteF_ofFieldOpListF_ofFieldOpF (φs : List 𝓕.FieldOp) (φ : 𝓕.FieldOp) :
    [ofFieldOpListF φs, ofFieldOpF φ]ₛca = ofFieldOpListF φs * ofFieldOpF φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOpF φ * ofFieldOpListF φs := by
  rw [← ofFieldOpListF_singleton, superCommuteF_ofFieldOpListF_ofFieldOpFsList,
    ofFieldOpListF_singleton]
  simp

lemma superCommuteF_anPartF_crPartF (φ φ' : 𝓕.FieldOp) :
    [anPartF φ, crPartF φ']ₛca = anPartF φ * crPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * anPartF φ := by
  match φ, φ' with
  | FieldOp.inAsymp φ, _ =>
    simp
  | _, FieldOp.outAsymp φ =>
    simp only [crPartF_posAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
      sub_self]
  | FieldOp.position φ, FieldOp.position φ' =>
    simp only [anPartF_position, crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.outAsymp φ, FieldOp.position φ' =>
    simp only [anPartF_posAsymp, crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.position φ, FieldOp.inAsymp φ' =>
    simp only [anPartF_position, crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp only [List.singleton_append, instCommGroup.eq_1, crAnStatistics,
      FieldStatistic.ofList_singleton, Function.comp_apply, crAnFieldOpToFieldOp_prod, ←
      ofCrAnListF_append]
  | FieldOp.outAsymp φ, FieldOp.inAsymp φ' =>
    simp only [anPartF_posAsymp, crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]

lemma superCommuteF_crPartF_anPartF (φ φ' : 𝓕.FieldOp) :
    [crPartF φ, anPartF φ']ₛca = crPartF φ * anPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * crPartF φ := by
    match φ, φ' with
    | FieldOp.outAsymp φ, _ =>
    simp only [crPartF_posAsymp, map_zero, LinearMap.zero_apply, zero_mul, instCommGroup.eq_1,
      mul_zero, sub_self]
    | _, FieldOp.inAsymp φ =>
    simp only [anPartF_negAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
      sub_self]
    | FieldOp.position φ, FieldOp.position φ' =>
    simp only [crPartF_position, anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
    | FieldOp.position φ, FieldOp.outAsymp φ' =>
    simp only [crPartF_position, anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
    | FieldOp.inAsymp φ, FieldOp.position φ' =>
    simp only [crPartF_negAsymp, anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
    | FieldOp.inAsymp φ, FieldOp.outAsymp φ' =>
    simp only [crPartF_negAsymp, anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]

/- Start of proof attempt -/
lemma round1_ofCrAnOpF_eq_ofCrAnListF_singleton (φ : 𝓕.CrAnFieldOp) : 
    ofCrAnOpF φ = ofCrAnListF [φ] := by
  rw [← ofCrAnListF_singleton]

lemma round1_superCommuteF_crPartF_crPartF (φ φ' : 𝓕.FieldOp) :
    [crPartF φ, crPartF φ']ₛca = crPartF φ * crPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * crPartF φ := by
  have h1 : ∀ (x : 𝓕.FieldOpFreeAlgebra), [x, 0]ₛca = 0 := by
    intro x
    simp [superCommuteF]
    <;> aesop
  have h2 : ∀ (x : 𝓕.FieldOpFreeAlgebra), [0, x]ₛca = 0 := by
    intro x
    simp [superCommuteF]
    <;> aesop
  have h3 : ∀ (φ : 𝓕.CrAnFieldOp), ofCrAnOpF φ = ofCrAnListF [φ] := by
    intro φ
    exact round1_ofCrAnOpF_eq_ofCrAnListF_singleton φ
  cases φ with
  | outAsymp p =>
    simp [crPartF]
    <;>
    (try simp [h2])
    <;>
    ring
  | inAsymp p =>
    cases φ' with
    | outAsymp p' =>
      simp [crPartF]
      <;>
      (try simp [h1])
      <;>
      ring
    | inAsymp p' =>
      simp [crPartF]
      have h4 : ofCrAnOpF ⟨FieldOp.inAsymp p, ()⟩ = ofCrAnListF [⟨FieldOp.inAsymp p, ()⟩] := by
        exact h3 ⟨FieldOp.inAsymp p, ()⟩
      have h5 : ofCrAnOpF ⟨FieldOp.inAsymp p', ()⟩ = ofCrAnListF [⟨FieldOp.inAsymp p', ()⟩] := by
        exact h3 ⟨FieldOp.inAsymp p', ()⟩
      rw [h4, h5]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [crAnStatistics, ← ofCrAnListF_append]
      <;> ring
    | position p' =>
      simp [crPartF]
      have h4 : ofCrAnOpF ⟨FieldOp.inAsymp p, ()⟩ = ofCrAnListF [⟨FieldOp.inAsymp p, ()⟩] := by
        exact h3 ⟨FieldOp.inAsymp p, ()⟩
      have h5 : ofCrAnOpF ⟨FieldOp.position p', CreateAnnihilate.create⟩ = 
        ofCrAnListF [⟨FieldOp.position p', CreateAnnihilate.create⟩] := by
        exact h3 ⟨FieldOp.position p', CreateAnnihilate.create⟩
      rw [h4, h5]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [crAnStatistics, ← ofCrAnListF_append]
      <;> ring
  | position p =>
    cases φ' with
    | outAsymp p' =>
      simp [crPartF]
      <;>
      (try simp [h1])
      <;>
      ring
    | inAsymp p' =>
      simp [crPartF]
      have h4 : ofCrAnOpF ⟨FieldOp.position p, CreateAnnihilate.create⟩ = 
        ofCrAnListF [⟨FieldOp.position p, CreateAnnihilate.create⟩] := by
        exact h3 ⟨FieldOp.position p, CreateAnnihilate.create⟩
      have h5 : ofCrAnOpF ⟨FieldOp.inAsymp p', ()⟩ = ofCrAnListF [⟨FieldOp.inAsymp p', ()⟩] := by
        exact h3 ⟨FieldOp.inAsymp p', ()⟩
      rw [h4, h5]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [crAnStatistics, ← ofCrAnListF_append]
      <;> ring
    | position p' =>
      simp [crPartF]
      have h4 : ofCrAnOpF ⟨FieldOp.position p, CreateAnnihilate.create⟩ = 
        ofCrAnListF [⟨FieldOp.position p, CreateAnnihilate.create⟩] := by
        exact h3 ⟨FieldOp.position p, CreateAnnihilate.create⟩
      have h5 : ofCrAnOpF ⟨FieldOp.position p', CreateAnnihilate.create⟩ = 
        ofCrAnListF [⟨FieldOp.position p', CreateAnnihilate.create⟩] := by
        exact h3 ⟨FieldOp.position p', CreateAnnihilate.create⟩
      rw [h4, h5]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [crAnStatistics, ← ofCrAnListF_append]
      <;> ring

theorem superCommuteF_crPartF_crPartF (φ φ' : 𝓕.FieldOp) :
    [crPartF φ, crPartF φ']ₛca = crPartF φ * crPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * crPartF φ  := by

  exact round1_superCommuteF_crPartF_crPartF φ φ'
