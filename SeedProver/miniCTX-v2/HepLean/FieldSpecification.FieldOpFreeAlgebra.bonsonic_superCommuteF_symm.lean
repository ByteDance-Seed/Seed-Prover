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

lemma superCommuteF_crPartF_crPartF (φ φ' : 𝓕.FieldOp) :
    [crPartF φ, crPartF φ']ₛca = crPartF φ * crPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * crPartF φ := by
  match φ, φ' with
  | FieldOp.outAsymp φ, _ =>
  simp only [crPartF_posAsymp, map_zero, LinearMap.zero_apply, zero_mul, instCommGroup.eq_1,
    mul_zero, sub_self]
  | _, FieldOp.outAsymp φ =>
  simp only [crPartF_posAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
    sub_self]
  | FieldOp.position φ, FieldOp.position φ' =>
  simp only [crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.position φ, FieldOp.inAsymp φ' =>
  simp only [crPartF_position, crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.inAsymp φ, FieldOp.position φ' =>
  simp only [crPartF_negAsymp, crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.inAsymp φ, FieldOp.inAsymp φ' =>
  simp only [crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp [crAnStatistics, ← ofCrAnListF_append]

lemma superCommuteF_anPartF_anPartF (φ φ' : 𝓕.FieldOp) :
    [anPartF φ, anPartF φ']ₛca =
    anPartF φ * anPartF φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * anPartF φ := by
  match φ, φ' with
  | FieldOp.inAsymp φ, _ =>
    simp
  | _, FieldOp.inAsymp φ =>
    simp
  | FieldOp.position φ, FieldOp.position φ' =>
    simp only [anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.position φ, FieldOp.outAsymp φ' =>
    simp only [anPartF_position, anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.outAsymp φ, FieldOp.position φ' =>
    simp only [anPartF_posAsymp, anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]
  | FieldOp.outAsymp φ, FieldOp.outAsymp φ' =>
    simp only [anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
    simp [crAnStatistics, ← ofCrAnListF_append]

lemma superCommuteF_crPartF_ofFieldOpListF (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [crPartF φ, ofFieldOpListF φs]ₛca =
    crPartF φ * ofFieldOpListF φs - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpListF φs *
    crPartF φ := by
  match φ with
  | FieldOp.inAsymp φ =>
    simp only [crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofFieldOpFsList]
    simp [crAnStatistics]
  | FieldOp.position φ =>
    simp only [crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofFieldOpFsList]
    simp [crAnStatistics]
  | FieldOp.outAsymp φ =>
    simp

lemma superCommuteF_anPartF_ofFieldOpListF (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [anPartF φ, ofFieldOpListF φs]ₛca =
    anPartF φ * ofFieldOpListF φs - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) •
    ofFieldOpListF φs * anPartF φ := by
  match φ with
  | FieldOp.inAsymp φ =>
    simp
  | FieldOp.position φ =>
    simp only [anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofFieldOpFsList]
    simp [crAnStatistics]
  | FieldOp.outAsymp φ =>
    simp only [anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofFieldOpFsList]
    simp [crAnStatistics]

lemma superCommuteF_crPartF_ofFieldOpF (φ φ' : 𝓕.FieldOp) :
    [crPartF φ, ofFieldOpF φ']ₛca =
    crPartF φ * ofFieldOpF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOpF φ' * crPartF φ := by
  rw [← ofFieldOpListF_singleton, superCommuteF_crPartF_ofFieldOpListF]
  simp

lemma superCommuteF_anPartF_ofFieldOpF (φ φ' : 𝓕.FieldOp) :
    [anPartF φ, ofFieldOpF φ']ₛca =
    anPartF φ * ofFieldOpF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOpF φ' * anPartF φ := by
  rw [← ofFieldOpListF_singleton, superCommuteF_anPartF_ofFieldOpListF]
  simp

/-!

## Mul equal superCommuteF

Lemmas which rewrite a multiplication of two elements of the algebra as their commuted
multiplication with a sign plus the super commutator.

-/
lemma ofCrAnListF_mul_ofCrAnListF_eq_superCommuteF (φs φs' : List 𝓕.CrAnFieldOp) :
    ofCrAnListF φs * ofCrAnListF φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnListF φs' * ofCrAnListF φs
    + [ofCrAnListF φs, ofCrAnListF φs']ₛca := by
  rw [superCommuteF_ofCrAnListF_ofCrAnListF]
  simp [ofCrAnListF_append]

lemma ofCrAnOpF_mul_ofCrAnListF_eq_superCommuteF (φ : 𝓕.CrAnFieldOp) (φs' : List 𝓕.CrAnFieldOp) :
    ofCrAnOpF φ * ofCrAnListF φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofCrAnListF φs' * ofCrAnOpF φ
    + [ofCrAnOpF φ, ofCrAnListF φs']ₛca := by
  rw [← ofCrAnListF_singleton, ofCrAnListF_mul_ofCrAnListF_eq_superCommuteF]
  simp

lemma ofFieldOpListF_mul_ofFieldOpListF_eq_superCommuteF (φs φs' : List 𝓕.FieldOp) :
    ofFieldOpListF φs * ofFieldOpListF φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpListF φs' * ofFieldOpListF φs
    + [ofFieldOpListF φs, ofFieldOpListF φs']ₛca := by
  rw [superCommuteF_ofFieldOpListF_ofFieldOpFsList]
  simp

lemma ofFieldOpF_mul_ofFieldOpListF_eq_superCommuteF (φ : 𝓕.FieldOp) (φs' : List 𝓕.FieldOp) :
    ofFieldOpF φ * ofFieldOpListF φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofFieldOpListF φs' * ofFieldOpF φ
    + [ofFieldOpF φ, ofFieldOpListF φs']ₛca := by
  rw [superCommuteF_ofFieldOpF_ofFieldOpFsList]
  simp

lemma ofFieldOpListF_mul_ofFieldOpF_eq_superCommuteF (φs : List 𝓕.FieldOp) (φ : 𝓕.FieldOp) :
    ofFieldOpListF φs * ofFieldOpF φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOpF φ * ofFieldOpListF φs
    + [ofFieldOpListF φs, ofFieldOpF φ]ₛca := by
  rw [superCommuteF_ofFieldOpListF_ofFieldOpF]
  simp

lemma crPartF_mul_anPartF_eq_superCommuteF (φ φ' : 𝓕.FieldOp) :
    crPartF φ * anPartF φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * crPartF φ +
    [crPartF φ, anPartF φ']ₛca := by
  rw [superCommuteF_crPartF_anPartF]
  simp

lemma anPartF_mul_crPartF_eq_superCommuteF (φ φ' : 𝓕.FieldOp) :
    anPartF φ * crPartF φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    crPartF φ' * anPartF φ +
    [anPartF φ, crPartF φ']ₛca := by
  rw [superCommuteF_anPartF_crPartF]
  simp

lemma crPartF_mul_crPartF_eq_superCommuteF (φ φ' : 𝓕.FieldOp) :
    crPartF φ * crPartF φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * crPartF φ +
    [crPartF φ, crPartF φ']ₛca := by
  rw [superCommuteF_crPartF_crPartF]
  simp

lemma anPartF_mul_anPartF_eq_superCommuteF (φ φ' : 𝓕.FieldOp) :
    anPartF φ * anPartF φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * anPartF φ +
    [anPartF φ, anPartF φ']ₛca := by
  rw [superCommuteF_anPartF_anPartF]
  simp

lemma ofCrAnListF_mul_ofFieldOpListF_eq_superCommuteF (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : ofCrAnListF φs * ofFieldOpListF φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpListF φs' * ofCrAnListF φs
    + [ofCrAnListF φs, ofFieldOpListF φs']ₛca := by
  rw [superCommuteF_ofCrAnListF_ofFieldOpFsList]
  simp

/-!

## Symmetry of the super commutator.

-/

lemma superCommuteF_ofCrAnListF_ofCrAnListF_symm (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs, ofCrAnListF φs']ₛca =
    (- 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs')) • [ofCrAnListF φs', ofCrAnListF φs]ₛca := by
  rw [superCommuteF_ofCrAnListF_ofCrAnListF, superCommuteF_ofCrAnListF_ofCrAnListF, smul_sub]
  simp only [instCommGroup.eq_1, neg_smul, sub_neg_eq_add]
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [exchangeSign_symm, exchangeSign_mul_self]
  simp only [one_smul]
  abel

lemma superCommuteF_ofCrAnOpF_ofCrAnOpF_symm (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOpF φ, ofCrAnOpF φ']ₛca =
    (- 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ')) • [ofCrAnOpF φ', ofCrAnOpF φ]ₛca := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, superCommuteF_ofCrAnOpF_ofCrAnOpF]
  rw [smul_sub]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, neg_smul, sub_neg_eq_add]
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [exchangeSign_symm, exchangeSign_mul_self]
  simp only [one_smul]
  abel

/-!

## Splitting the super commutator on lists into sums.

-/

lemma superCommuteF_ofCrAnListF_ofCrAnListF_cons (φ : 𝓕.CrAnFieldOp) (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs, ofCrAnListF (φ :: φs')]ₛca =
    [ofCrAnListF φs, ofCrAnOpF φ]ₛca * ofCrAnListF φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ)
    • ofCrAnOpF φ * [ofCrAnListF φs, ofCrAnListF φs']ₛca := by
  rw [superCommuteF_ofCrAnListF_ofCrAnListF]
  conv_rhs =>
    lhs
    rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF, sub_mul,
      ← ofCrAnListF_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofCrAnListF_append, ofCrAnListF_singleton, smul_mul_assoc,
      mul_assoc, ← ofCrAnListF_append]
  conv_rhs =>
    rhs
    rw [superCommuteF_ofCrAnListF_ofCrAnListF, mul_sub, smul_mul_assoc]
  simp only [instCommGroup.eq_1, List.cons_append, List.append_assoc, List.nil_append,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sub_add_sub_cancel, sub_right_inj]
  rw [← ofCrAnListF_cons, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp only [instCommGroup, map_mul, mul_comm]

lemma superCommuteF_ofCrAnListF_ofFieldOpListF_cons (φ : 𝓕.FieldOp) (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : [ofCrAnListF φs, ofFieldOpListF (φ :: φs')]ₛca =
    [ofCrAnListF φs, ofFieldOpF φ]ₛca * ofFieldOpListF φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOpF φ * [ofCrAnListF φs, ofFieldOpListF φs']ₛca := by
  rw [superCommuteF_ofCrAnListF_ofFieldOpFsList]
  conv_rhs =>
    lhs
    rw [← ofFieldOpListF_singleton, superCommuteF_ofCrAnListF_ofFieldOpFsList, sub_mul, mul_assoc,
      ← ofFieldOpListF_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofFieldOpListF_singleton, smul_mul_assoc,
      smul_mul_assoc, mul_assoc]
  conv_rhs =>
    rhs
    rw [superCommuteF_ofCrAnListF_ofFieldOpFsList, mul_sub, smul_mul_assoc]
  simp only [instCommGroup, Algebra.smul_mul_assoc, List.singleton_append, Algebra.mul_smul_comm,
    sub_add_sub_cancel, sub_right_inj]
  rw [ofFieldOpListF_cons, mul_assoc, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp [mul_comm]

/--
For a field specification `𝓕`, and two lists `φs = φ₀…φₙ` and `φs'` of `𝓕.CrAnFieldOp`
the following super commutation relation holds:

`[φs', φ₀…φₙ]ₛca = ∑ i, 𝓢(φs', φ₀…φᵢ₋₁) • φ₀…φᵢ₋₁ * [φs', φᵢ]ₛca * φᵢ₊₁ … φₙ`

The proof of this relation is via induction on the length of `φs`.
-/
lemma superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum (φs : List 𝓕.CrAnFieldOp) :
    (φs' : List 𝓕.CrAnFieldOp) → [ofCrAnListF φs, ofCrAnListF φs']ₛca =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofCrAnListF (φs'.take n) * [ofCrAnListF φs, ofCrAnOpF (φs'.get n)]ₛca *
    ofCrAnListF (φs'.drop (n + 1))
  | [] => by
    simp [← ofCrAnListF_nil, superCommuteF_ofCrAnListF_ofCrAnListF]
  | φ :: φs' => by
    rw [superCommuteF_ofCrAnListF_ofCrAnListF_cons,
      superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofCrAnListF_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]

lemma superCommuteF_ofCrAnListF_ofFieldOpListF_eq_sum (φs : List 𝓕.CrAnFieldOp) :
    (φs' : List 𝓕.FieldOp) →
    [ofCrAnListF φs, ofFieldOpListF φs']ₛca =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
      ofFieldOpListF (φs'.take n) * [ofCrAnListF φs, ofFieldOpF (φs'.get n)]ₛca *
      ofFieldOpListF (φs'.drop (n + 1))
  | [] => by
    simp only [superCommuteF_ofCrAnListF_ofFieldOpFsList, instCommGroup, ofList_empty,
      exchangeSign_bosonic, one_smul, List.length_nil, Finset.univ_eq_empty, List.take_nil,
      List.get_eq_getElem, List.drop_nil, Finset.sum_empty]
    simp
  | φ :: φs' => by
    rw [superCommuteF_ofCrAnListF_ofFieldOpListF_cons,
      superCommuteF_ofCrAnListF_ofFieldOpListF_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofFieldOpListF_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]

lemma summerCommute_jacobi_ofCrAnListF (φs1 φs2 φs3 : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs1, [ofCrAnListF φs2, ofCrAnListF φs3]ₛca]ₛca =
    𝓢(𝓕 |>ₛ φs1, 𝓕 |>ₛ φs3) •
    (- 𝓢(𝓕 |>ₛ φs2, 𝓕 |>ₛ φs3) • [ofCrAnListF φs3, [ofCrAnListF φs1, ofCrAnListF φs2]ₛca]ₛca -
    𝓢(𝓕 |>ₛ φs1, 𝓕 |>ₛ φs2) • [ofCrAnListF φs2, [ofCrAnListF φs3, ofCrAnListF φs1]ₛca]ₛca) := by
  repeat rw [superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [instCommGroup, map_sub, map_smul, neg_smul]
  repeat rw [superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [instCommGroup.eq_1, ofList_append_eq_mul, List.append_assoc]
  by_cases h1 : (𝓕 |>ₛ φs1) = bosonic <;>
    by_cases h2 : (𝓕 |>ₛ φs2) = bosonic <;>
    by_cases h3 : (𝓕 |>ₛ φs3) = bosonic
  · simp only [h1, h2, h3, mul_self, bosonic_exchangeSign, one_smul, exchangeSign_bosonic, neg_sub]
    abel
  · simp only [h1, h2, bosonic_exchangeSign, one_smul, mul_bosonic, mul_self, map_one,
    exchangeSign_bosonic, neg_sub]
    abel
  · simp only [h1, h3, mul_bosonic, bosonic_exchangeSign, one_smul, exchangeSign_bosonic, neg_sub,
    mul_self, map_one]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_self, bosonic_exchangeSign, one_smul,
      fermionic_exchangeSign_fermionic, neg_smul, neg_sub, bosonic_mul_fermionic, sub_neg_eq_add,
      mul_bosonic, smul_add, exchangeSign_bosonic]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_self, map_one, one_smul, exchangeSign_bosonic, mul_bosonic,
      bosonic_exchangeSign, bosonic_mul_fermionic, neg_sub]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, bosonic_mul_fermionic, fermionic_exchangeSign_fermionic, neg_smul,
      one_smul, sub_neg_eq_add, bosonic_exchangeSign, mul_bosonic, smul_add, exchangeSign_bosonic,
      neg_sub, mul_self]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_bosonic, fermionic_exchangeSign_fermionic, neg_smul, one_smul,
      sub_neg_eq_add, exchangeSign_bosonic, bosonic_mul_fermionic, smul_add, mul_self,
      bosonic_exchangeSign, neg_sub]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_self, map_one, one_smul, fermionic_exchangeSign_fermionic, neg_smul,
      neg_sub]
    abel

/-!

## Interaction with grading.

-/

lemma superCommuteF_grade {a b : 𝓕.FieldOpFreeAlgebra} {f1 f2 : FieldStatistic}
    (ha : a ∈ statisticSubmodule f1) (hb : b ∈ statisticSubmodule f2) :
    [a, b]ₛca ∈ statisticSubmodule (f1 + f2) := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule f2) : Prop :=
    [a, a2]ₛca ∈ statisticSubmodule (f1 + f2)
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    simp only [add_eq_mul, instCommGroup, p]
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule f1) : Prop :=
        [a2, ofCrAnListF φs]ₛca ∈ statisticSubmodule (f1 + f2)
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [add_eq_mul, instCommGroup, p]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      apply Submodule.sub_mem _
      · apply ofCrAnListF_mem_statisticSubmodule_of
        rw [ofList_append_eq_mul, hφs, hφs']
      · apply Submodule.smul_mem
        apply ofCrAnListF_mem_statisticSubmodule_of
        rw [ofList_append_eq_mul, hφs, hφs']
        rw [mul_comm]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp only [add_eq_mul, instCommGroup, map_add, LinearMap.add_apply, p]
      exact Submodule.add_mem _ hp1 hp2
    · intro c x hx hp1
      simp only [add_eq_mul, instCommGroup, map_smul, LinearMap.smul_apply, p]
      exact Submodule.smul_mem _ c hp1
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp only [add_eq_mul, instCommGroup, map_add, p]
    exact Submodule.add_mem _ hp1 hp2
  · intro c x hx hp1
    simp only [add_eq_mul, instCommGroup, map_smul, p]
    exact Submodule.smul_mem _ c hp1
  · exact hb

lemma superCommuteF_bosonic_bosonic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
    [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
        [a2, ofCrAnListF φs]ₛca = a2 * ofCrAnListF φs - ofCrAnListF φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [hφs, ofCrAnListF_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [p, map_add, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_bosonic_fermionic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
    [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
        [a2, ofCrAnListF φs]ₛca = a2 * ofCrAnListF φs - ofCrAnListF φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [hφs, hφs', ofCrAnListF_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [p, map_add, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_fermionic_bonsonic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
    [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
        [a2, ofCrAnListF φs]ₛca = a2 * ofCrAnListF φs - ofCrAnListF φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnListF_ofCrAnListF]
      simp [hφs, hφs', ofCrAnListF_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [map_add, mul_add, add_mul, p]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_bonsonic {a b : 𝓕.FieldOpFreeAlgebra} (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  rw [← bosonicProjF_add_fermionicProjF a]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommuteF_bosonic_bosonic (by simp) hb, superCommuteF_fermionic_bonsonic (by simp) hb]
  simp only [add_mul, mul_add]
  abel

lemma bosonic_superCommuteF {a b : 𝓕.FieldOpFreeAlgebra} (ha : a ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  rw [← bosonicProjF_add_fermionicProjF b]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommuteF_bosonic_bosonic ha (by simp), superCommuteF_bosonic_fermionic ha (by simp)]
  simp only [add_mul, mul_add]
  abel

lemma superCommuteF_bonsonic_symm {a b : 𝓕.FieldOpFreeAlgebra}
    (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = - [b, a]ₛca := by
  rw [bosonic_superCommuteF hb, superCommuteF_bonsonic hb]
  simp

/- Start of proof attempt -/
lemma round1_h1 (𝓕 : FieldSpecification)
  (a b : 𝓕.FieldOpFreeAlgebra)
  (ha : a ∈ statisticSubmodule bosonic):
  [a, b]ₛca = a * b - b * a := by
  exact bosonic_superCommuteF ha

lemma round1_h2 (𝓕 : FieldSpecification)
  (a b : 𝓕.FieldOpFreeAlgebra)
  (ha : a ∈ statisticSubmodule bosonic):
  [b, a]ₛca = b * a - a * b := by
  exact superCommuteF_bonsonic ha

theorem bonsonic_superCommuteF_symm {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = - [b, a]ₛca  := by

  have h1 : [a, b]ₛca = a * b - b * a := by
    exact round1_h1 𝓕 a b ha
  have h2 : [b, a]ₛca = b * a - a * b := by
    exact round1_h2 𝓕 a b ha
  rw [h1, h2]
  ring
  <;> simp_all
  <;> ring
