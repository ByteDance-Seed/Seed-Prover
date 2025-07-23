-- In HepLean/HepLean/PerturbationTheory/FieldOpAlgebra/SuperCommute.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.TimeOrder
import HepLean.PerturbationTheory.FieldOpAlgebra.Basic
/-!

# SuperCommute on Field operator algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

lemma ι_superCommuteF_eq_zero_of_ι_right_zero (a b : 𝓕.FieldOpFreeAlgebra) (h : ι b = 0) :
    ι [a, b]ₛca = 0 := by
  rw [superCommuteF_expand_bosonicProjF_fermionicProjF]
  rw [ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero] at h
  simp_all

lemma ι_superCommuteF_eq_zero_of_ι_left_zero (a b : 𝓕.FieldOpFreeAlgebra) (h : ι a = 0) :
    ι [a, b]ₛca = 0 := by
  rw [superCommuteF_expand_bosonicProjF_fermionicProjF]
  rw [ι_eq_zero_iff_ι_bosonicProjF_fermonicProj_zero] at h
  simp_all

/-!

## Defining normal order for `FiedOpAlgebra`.

-/

lemma ι_superCommuteF_right_zero_of_mem_ideal (a b : 𝓕.FieldOpFreeAlgebra)
    (h : b ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι [a, b]ₛca = 0 := by
  apply ι_superCommuteF_eq_zero_of_ι_right_zero
  exact (ι_eq_zero_iff_mem_ideal b).mpr h

lemma ι_superCommuteF_eq_of_equiv_right (a b1 b2 : 𝓕.FieldOpFreeAlgebra) (h : b1 ≈ b2) :
    ι [a, b1]ₛca = ι [a, b2]ₛca := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_superCommuteF_right_zero_of_mem_ideal a (b1 - b2) h

/-- The super commutator on the `FieldOpAlgebra` defined as a linear map `[a,_]ₛ`. -/
noncomputable def superCommuteRight (a : 𝓕.FieldOpFreeAlgebra) :
  FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ superCommuteF a)
    (ι_superCommuteF_eq_of_equiv_right a)
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

lemma superCommuteRight_apply_ι (a b : 𝓕.FieldOpFreeAlgebra) :
    superCommuteRight a (ι b) = ι [a, b]ₛca := by rfl

lemma superCommuteRight_apply_quot (a b : 𝓕.FieldOpFreeAlgebra) :
    superCommuteRight a ⟦b⟧= ι [a, b]ₛca := by rfl

lemma superCommuteRight_eq_of_equiv (a1 a2 : 𝓕.FieldOpFreeAlgebra) (h : a1 ≈ a2) :
    superCommuteRight a1 = superCommuteRight a2 := by
  rw [equiv_iff_sub_mem_ideal] at h
  ext b
  obtain ⟨b, rfl⟩ := ι_surjective b
  have ha1b1 : (superCommuteRight (a1 - a2)) (ι b) = 0 := by
    rw [superCommuteRight_apply_ι]
    apply ι_superCommuteF_eq_zero_of_ι_left_zero
    exact (ι_eq_zero_iff_mem_ideal (a1 - a2)).mpr h
  simp_all only [superCommuteRight_apply_ι, map_sub, LinearMap.sub_apply]
  trans ι ((superCommuteF a2) b) + 0
  rw [← ha1b1]
  simp only [add_sub_cancel]
  simp

/-- For a field specification `𝓕`, `superCommute` is the linear map

  `FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕`

  defined as the decent of `ι ∘ superCommuteF` in both arguments.
  In particular for `φs` and `φs'` lists of `𝓕.CrAnFieldOp` in `FieldOpAlgebra 𝓕` the following
  relation holds:

  `superCommute φs φs' = φs * φs' - 𝓢(φs, φs') • φs' * φs`

  The notation `[a, b]ₛ` is used for `superCommute a b`.
  -/
noncomputable def superCommute : FieldOpAlgebra 𝓕 →ₗ[ℂ]
    FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift superCommuteRight superCommuteRight_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, rfl⟩ := ι_surjective x
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_add, ι_apply, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp only [LinearMap.add_apply]
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp
  map_smul' c y := by
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_smul, ι_apply, ι_apply, ι_apply]
    simp only [Quotient.lift_mk, RingHom.id_apply, LinearMap.smul_apply]
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp

@[inherit_doc superCommute]
scoped[FieldSpecification.FieldOpAlgebra] notation "[" a "," b "]ₛ" => superCommute a b

lemma superCommute_eq_ι_superCommuteF (a b : 𝓕.FieldOpFreeAlgebra) :
    [ι a, ι b]ₛ = ι [a, b]ₛca := rfl

/-!

## Properties of `superCommute`.

-/

/-!

## Properties from the definition of FieldOpAlgebra

-/

lemma superCommute_create_create {φ φ' : 𝓕.CrAnFieldOp}
    (h : 𝓕 |>ᶜ φ = .create) (h' : 𝓕 |>ᶜ φ' = .create) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 := by
  rw [ofCrAnOp, ofCrAnOp]
  rw [superCommute_eq_ι_superCommuteF, ι_superCommuteF_of_create_create _ _ h h']

lemma superCommute_annihilate_annihilate {φ φ' : 𝓕.CrAnFieldOp}
    (h : 𝓕 |>ᶜ φ = .annihilate) (h' : 𝓕 |>ᶜ φ' = .annihilate) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 := by
  rw [ofCrAnOp, ofCrAnOp]
  rw [superCommute_eq_ι_superCommuteF, ι_superCommuteF_of_annihilate_annihilate _ _ h h']

lemma superCommute_diff_statistic {φ φ' : 𝓕.CrAnFieldOp} (h : (𝓕 |>ₛ φ) ≠ 𝓕 |>ₛ φ') :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = 0 := by
  rw [ofCrAnOp, ofCrAnOp]
  rw [superCommute_eq_ι_superCommuteF, ι_superCommuteF_of_diff_statistic h]

lemma superCommute_ofCrAnOp_ofFieldOp_diff_stat_zero (φ : 𝓕.CrAnFieldOp) (ψ : 𝓕.FieldOp)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : [ofCrAnOp φ, ofFieldOp ψ]ₛ = 0 := by
  rw [ofFieldOp_eq_sum, map_sum]
  rw [Finset.sum_eq_zero]
  intro x hx
  apply superCommute_diff_statistic
  simpa [crAnStatistics] using h

lemma superCommute_anPart_ofFieldOpF_diff_grade_zero (φ ψ : 𝓕.FieldOp)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : [anPart φ, ofFieldOp ψ]ₛ = 0 := by
  match φ with
  | FieldOp.inAsymp _ =>
    simp
  | FieldOp.position φ =>
    simp only [anPartF_position]
    apply superCommute_ofCrAnOp_ofFieldOp_diff_stat_zero _ _ _
    simpa [crAnStatistics] using h
  | FieldOp.outAsymp _ =>
    simp only [anPartF_posAsymp]
    apply superCommute_ofCrAnOp_ofFieldOp_diff_stat_zero _ _
    simpa [crAnStatistics] using h

lemma superCommute_ofCrAnOp_ofCrAnOp_mem_center (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ ∈ Subalgebra.center ℂ (FieldOpAlgebra 𝓕) := by
  rw [ofCrAnOp, ofCrAnOp, superCommute_eq_ι_superCommuteF]
  exact ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center φ φ'

lemma superCommute_ofCrAnOp_ofCrAnOp_commute (φ φ' : 𝓕.CrAnFieldOp)
    (a : FieldOpAlgebra 𝓕) :
    a * [ofCrAnOp φ, ofCrAnOp φ']ₛ = [ofCrAnOp φ, ofCrAnOp φ']ₛ * a := by
  have h1 := superCommute_ofCrAnOp_ofCrAnOp_mem_center φ φ'
  rw [@Subalgebra.mem_center_iff] at h1
  exact h1 a

lemma superCommute_ofCrAnOp_ofFieldOp_mem_center (φ : 𝓕.CrAnFieldOp) (φ' : 𝓕.FieldOp) :
    [ofCrAnOp φ, ofFieldOp φ']ₛ ∈ Subalgebra.center ℂ (FieldOpAlgebra 𝓕) := by
  rw [ofFieldOp_eq_sum]
  simp only [map_sum]
  refine Subalgebra.sum_mem (Subalgebra.center ℂ 𝓕.FieldOpAlgebra) ?_
  intro x hx
  exact superCommute_ofCrAnOp_ofCrAnOp_mem_center φ ⟨φ', x⟩

lemma superCommute_ofCrAnOp_ofFieldOp_commute (φ : 𝓕.CrAnFieldOp) (φ' : 𝓕.FieldOp)
    (a : FieldOpAlgebra 𝓕) : a * [ofCrAnOp φ, ofFieldOp φ']ₛ =
    [ofCrAnOp φ, ofFieldOp φ']ₛ * a := by
  have h1 := superCommute_ofCrAnOp_ofFieldOp_mem_center φ φ'
  rw [@Subalgebra.mem_center_iff] at h1
  exact h1 a

lemma superCommute_anPart_ofFieldOp_mem_center (φ φ' : 𝓕.FieldOp) :
    [anPart φ, ofFieldOp φ']ₛ ∈ Subalgebra.center ℂ (FieldOpAlgebra 𝓕) := by
  match φ with
  | FieldOp.inAsymp _ =>
    simp only [anPart_negAsymp, map_zero, LinearMap.zero_apply]
    exact Subalgebra.zero_mem (Subalgebra.center ℂ _)
  | FieldOp.position φ =>
    exact superCommute_ofCrAnOp_ofFieldOp_mem_center _ _
  | FieldOp.outAsymp _ =>
    exact superCommute_ofCrAnOp_ofFieldOp_mem_center _ _

/-!

### `superCommute` on different constructors.

-/

lemma superCommute_ofCrAnList_ofCrAnList (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnList φs, ofCrAnList φs']ₛ =
    ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs) := by
  rw [ofCrAnList_eq_ι_ofCrAnListF, ofCrAnList_eq_ι_ofCrAnListF]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofCrAnListF_ofCrAnListF]
  rfl

lemma superCommute_ofCrAnOp_ofCrAnOp (φ φ' : 𝓕.CrAnFieldOp) :
    [ofCrAnOp φ, ofCrAnOp φ']ₛ = ofCrAnOp φ * ofCrAnOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofCrAnOp φ' * ofCrAnOp φ := by
  rw [ofCrAnOp, ofCrAnOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofCrAnOpF_ofCrAnOpF]
  rfl

lemma superCommute_ofCrAnList_ofFieldOpList (φcas : List 𝓕.CrAnFieldOp)
    (φs : List 𝓕.FieldOp) :
    [ofCrAnList φcas, ofFieldOpList φs]ₛ = ofCrAnList φcas * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φcas, 𝓕 |>ₛ φs) • ofFieldOpList φs * ofCrAnList φcas := by
  rw [ofCrAnList, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofCrAnListF_ofFieldOpFsList]
  rfl

lemma superCommute_ofFieldOpList_ofFieldOpList (φs φs' : List 𝓕.FieldOp) :
    [ofFieldOpList φs, ofFieldOpList φs']ₛ = ofFieldOpList φs * ofFieldOpList φs' -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOpList φs := by
  rw [ofFieldOpList, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofFieldOpListF_ofFieldOpFsList]
  rfl

lemma superCommute_ofFieldOp_ofFieldOpList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [ofFieldOp φ, ofFieldOpList φs]ₛ = ofFieldOp φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * ofFieldOp φ := by
  rw [ofFieldOp, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofFieldOpF_ofFieldOpFsList]
  rfl

lemma superCommute_ofFieldOpList_ofFieldOp (φs : List 𝓕.FieldOp) (φ : 𝓕.FieldOp) :
    [ofFieldOpList φs, ofFieldOp φ]ₛ = ofFieldOpList φs * ofFieldOp φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOp φ * ofFieldOpList φs := by
  rw [ofFieldOpList, ofFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofFieldOpListF_ofFieldOpF]
  rfl

lemma superCommute_anPart_crPart (φ φ' : 𝓕.FieldOp) :
    [anPart φ, crPart φ']ₛ = anPart φ * crPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ := by
  rw [anPart, crPart]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_crPartF]
  rfl

lemma superCommute_crPart_anPart (φ φ' : 𝓕.FieldOp) :
    [crPart φ, anPart φ']ₛ = crPart φ * anPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ := by
  rw [anPart, crPart]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_anPartF]
  rfl

@[simp]
lemma superCommute_crPart_crPart (φ φ' : 𝓕.FieldOp) : [crPart φ, crPart φ']ₛ = 0 := by
  match φ, φ' with
  | FieldOp.outAsymp φ, _ =>
    simp
  | _, FieldOp.outAsymp φ =>
    simp
  | FieldOp.position φ, FieldOp.position φ' =>
    simp only [crPart_position]
    apply superCommute_create_create
    · rfl
    · rfl
  | FieldOp.position φ, FieldOp.inAsymp φ' =>
    simp only [crPart_position, crPart_negAsymp]
    apply superCommute_create_create
    · rfl
    · rfl
  | FieldOp.inAsymp φ, FieldOp.inAsymp φ' =>
    simp only [crPart_negAsymp]
    apply superCommute_create_create
    · rfl
    · rfl
  | FieldOp.inAsymp φ, FieldOp.position φ' =>
    simp only [crPart_negAsymp, crPart_position]
    apply superCommute_create_create
    · rfl
    · rfl

@[simp]
lemma superCommute_anPart_anPart (φ φ' : 𝓕.FieldOp) : [anPart φ, anPart φ']ₛ = 0 := by
  match φ, φ' with
  | FieldOp.inAsymp φ, _ =>
    simp
  | _, FieldOp.inAsymp φ =>
    simp
  | FieldOp.position φ, FieldOp.position φ' =>
    simp only [anPart_position]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl
  | FieldOp.position φ, FieldOp.outAsymp φ' =>
    simp only [anPart_position, anPart_posAsymp]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl
  | FieldOp.outAsymp φ, FieldOp.outAsymp φ' =>
    simp only [anPart_posAsymp]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl
  | FieldOp.outAsymp φ, FieldOp.position φ' =>
    simp only [anPart_posAsymp, anPart_position]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl

lemma superCommute_crPart_ofFieldOpList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [crPart φ, ofFieldOpList φs]ₛ = crPart φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * crPart φ := by
  rw [crPart, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_ofFieldOpListF]
  rfl

lemma superCommute_anPart_ofFieldOpList (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    [anPart φ, ofFieldOpList φs]ₛ = anPart φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * anPart φ := by
  rw [anPart, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_ofFieldOpListF]
  rfl

lemma superCommute_crPart_ofFieldOp (φ φ' : 𝓕.FieldOp) :
    [crPart φ, ofFieldOp φ']ₛ = crPart φ * ofFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * crPart φ := by
  rw [crPart, ofFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_ofFieldOpF]
  rfl

lemma superCommute_anPart_ofFieldOp (φ φ' : 𝓕.FieldOp) :
    [anPart φ, ofFieldOp φ']ₛ = anPart φ * ofFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * anPart φ := by
  rw [anPart, ofFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_ofFieldOpF]
  rfl

/-!

## Mul equal superCommute

Lemmas which rewrite a multiplication of two elements of the algebra as their commuted
multiplication with a sign plus the super commutator.

-/

lemma ofCrAnList_mul_ofCrAnList_eq_superCommute (φs φs' : List 𝓕.CrAnFieldOp) :
    ofCrAnList φs * ofCrAnList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofCrAnList φs']ₛ := by
  rw [superCommute_ofCrAnList_ofCrAnList]
  simp [ofCrAnList_append]

lemma ofCrAnOp_mul_ofCrAnList_eq_superCommute (φ : 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.CrAnFieldOp) : ofCrAnOp φ * ofCrAnList φs' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnOp φ
    + [ofCrAnOp φ, ofCrAnList φs']ₛ := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp

lemma ofFieldOpList_mul_ofFieldOpList_eq_superCommute (φs φs' : List 𝓕.FieldOp) :
    ofFieldOpList φs * ofFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOpList φs
    + [ofFieldOpList φs, ofFieldOpList φs']ₛ := by
  rw [superCommute_ofFieldOpList_ofFieldOpList]
  simp

lemma ofFieldOp_mul_ofFieldOpList_eq_superCommute (φ : 𝓕.FieldOp) (φs' : List 𝓕.FieldOp) :
    ofFieldOp φ * ofFieldOpList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOp φ
    + [ofFieldOp φ, ofFieldOpList φs']ₛ := by
  rw [superCommute_ofFieldOp_ofFieldOpList]
  simp

lemma ofFieldOp_mul_ofFieldOp_eq_superCommute (φ φ' : 𝓕.FieldOp) :
    ofFieldOp φ * ofFieldOp φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * ofFieldOp φ
    + [ofFieldOp φ, ofFieldOp φ']ₛ := by
  rw [← ofFieldOpList_singleton, ← ofFieldOpList_singleton]
  rw [ofFieldOpList_mul_ofFieldOpList_eq_superCommute, ofFieldOpList_singleton]
  simp

lemma ofFieldOpList_mul_ofFieldOp_eq_superCommute (φs : List 𝓕.FieldOp) (φ : 𝓕.FieldOp) :
    ofFieldOpList φs * ofFieldOp φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOp φ * ofFieldOpList φs
    + [ofFieldOpList φs, ofFieldOp φ]ₛ := by
  rw [superCommute_ofFieldOpList_ofFieldOp]
  simp

lemma ofCrAnList_mul_ofFieldOpList_eq_superCommute (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : ofCrAnList φs * ofFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofFieldOpList φs']ₛ := by
  rw [superCommute_ofCrAnList_ofFieldOpList]
  simp

lemma crPart_mul_anPart_eq_superCommute (φ φ' : 𝓕.FieldOp) :
    crPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ
    + [crPart φ, anPart φ']ₛ := by
  rw [superCommute_crPart_anPart]
  simp

lemma anPart_mul_crPart_eq_superCommute (φ φ' : 𝓕.FieldOp) :
    anPart φ * crPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ
    + [anPart φ, crPart φ']ₛ := by
  rw [superCommute_anPart_crPart]
  simp

lemma crPart_mul_crPart_swap (φ φ' : 𝓕.FieldOp) :
    crPart φ * crPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * crPart φ := by
  trans 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * crPart φ + [crPart φ, crPart φ']ₛ
  · rw [crPart, crPart, superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_crPartF]
    simp
  · simp

/- Start of proof attempt -/
lemma round1_anPart_mul_anPart_swap (φ φ' : 𝓕.FieldOp) :
    anPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ := by
  have h1 : [anPart φ, anPart φ']ₛ = 0 := by
    exact superCommute_anPart_anPart φ φ'
  have h2 : [anPart φ, anPart φ']ₛ = anPart φ * anPart φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ := by
    cases φ <;> cases φ' <;> simp [superCommute_ofCrAnOp_ofCrAnOp, superCommute_ofFieldOp_ofFieldOpList, ofFieldOpList, ofFieldOp, superCommute_eq_ι_superCommuteF] <;>
      (try simp_all) <;>
      (try ring_nf) <;>
      (try simp_all) <;>
      (try aesop) <;>
      (try
        {
          aesop
        }) <;>
      (try
        {
          simp_all [superCommute]
        })
  have h3 : anPart φ * anPart φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ = 0 := by
    have h31 : [anPart φ, anPart φ']ₛ = 0 := h1
    have h32 : [anPart φ, anPart φ']ₛ = anPart φ * anPart φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ := h2
    rw [h32] at h31
    exact h31
  have h4 : anPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ := by
    simpa using sub_eq_zero.mp h3
  exact h4

theorem anPart_mul_anPart_swap (φ φ' : 𝓕.FieldOp) :
    anPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ  := by

  exact round1_anPart_mul_anPart_swap φ φ'
