-- In HepLean/HepLean/PerturbationTheory/FieldOpAlgebra/NormalOrder/Basic.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.NormalOrder
import HepLean.PerturbationTheory.FieldOpAlgebra.SuperCommute
/-!

# Normal Ordering on Field operator algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-!

## Normal order on super-commutators.

The main result of this is
`ι_normalOrderF_superCommuteF_eq_zero_mul`
which states that applying `ι` to the normal order of something containing a super-commutator
is zero.

-/

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero
    (φa φa' : 𝓕.CrAnFieldOp) (φs φs' : List 𝓕.CrAnFieldOp) :
    ι 𝓝ᶠ(ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * ofCrAnListF φs') = 0 := by
  rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa) with hφa | hφa
  <;> rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa') with hφa' | hφa'
  · rw [normalOrderF_superCommuteF_ofCrAnListF_create_create_ofCrAnListF φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, ι_superCommuteF_of_create_create φa φa' hφa hφa']
    simp
  · rw [normalOrderF_superCommuteF_create_annihilate φa φa' hφa hφa' (ofCrAnListF φs)
      (ofCrAnListF φs')]
    simp
  · rw [normalOrderF_superCommuteF_annihilate_create φa' φa hφa' hφa (ofCrAnListF φs)
      (ofCrAnListF φs')]
    simp
  · rw [normalOrderF_superCommuteF_ofCrAnListF_annihilate_annihilate_ofCrAnListF
      φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul,
      ι_superCommuteF_of_annihilate_annihilate φa φa' hφa hφa']
    simp

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero
    (φa φa' : 𝓕.CrAnFieldOp) (φs : List 𝓕.CrAnFieldOp)
    (a : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * a) = 0 := by
  have hf : ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
      mulLinearMap (ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca) = 0 := by
    apply ofCrAnListFBasis.ext
    intro l
    simp only [FieldOpFreeAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    exact ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero φa φa' φs l
  change (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap ((ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca))) a = 0
  rw [hf]
  simp

lemma ι_normalOrderF_superCommuteF_ofCrAnOpF_eq_zero_mul (φa φa' : 𝓕.CrAnFieldOp)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * b) = 0 := by
  rw [mul_assoc]
  change (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ mulLinearMap.flip
    ([ofCrAnOpF φa, ofCrAnOpF φa']ₛca * b)) a = 0
  have hf : ι.toLinearMap ∘ₗ normalOrderF ∘ₗ mulLinearMap.flip
      ([ofCrAnOpF φa, ofCrAnOpF φa']ₛca * b) = 0 := by
    apply ofCrAnListFBasis.ext
    intro l
    simp only [mulLinearMap, FieldOpFreeAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    rw [← mul_assoc]
    exact ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero φa φa' _ _
  rw [hf]
  simp

lemma ι_normalOrderF_superCommuteF_ofCrAnOpF_ofCrAnListF_eq_zero_mul (φa : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnListF φs]ₛca * b) = 0 := by
  rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b, ofCrAnListF_singleton]
  rw [ι_normalOrderF_superCommuteF_ofCrAnOpF_eq_zero_mul]

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnOpF_eq_zero_mul (φa : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnListF φs, ofCrAnOpF φa]ₛca * b) = 0 := by
  rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF_symm, ofCrAnListF_singleton]
  simp only [FieldStatistic.instCommGroup.eq_1, FieldStatistic.ofList_singleton, mul_neg,
    Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, map_neg, map_smul]
  rw [ι_normalOrderF_superCommuteF_ofCrAnOpF_ofCrAnListF_eq_zero_mul]
  simp

/- Start of proof attempt -/
lemma round1_ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero_mul
    (φs φs' : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnListF φs, ofCrAnListF φs']ₛca * b) = 0 := by
  rw [superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro n _
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b]
  rw [ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnOpF_eq_zero_mul]
  <;> simp

theorem ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero_mul
    (φs φs' : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnListF φs, ofCrAnListF φs']ₛca * b) = 0  := by

  exact round1_ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero_mul φs φs' a b
