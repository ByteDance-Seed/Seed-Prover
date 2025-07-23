-- In HepLean/HepLean/PerturbationTheory/FieldOpAlgebra/WicksTheoremNormal.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.StaticWickTheorem
import HepLean.PerturbationTheory.FieldOpAlgebra.WicksTheorem
import HepLean.PerturbationTheory.WickContraction.Sign.Join
import HepLean.PerturbationTheory.WickContraction.TimeCond
/-!

# Wick's theorem for normal ordered lists

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra
namespace FieldOpAlgebra
open WickContraction
open EqTimeOnly

/--
For a list `φs` of `𝓕.FieldOp`, then

`𝓣(φs) = ∑ φsΛ, φsΛ.sign • φsΛ.timeContract * 𝓣(𝓝([φsΛ]ᵘᶜ))`

where the sum is over all Wick contraction `φsΛ` which only have equal time contractions.

This result follows from
- `static_wick_theorem` to rewrite `𝓣(φs)` on the left hand side as a sum of
  `𝓣(φsΛ.staticWickTerm)`.
- `EqTimeOnly.timeOrder_staticContract_of_not_mem` and `timeOrder_timeOrder_mid` to set to
  those `𝓣(φsΛ.staticWickTerm)` for which `φsΛ` has a contracted pair which are not
  equal time to zero.
- `staticContract_eq_timeContract_of_eqTimeOnly` to rewrite the static contract
  in the remaining `𝓣(φsΛ.staticWickTerm)` as a time contract.
- `timeOrder_timeContract_mul_of_eqTimeOnly_left` to move the time contracts out of the time
  ordering.
-/
lemma timeOrder_ofFieldOpList_eqTimeOnly (φs : List 𝓕.FieldOp) :
    𝓣(ofFieldOpList φs) = ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs)}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := by
  rw [static_wick_theorem φs]
  let e2 : WickContraction φs.length ≃
    {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} ⊕
    {φsΛ : WickContraction φs.length // ¬ φsΛ.EqTimeOnly} :=
    (Equiv.sumCompl _).symm
  rw [← e2.symm.sum_comp]
  simp only [Equiv.symm_symm, Algebra.smul_mul_assoc, Fintype.sum_sum_type,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, map_add, map_sum, map_smul, e2]
  simp only [staticWickTerm, Algebra.smul_mul_assoc, map_smul]
  conv_lhs =>
    enter [2, 2, x]
    rw [timeOrder_timeOrder_left]
    rw [timeOrder_staticContract_of_not_mem _ x.2]
  simp only [Finset.univ_eq_attach, zero_mul, map_zero, smul_zero, Finset.sum_const_zero, add_zero]
  congr
  funext x
  rw [staticContract_eq_timeContract_of_eqTimeOnly]
  rw [timeOrder_timeContract_mul_of_eqTimeOnly_left]
  exact x.2
  exact x.2

lemma timeOrder_ofFieldOpList_eq_eqTimeOnly_empty (φs : List 𝓕.FieldOp) :
    𝓣(ofFieldOpList φs) = 𝓣(𝓝(ofFieldOpList φs)) +
    ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := by
  let e1 : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} ≃
      {φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // φsΛ.1 = empty} ⊕
      {φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // ¬ φsΛ.1 = empty} :=
      (Equiv.sumCompl _).symm
  rw [timeOrder_ofFieldOpList_eqTimeOnly, ← e1.symm.sum_comp]
  simp only [Equiv.symm_symm, Algebra.smul_mul_assoc, Fintype.sum_sum_type,
    Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, ne_eq, e1]
  congr 1
  · let e2 : {φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // φsΛ.1 = empty } ≃
      Unit := {
      toFun := fun x => (), invFun := fun x => ⟨⟨empty, by simp⟩, rfl⟩,
      left_inv a := by
        ext
        simp [a.2], right_inv a := by simp}
    rw [← e2.symm.sum_comp]
    simp [e2, sign_empty]
  · let e2 : { φsΛ : {φsΛ : WickContraction φs.length // φsΛ.EqTimeOnly} // ¬ φsΛ.1 = empty } ≃
      {φsΛ // φsΛ.EqTimeOnly ∧ φsΛ ≠ empty} := {
        toFun := fun x => ⟨x, ⟨x.1.2, x.2⟩⟩, invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
        left_inv a := by rfl, right_inv a := by rfl }
    rw [← e2.symm.sum_comp]
    rfl

/- Start of proof attempt -/
lemma round1_normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty (φs : List 𝓕.FieldOp) :
    𝓣(𝓝(ofFieldOpList φs)) = 𝓣(ofFieldOpList φs) -
    ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := by
  have h2 : 𝓣(ofFieldOpList φs) = 𝓣(𝓝(ofFieldOpList φs)) + ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}), φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)) := timeOrder_ofFieldOpList_eq_eqTimeOnly_empty φs
  rw [h2]
  simp [add_sub_cancel_right]
  <;> ring

/--
For a list `φs` of `𝓕.FieldOp`, then

`𝓣(𝓝(φs)) = 𝓣(φs) - ∑ φsΛ, φsΛ.sign • φsΛ.timeContract.1 * 𝓣(𝓝([φsΛ]ᵘᶜ))`

where the sum is over all *non-empty* Wick contraction `φsΛ` which only
  have equal time contractions.

This result follows directly from
- `timeOrder_ofFieldOpList_eqTimeOnly`
-/
theorem normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty (φs : List 𝓕.FieldOp) :
    𝓣(𝓝(ofFieldOpList φs)) = 𝓣(ofFieldOpList φs) -
    ∑ (φsΛ : {φsΛ // φsΛ.EqTimeOnly (φs := φs) ∧ φsΛ ≠ empty}),
    φsΛ.1.sign • φsΛ.1.timeContract.1 * 𝓣(𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ))  := by

  exact round1_normalOrder_timeOrder_ofFieldOpList_eq_eqTimeOnly_empty φs
