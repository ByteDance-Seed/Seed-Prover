-- In HepLean/HepLean/PerturbationTheory/FieldOpFreeAlgebra/NormTimeOrder.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.Basic
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Norm-time Ordering in the FieldOpFreeAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section
open HepLean.List

/-!

## Norm-time order

-/

/-- The normal-time ordering on `FieldOpFreeAlgebra`. -/
def normTimeOrder : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)

@[inherit_doc normTimeOrder]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓣𝓝ᶠ(" a ")" => normTimeOrder a

/- Start of proof attempt -/
lemma round1_normTimeOrder_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    normTimeOrder (ofCrAnListF φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
  have h1 : (Basis.constr ofCrAnListFBasis ℂ fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) (ofCrAnListFBasis φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
    have h11 : (Basis.constr ofCrAnListFBasis ℂ fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) (ofCrAnListFBasis φs) = (fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) φs := by
      apply Basis.constr_basis
    have h12 : (fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) φs = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
      simp
    rw [h11, h12]
  have h2 : (Basis.constr ofCrAnListFBasis ℂ fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) (ofCrAnListF φs) = (Basis.constr ofCrAnListFBasis ℂ fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) (ofCrAnListFBasis φs) := by
    congr 1
    <;> aesop
  have h3 : (Basis.constr ofCrAnListFBasis ℂ fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) (ofCrAnListF φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
    rw [h2]
    exact h1
  have h4 : normTimeOrder (ofCrAnListF φs) = (Basis.constr ofCrAnListFBasis ℂ fun φs => normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)) (ofCrAnListF φs) := by
    rfl
  rw [h4]
  exact h3

theorem normTimeOrder_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    𝓣𝓝ᶠ(ofCrAnListF φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs)  := by

  have h_main : normTimeOrder (ofCrAnListF φs) = normTimeOrderSign φs • ofCrAnListF (normTimeOrderList φs) := by
    exact round1_normTimeOrder_ofCrAnListF φs
  simpa using h_main
