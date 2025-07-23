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

/- Start of proof attempt -/
lemma round1_superCommuteF_ofCrAnListF_ofCrAnListF (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs, ofCrAnListF φs']ₛca =
    ofCrAnListF (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnListF (φs' ++ φs) := by
  have h1 : ofCrAnListF φs = ofCrAnListFBasis φs := by simp [ofCrAnListF]
  have h2 : ofCrAnListF φs' = ofCrAnListFBasis φs' := by simp [ofCrAnListF]
  simp only [superCommuteF, h1, h2, Basis.constr_basis]
  <;> simp
  <;> aesop

theorem superCommuteF_ofCrAnListF_ofCrAnListF (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs, ofCrAnListF φs']ₛca =
    ofCrAnListF (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnListF (φs' ++ φs)  := by

  exact round1_superCommuteF_ofCrAnListF_ofCrAnListF φs φs'
