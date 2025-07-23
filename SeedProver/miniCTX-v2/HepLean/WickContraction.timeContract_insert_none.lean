-- In HepLean/HepLean/PerturbationTheory/WickContraction/TimeContract.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Sign.Basic
import HepLean.PerturbationTheory.FieldOpAlgebra.TimeContraction
/-!

# Time contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

/-- For a list `φs` of `𝓕.FieldOp` and a Wick contraction `φsΛ` the
  element of the center of `𝓕.FieldOpAlgebra`, `φsΛ.timeContract` is defined as the product
  of `timeContract φs[j] φs[k]` over contracted pairs `{j, k}` in `φsΛ`
  with `j < k`. -/
noncomputable def timeContract {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    Subalgebra.center ℂ 𝓕.FieldOpAlgebra :=
  ∏ (a : φsΛ.1), ⟨FieldOpAlgebra.timeContract
    (φs.get (φsΛ.fstFieldOfContract a)) (φs.get (φsΛ.sndFieldOfContract a)),
    timeContract_mem_center _ _⟩

/- Start of proof attempt -/
lemma round1_h1 (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).timeContract = φsΛ.timeContract := by
  have h51 := WickContraction.insertAndContract_none_prod_contractions φ φs φsΛ i
    (fun a => (⟨FieldOpAlgebra.timeContract ((List.insertIdx (↑i) φ φs).get ((WickContraction.insertAndContract φ φsΛ i none).fstFieldOfContract a)) ((List.insertIdx (↑i) φ φs).get ((WickContraction.insertAndContract φ φsΛ i none).sndFieldOfContract a)), timeContract_mem_center _ _⟩ : Subalgebra.center ℂ 𝓕.FieldOpAlgebra))
  simpa [timeContract] using h51

/-- For a list `φs = φ₀…φₙ` of `𝓕.FieldOp`, a Wick contraction `φsΛ` of `φs`, an element `φ` of
  `𝓕.FieldOp`, and a `i ≤ φs.length` the following relation holds

  `(φsΛ ↩Λ φ i none).timeContract = φsΛ.timeContract`

  The prove of this result ultimately a consequence of definitions. -/
theorem timeContract_insert_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).timeContract = φsΛ.timeContract  := by

  exact round1_h1 φ φs φsΛ i
