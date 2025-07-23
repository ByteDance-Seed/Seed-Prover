-- In HepLean/HepLean/PerturbationTheory/WickContraction/ExtractEquiv.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.InsertAndContractNat
/-!

# Equivalence extracting element from contraction

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

/- Start of proof attempt -/
lemma round1_extractEquiv_equiv {c1 c2 : (c : WickContraction n) × Option c.uncontracted}
    (h : c1.1 = c2.1) (ho : c1.2 = WickContraction.uncontractedCongr (by rw [h]) c2.2) : c1 = c2 := by
  rcases c1 with ⟨c1_fst, c1_snd⟩
  rcases c2 with ⟨c2_fst, c2_snd⟩
  have h1 : c1_fst = c2_fst := h
  subst h1
  have h2 : c1_snd = c2_snd := by
    simp_all [WickContraction.uncontractedCongr_none, WickContraction.uncontractedCongr_some]
    <;>
    (try aesop) <;>
    (try
      {
        cases c2_snd <;> simp_all [WickContraction.uncontractedCongr_none, WickContraction.uncontractedCongr_some] <;>
        aesop
      }) <;>
    (try
      {
        simp_all [Subtype.ext_iff_val]
        <;> aesop
      })
    <;>
    aesop
  simp [Prod.ext_iff, h2]
  <;> aesop

theorem extractEquiv_equiv {c1 c2 : (c : WickContraction n) × Option c.uncontracted}
    (h : c1.1 = c2.1) (ho : c1.2 = uncontractedCongr (by rw [h]) c2.2) : c1 = c2  := by

  exact round1_extractEquiv_equiv h ho
