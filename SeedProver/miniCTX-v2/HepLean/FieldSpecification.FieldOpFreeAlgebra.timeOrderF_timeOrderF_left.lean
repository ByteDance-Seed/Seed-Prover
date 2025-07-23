-- In HepLean/HepLean/PerturbationTheory/FieldOpFreeAlgebra/TimeOrder.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Time Ordering in the FieldOpFreeAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section
open HepLean.List
/-!

## Time order

-/

/-- For a field specification `𝓕`, `timeOrderF` is the linear map

  `FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕`

  defined by its action on the basis `ofCrAnListF φs`, taking
  `ofCrAnListF φs` to

  `crAnTimeOrderSign φs • ofCrAnListF (crAnTimeOrderList φs)`.

  That is, `timeOrderF` time-orders the field operators and multiplies by the sign of the
  time order.

  The notation `𝓣ᶠ(a)` is used for `timeOrderF a` -/
def timeOrderF : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  crAnTimeOrderSign φs • ofCrAnListF (crAnTimeOrderList φs)

@[inherit_doc timeOrderF]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓣ᶠ(" a ")" => timeOrderF a

lemma timeOrderF_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    𝓣ᶠ(ofCrAnListF φs) = crAnTimeOrderSign φs • ofCrAnListF (crAnTimeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [timeOrderF, Basis.constr_basis]

lemma timeOrderF_timeOrderF_mid (a b c : 𝓕.FieldOpFreeAlgebra) :
    𝓣ᶠ(a * b * c) = 𝓣ᶠ(a * 𝓣ᶠ(b) * c) := by
  let pc (c : 𝓕.FieldOpFreeAlgebra) (hc : c ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
    Prop := 𝓣ᶠ(a * b * c) = 𝓣ᶠ(a * 𝓣ᶠ(b) * c)
  change pc c (Basis.mem_span _ c)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList, pc]
    let pb (b : 𝓕.FieldOpFreeAlgebra) (hb : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
      Prop := 𝓣ᶠ(a * b * ofCrAnListF φs) = 𝓣ᶠ(a * 𝓣ᶠ(b) * ofCrAnListF φs)
    change pb b (Basis.mem_span _ b)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp only [ofListBasis_eq_ofList, pb]
      let pa (a : 𝓕.FieldOpFreeAlgebra) (ha : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
        Prop := 𝓣ᶠ(a * ofCrAnListF φs' * ofCrAnListF φs) =
          𝓣ᶠ(a * 𝓣ᶠ(ofCrAnListF φs') * ofCrAnListF φs)
      change pa a (Basis.mem_span _ a)
      apply Submodule.span_induction
      · intro x hx
        obtain ⟨φs'', rfl⟩ := hx
        simp only [ofListBasis_eq_ofList, pa]
        rw [timeOrderF_ofCrAnListF]
        simp only [← ofCrAnListF_append, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, map_smul]
        rw [timeOrderF_ofCrAnListF, timeOrderF_ofCrAnListF, smul_smul]
        congr 1
        · simp only [crAnTimeOrderSign, crAnTimeOrderList]
          rw [Wick.koszulSign_of_append_eq_insertionSort, mul_comm]
        · congr 1
          simp only [crAnTimeOrderList]
          rw [insertionSort_append_insertionSort_append]
      · simp [pa]
      · intro x y hx hy h1 h2
        simp_all [pa, add_mul]
      · intro x hx h
        simp_all [pa]
    · simp [pb]
    · intro x y hx hy h1 h2
      simp_all [pb, mul_add, add_mul]
    · intro x hx h
      simp_all [pb]
  · simp [pc]
  · intro x y hx hy h1 h2
    simp_all [pc, mul_add]
  · intro x hx h hp
    simp_all [pc]

lemma timeOrderF_timeOrderF_right (a b : 𝓕.FieldOpFreeAlgebra) : 𝓣ᶠ(a * b) = 𝓣ᶠ(a * 𝓣ᶠ(b)) := by
  trans 𝓣ᶠ(a * b * 1)
  · simp
  · rw [timeOrderF_timeOrderF_mid]
    simp

/- Start of proof attempt -/
lemma round1_timeOrderF_timeOrderF_left (a b : 𝓕.FieldOpFreeAlgebra) : 
  𝓣ᶠ(a * b) = 𝓣ᶠ(𝓣ᶠ(a) * b) := by
  have h := timeOrderF_timeOrderF_mid (1 : 𝓕.FieldOpFreeAlgebra) a b
  simpa using h

theorem timeOrderF_timeOrderF_left (a b : 𝓕.FieldOpFreeAlgebra) : 𝓣ᶠ(a * b) = 𝓣ᶠ(𝓣ᶠ(a) * b)  := by

  exact round1_timeOrderF_timeOrderF_left a b
