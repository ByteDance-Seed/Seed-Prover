-- In FLT/FLT/HaarMeasure/DomMulActMeasure.lean

/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory.Measure

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [MeasurableSpace A]
  -- We only need `MeasurableConstSMul G A` but we don't have this class. So we erroneously must
  -- assume `MeasurableSpace G` + `MeasurableSMul G A`
  [MeasurableSpace G] [MeasurableSMul G A]
variable {μ ν : Measure A} {g : G}

lemma domSMul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) :
    (g • μ) s = μ ((DomMulAct.mk.symm g) • s) := by
  refine ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)).map_apply _).trans ?_
  congr 1
  exact Set.preimage_smul_inv (DomMulAct.mk.symm g) s


/- Start of proof attempt -/
lemma round1_h4 (g : Gᵈᵐᵃ) :
  ∀ (s : Set A), (g • μ) s = (Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) s := by
  intro s
  have h41 : (g • μ) s = μ ((DomMulAct.mk.symm g) • s) := domSMul_apply μ g s
  have h44 : (DomMulAct.mk.symm g) • s = (MeasurableEquiv.smul ((DomMulAct.mk.symm g)⁻¹)) ⁻¹' s := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MeasurableEquiv.smul_apply]
      have h5 : (DomMulAct.mk.symm g)⁻¹ • ((DomMulAct.mk.symm g) • y) = y := by
        calc
          (DomMulAct.mk.symm g)⁻¹ • ((DomMulAct.mk.symm g) • y) = ((DomMulAct.mk.symm g)⁻¹ * (DomMulAct.mk.symm g)) • y := by rw [mul_smul]
          _ = (1 : G) • y := by rw [inv_mul_self]
          _ = y := by simp
      rw [h5]
      exact hy
    · intro h6
      refine ⟨(DomMulAct.mk.symm g)⁻¹ • x, h6,?_⟩
      have h7 : (DomMulAct.mk.symm g) • ((DomMulAct.mk.symm g)⁻¹ • x) = x := by
        calc
          (DomMulAct.mk.symm g) • ((DomMulAct.mk.symm g)⁻¹ • x) = ((DomMulAct.mk.symm g) * (DomMulAct.mk.symm g)⁻¹) • x := by rw [mul_smul]
          _ = (1 : G) • x := by rw [mul_inv_self]
          _ = x := by simp
      exact h7
  have h45 : μ ((DomMulAct.mk.symm g) • s) = μ ((MeasurableEquiv.smul ((DomMulAct.mk.symm g)⁻¹)) ⁻¹' s) := by rw [h44]
  have h46 : (Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) s = μ ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) ⁻¹' s) := by
    simp [Measure.map_apply]
    <;> aesop
  have h47 : (g • μ) s = μ ((MeasurableEquiv.smul ((DomMulAct.mk.symm g)⁻¹)) ⁻¹' s) := by rw [h41, h45]
  have h48 : (Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) s = μ ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) ⁻¹' s) := by rw [h46]
  rw [h47, h48]

lemma round1_h5 (g : Gᵈᵐᵃ) (h4 : ∀ (s : Set A), (g • μ) s = (Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) s) :
  g • μ = Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ := by
  ext s
  exact h4 s

theorem integral_domSMul {α} [NormedAddCommGroup α] [NormedSpace ℝ α] (g : Gᵈᵐᵃ) (f : A → α) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ  := by


  have h4 : ∀ (s : Set A), (g • μ) s = (Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) s := by
    exact round1_h4 g

  have h5 : g • μ = Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ := by
    exact round1_h5 g h4

  have h9 : ∫ x, f x ∂g • μ = ∫ x, f x ∂(Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) := by
    rw [h5]

  have h10 : ∫ x, f x ∂(Measure.map (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) μ) = ∫ x, f ((DomMulAct.mk.symm g : G)⁻¹ • x) ∂μ := by
    rw [MeasureTheory.integral_map_equiv]
    <;> simp

  rw [h9, h10]
