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

lemma integral_domSMul {α} [NormedAddCommGroup α] [NormedSpace ℝ α] (g : Gᵈᵐᵃ) (f : A → α) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

variable [TopologicalSpace A] [BorelSpace A] [TopologicalAddGroup A] [LocallyCompactSpace A]
  [ContinuousConstSMul G A] [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

instance : SMulCommClass ℝ≥0 Gᵈᵐᵃ (Measure A) where
  smul_comm r g μ := show r • μ.map _ = (r • μ).map _ by simp

instance : SMulCommClass Gᵈᵐᵃ ℝ≥0 (Measure A) := .symm ..

instance (g : Gᵈᵐᵃ) [Regular μ] : Regular (g • μ) :=
  Regular.map (μ := μ) (Homeomorph.smul ((DomMulAct.mk.symm g : G)⁻¹))

instance (g : Gᵈᵐᵃ) : (g • μ).IsAddHaarMeasure :=
  (DistribMulAction.toAddEquiv _ (DomMulAct.mk.symm g⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

variable (μ ν) in
lemma addHaarScalarFactor_domSMul (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ ν := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(A, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have int_f_ne_zero : ∫ x, f x ∂g • ν ≠ 0 :=
    (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'
  apply NNReal.coe_injective
  rw [addHaarScalarFactor_eq_integral_div (g • μ) (g • ν) f_cont f_comp int_f_ne_zero,
    integral_domSMul, integral_domSMul]
  refine (addHaarScalarFactor_eq_integral_div _ _ (by fun_prop) ?_ ?_).symm
  · exact f_comp.comp_isClosedEmbedding (Homeomorph.smul _).isClosedEmbedding
  · rw [← integral_domSMul]
    exact (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'

variable (μ) in
lemma addHaarScalarFactor_smul_congr (g : Gᵈᵐᵃ) :
    addHaarScalarFactor μ (g • μ) = addHaarScalarFactor ν (g • ν) := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_domSMul,
    mul_comm, ← addHaarScalarFactor_eq_mul]

variable (μ) in

/- Start of proof attempt -/
lemma round1_h1 (μ ν : Measure A) :
    ∀ (μ₁ : Measure A) [μ₁.IsAddHaarMeasure], addHaarScalarFactor μ₁ μ₁ = 1 := by
  intro μ₁ hμ₁
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(A, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have h141 : ∫ x, f x ∂μ₁ > 0 := f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero
  have h142 : ∫ x, f x ∂μ₁ ≠ 0 := by linarith
  have h143 : (addHaarScalarFactor μ₁ μ₁ : ℝ) = (∫ x, f x ∂μ₁) / (∫ x, f x ∂μ₁) := by
    rw [addHaarScalarFactor_eq_integral_div μ₁ μ₁ f_cont f_comp h142]
    <;> field_simp
  have h144 : (addHaarScalarFactor μ₁ μ₁ : ℝ) = 1 := by
    rw [h143]
    field_simp [h142]
    <;> ring
  exact_mod_cast h144

lemma round1_h2 (μ ν : Measure A) (h1 : ∀ (μ₁ : Measure A) [μ₁.IsAddHaarMeasure], addHaarScalarFactor μ₁ μ₁ = 1) :
    ∀ (μ₁ μ₂ : Measure A) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure], addHaarScalarFactor μ₁ μ₂ * addHaarScalarFactor μ₂ μ₁ = 1 := by
  intro μ₁ μ₂ hμ₁ hμ₂
  have h21 : (addHaarScalarFactor μ₁ μ₁ : ℝ) = (addHaarScalarFactor μ₁ μ₂ * addHaarScalarFactor μ₂ μ₁ : ℝ) := by
    have h := addHaarScalarFactor_eq_mul μ₁ μ₂ μ₁
    exact_mod_cast h
  have h22 : (addHaarScalarFactor μ₁ μ₁ : ℝ) = 1 := by exact_mod_cast h1 μ₁
  have h212 : (addHaarScalarFactor μ₁ μ₂ * addHaarScalarFactor μ₂ μ₁ : ℝ) = 1 := by
    linarith
  exact_mod_cast h212

theorem addHaarScalarFactor_smul_congr' (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) μ = addHaarScalarFactor (g • ν) ν  := by

  have h1 : ∀ (μ₁ : Measure A) [μ₁.IsAddHaarMeasure], addHaarScalarFactor μ₁ μ₁ = 1 := by
    exact round1_h1 μ ν

  have h2 : ∀ (μ₁ μ₂ : Measure A) [μ₁.IsAddHaarMeasure] [μ₂.IsAddHaarMeasure], addHaarScalarFactor μ₁ μ₂ * addHaarScalarFactor μ₂ μ₁ = 1 := by
    exact round1_h2 μ ν h1

  have h23 : addHaarScalarFactor (g • μ) μ * addHaarScalarFactor μ (g • μ) = 1 := by
    exact h2 (g • μ) μ

  have h24 : addHaarScalarFactor (g • ν) ν * addHaarScalarFactor ν (g • ν) = 1 := by
    exact h2 (g • ν) ν

  have h11 : addHaarScalarFactor μ (g • μ) = addHaarScalarFactor ν (g • ν) := addHaarScalarFactor_smul_congr μ g

  have h16 : (addHaarScalarFactor (g • μ) μ : ℝ) * (addHaarScalarFactor ν (g • ν) : ℝ) = 1 := by
    have h23' : (addHaarScalarFactor (g • μ) μ * addHaarScalarFactor μ (g • μ) : ℝ) = 1 := by exact_mod_cast h23
    have h11' : (addHaarScalarFactor μ (g • μ) : ℝ) = (addHaarScalarFactor ν (g • ν) : ℝ) := by exact_mod_cast h11
    rw [h11'] at h23'
    linarith

  have h17 : (addHaarScalarFactor (g • ν) ν : ℝ) * (addHaarScalarFactor ν (g • ν) : ℝ) = 1 := by exact_mod_cast h24

  have h19' : (addHaarScalarFactor ν (g • ν) : ℝ) ≠ 0 := by
    by_contra h
    have h191 : (addHaarScalarFactor (g • ν) ν : ℝ) * (addHaarScalarFactor ν (g • ν) : ℝ) = 0 := by
      rw [h]
      ring
    linarith

  have h20 : (addHaarScalarFactor (g • μ) μ : ℝ) * (addHaarScalarFactor ν (g • ν) : ℝ) = (addHaarScalarFactor (g • ν) ν : ℝ) * (addHaarScalarFactor ν (g • ν) : ℝ) := by
    linarith

  have h21 : (addHaarScalarFactor (g • μ) μ : ℝ) = (addHaarScalarFactor (g • ν) ν : ℝ) := by
    apply (mul_right_inj' h19').mp
    linarith

  exact_mod_cast h21
