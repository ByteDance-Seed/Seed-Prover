-- In FLT/FLT/HaarMeasure/DistribHaarChar/Basic.lean

/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import FLT.HaarMeasure.DomMulActMeasure

/-!
# The distributive character of Haar measures

Given a group `G` acting on an measurable additive commutative group `A`, and an element `g : G`,
one can pull back the Haar measure `μ` of `A` along the map `(g • ·) : A → A` to get another Haar
measure `μ'` on `A`. By unicity of Haar measures, there exists some nonnegative real number `r` such
that `μ' = r • μ`. We can thus define a map `distribHaarChar : G → ℝ≥0` sending `g` to its
associated real number `r`. Furthermore, this number doesn't depend on the Haar measure `μ` we
started with, and `distribHaarChar` is a group homomorphism.

## See also

[Zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/canonical.20norm.20coming.20from.20Haar.20measure/near/480050592)
-/

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory.Measure

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [MeasurableSpace A]
  [MeasurableSpace G] -- not needed actually
  [MeasurableSMul G A] -- only need `MeasurableConstSMul` but we don't have this class.
variable {μ ν : Measure A} {g : G}

variable [TopologicalSpace A] [BorelSpace A] [TopologicalAddGroup A] [LocallyCompactSpace A]
  [ContinuousConstSMul G A] [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

variable (μ A) in
@[simps (config := .lemmasOnly)]
noncomputable def distribHaarChar : G →* ℝ≥0 where
  toFun g := addHaarScalarFactor (DomMulAct.mk g • addHaar) (addHaar (G := A))
  map_one' := by simp
  map_mul' g g' := by
    simp_rw [DomMulAct.mk_mul]
    rw [addHaarScalarFactor_eq_mul _ (DomMulAct.mk g' • addHaar (G := A))]
    congr 1
    simp_rw [mul_smul]
    rw [addHaarScalarFactor_domSMul]

variable (μ) in

/- Start of proof attempt -/
lemma round1_h3 (g : G) (μ : Measure A) [μ.IsAddHaarMeasure] :
    addHaarScalarFactor (DomMulAct.mk g • μ) (DomMulAct.mk g • addHaar (G := A)) = addHaarScalarFactor μ (addHaar (G := A)) := by
  rw [addHaarScalarFactor_domSMul]

theorem addHaarScalarFactor_smul_eq_distribHaarChar (g : G) :
    addHaarScalarFactor (DomMulAct.mk g • μ) μ = distribHaarChar A g  := by

  have h11 : addHaarScalarFactor μ μ = 1 := by simp

  have h12 : addHaarScalarFactor μ μ = addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ := by
    rw [addHaarScalarFactor_eq_mul μ (addHaar (G := A)) μ]

  have h13 : (1 : ℝ≥0) = addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ := by
    have h131 : addHaarScalarFactor μ μ = 1 := h11
    have h132 : addHaarScalarFactor μ μ = addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ := h12
    rw [h131] at h132
    exact h132

  have h14 : addHaarScalarFactor (DomMulAct.mk g • μ) μ = addHaarScalarFactor (DomMulAct.mk g • μ) (DomMulAct.mk g • addHaar (G := A)) * addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) μ := by
    rw [addHaarScalarFactor_eq_mul (DomMulAct.mk g • μ) (DomMulAct.mk g • addHaar (G := A)) μ]

  have h15 : addHaarScalarFactor (DomMulAct.mk g • μ) (DomMulAct.mk g • addHaar (G := A)) = addHaarScalarFactor μ (addHaar (G := A)) := by
    exact round1_h3 g μ

  have h16 : addHaarScalarFactor (DomMulAct.mk g • μ) μ = addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) μ := by
    rw [h14, h15]

  have h17 : addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) μ = addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ := by
    rw [addHaarScalarFactor_eq_mul (DomMulAct.mk g • addHaar (G := A)) (addHaar (G := A)) μ]

  have h18 : distribHaarChar A g = addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) (addHaar (G := A)) := by
    simp [distribHaarChar]

  have h19 : addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) μ = distribHaarChar A g * addHaarScalarFactor (addHaar (G := A)) μ := by
    have h191 : addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) μ = addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ := h17
    have h192 : distribHaarChar A g = addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) (addHaar (G := A)) := by rw [h18]
    rw [h191]
    rw [h192]
    <;> ring

  have h20 : addHaarScalarFactor (DomMulAct.mk g • μ) μ = (addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ) * distribHaarChar A g := by
    calc
      addHaarScalarFactor (DomMulAct.mk g • μ) μ = addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (DomMulAct.mk g • addHaar (G := A)) μ := h16
      _ = addHaarScalarFactor μ (addHaar (G := A)) * (distribHaarChar A g * addHaarScalarFactor (addHaar (G := A)) μ) := by rw [h19]
      _ = (addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ) * distribHaarChar A g := by ring

  have h21 : addHaarScalarFactor (DomMulAct.mk g • μ) μ = (1 : ℝ≥0) * distribHaarChar A g := by
    rw [h20]
    have h211 : (1 : ℝ≥0) = addHaarScalarFactor μ (addHaar (G := A)) * addHaarScalarFactor (addHaar (G := A)) μ := h13
    rw [h211]
    <;> ring

  have h22 : (1 : ℝ≥0) * distribHaarChar A g = distribHaarChar A g := by simp

  rw [h21, h22]
