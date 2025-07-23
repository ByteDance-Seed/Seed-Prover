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
lemma addHaarScalarFactor_smul_eq_distribHaarChar (g : G) :
    addHaarScalarFactor (DomMulAct.mk g • μ) μ = distribHaarChar A g :=
  addHaarScalarFactor_smul_congr' ..

variable (μ) in
lemma addHaarScalarFactor_smul_inv_eq_distribHaarChar (g : G) :
    addHaarScalarFactor μ ((DomMulAct.mk g)⁻¹ • μ) = distribHaarChar A g := by
  rw [← addHaarScalarFactor_domSMul _ _ (DomMulAct.mk g)]
  simp_rw [← mul_smul, mul_inv_cancel, one_smul]
  exact addHaarScalarFactor_smul_eq_distribHaarChar ..

variable (μ) in
lemma addHaarScalarFactor_smul_eq_distribHaarChar_inv (g : G) :
    addHaarScalarFactor μ (DomMulAct.mk g • μ) = (distribHaarChar A g)⁻¹ := by
  rw [← map_inv, ← addHaarScalarFactor_smul_inv_eq_distribHaarChar μ, DomMulAct.mk_inv, inv_inv]

/- Start of proof attempt -/
lemma round1_h (f : G →* ℝ≥0) (g : G) : 0 < f g := by
  have h11 : f (g * g⁻¹) = f g * f g⁻¹ := by
    exact?
  have h12 : g * g⁻¹ = 1 := by
    group
  have h13 : f (g * g⁻¹) = f 1 := by rw [h12]
  have h14 : f 1 = 1 := by
    exact?
  have h15 : f g * f g⁻¹ = 1 := by
    calc
      f g * f g⁻¹ = f (g * g⁻¹) := by rw [h11]
      _ = f 1 := by rw [h13]
      _ = 1 := by simpa using h14
  have h16 : (f g : ℝ≥0) ≥ 0 := by positivity
  have h17 : (f g : ℝ≥0) ≠ 0 := by
    by_contra h17
    have h18 : (f g : ℝ≥0) = 0 := by tauto
    have h19 : (f g : ℝ≥0) * (f g⁻¹ : ℝ≥0) = 0 := by
      rw [h18]
      <;> simp
    have h20 : (f g : ℝ≥0) * (f g⁻¹ : ℝ≥0) = 1 := by exact_mod_cast h15
    rw [h19] at h20
    norm_num at h20
    <;> contradiction
  have h21 : (0 : ℝ≥0) < f g := by
    by_contra h21
    have h22 : ¬(0 : ℝ≥0) < f g := h21
    have h23 : (f g : ℝ≥0) ≤ 0 := by
      exact?
    have h24 : (f g : ℝ≥0) = 0 := by
      have h241 : (0 : ℝ≥0) ≤ (f g : ℝ≥0) := by positivity
      have h242 : (f g : ℝ≥0) ≤ 0 := h23
      have h243 : (f g : ℝ≥0) = 0 := by
        exact le_antisymm h242 h241
      exact h243
    have h25 : (f g : ℝ≥0) = 0 := h24
    contradiction
  exact_mod_cast h21

theorem distribHaarChar_pos : 0 < distribHaarChar A g  := by

  have h1 : ∀ (f : G →* ℝ≥0) (g : G), 0 < f g := by
    intro f g
    exact round1_h f g
  exact h1 (distribHaarChar A) g
