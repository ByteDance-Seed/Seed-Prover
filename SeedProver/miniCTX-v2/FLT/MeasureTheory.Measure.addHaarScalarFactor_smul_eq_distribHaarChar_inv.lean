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

/- Start of proof attempt -/
lemma round1_h2 (G A : Type*) [Group G] [AddCommGroup A] [DistribMulAction G A] (g : G) :
  (DomMulAct.mk (g⁻¹))⁻¹ = DomMulAct.mk g := by
  simp [DomMulAct.mk_inv]
  <;> group

lemma round1_h3 (g : G) : distribHaarChar A g⁻¹ = (distribHaarChar A g)⁻¹ := by
  simp [MonoidHom.map_inv]

theorem addHaarScalarFactor_smul_eq_distribHaarChar_inv (g : G) :
    addHaarScalarFactor μ (DomMulAct.mk g • μ) = (distribHaarChar A g)⁻¹  := by

  have h1 : addHaarScalarFactor μ ((DomMulAct.mk (g⁻¹))⁻¹ • μ) = distribHaarChar A (g⁻¹) := by
    exact addHaarScalarFactor_smul_inv_eq_distribHaarChar μ (g⁻¹)
  have h2 : (DomMulAct.mk (g⁻¹))⁻¹ = DomMulAct.mk g := by
    exact round1_h2 G A g
  have h1' : addHaarScalarFactor μ (DomMulAct.mk g • μ) = distribHaarChar A (g⁻¹) := by
    rw [h2] at h1
    exact h1
  have h3 : distribHaarChar A (g⁻¹) = (distribHaarChar A g)⁻¹ := by
    exact round1_h3 g
  rw [h1']
  rw [h3]
