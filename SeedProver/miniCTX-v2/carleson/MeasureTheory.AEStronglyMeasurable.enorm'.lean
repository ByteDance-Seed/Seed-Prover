-- In carleson/Carleson/ToMathlib/ENorm.lean

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

noncomputable section

open ENNReal NNReal Function Set

variable {α α' E E₁ E₂ F : Type*} [ENorm F]

@[simp] lemma enorm_toReal_le {x : ℝ≥0∞} : ‖x.toReal‖ₑ ≤ x := by simp [← ofReal_norm, ofReal_toReal_le]

@[simp] lemma enorm_toReal {x : ℝ≥0∞} (hx : x ≠ ⊤) : ‖x.toReal‖ₑ = x := by
  simp [hx, ← ofReal_norm_eq_enorm]

/-- A type `E` equipped with a continuous map `‖·‖ₑ : E → ℝ≥0∞`.
Note: do we want to unbundle this (at least separate out `TopologicalSpace E`?)
Note: not sure if this is the "right" class to add to Mathlib. -/
class ContinuousENorm (E : Type*) extends ENorm E, TopologicalSpace E where
  continuous_enorm : Continuous enorm
  -- the topology is somehow defined by the enorm.

-- todo: maybe generalize to ENormedMonoid and use `to_additive` if necessary for Mathlib.
/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddMonoid (E : Type*) extends ContinuousENorm E, AddMonoid E where
  enorm_eq_zero : ∀ x : E, ‖x‖ₑ = 0 ↔ x = 0
  -- enorm_neg : ∀ x y : E, x + y = 0 → ‖x‖ₑ = ‖y‖ₑ -- this is a silly way to write this
  enorm_add_le : ∀ x y : E, ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommMonoid (E : Type*) extends ENormedAddMonoid E, AddCommMonoid E where

/-- An enormed monoid is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedAddCommSubMonoid (E : Type*) extends ENormedAddCommMonoid E, Sub E where
  sub_add_cancel_of_enorm_le : ∀ ⦃x y : E⦄, ‖y‖ₑ ≤ ‖x‖ₑ → x - y + y = x
  add_right_cancel_of_enorm_lt_top : ∀ ⦃x : E⦄, ‖x‖ₑ < ⊤ → ∀ {y z : E}, y + x = z + x → y = z
  esub_self : ∀ x : E, x - x = 0

/-- An enormed space is an additive monoid endowed with a continuous enorm.
Note: not sure if this is the "right" class to add to Mathlib. -/
class ENormedSpace (E : Type*) extends ENormedAddCommMonoid E, Module ℝ≥0 E where
  enorm_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export ENormedAddMonoid (enorm_eq_zero enorm_add_le)
export ENormedAddCommSubMonoid
  (sub_add_cancel_of_enorm_le add_right_cancel_of_enorm_lt_top esub_self)
export ENormedSpace (enorm_smul)

attribute [simp] ENormedAddMonoid.enorm_eq_zero ENormedSpace.enorm_smul

@[simp] lemma enorm_zero' {ε} [ENormedAddMonoid ε] : ‖(0 : ε)‖ₑ = 0 := by simp

instance : ENormedSpace ℝ≥0∞ where
  enorm := id
  enorm_eq_zero := by simp
  -- enorm_neg := by simp
  enorm_add_le := by simp
  add_comm := by simp [add_comm]
  continuous_enorm := continuous_id
  enorm_smul := by simp

instance [SeminormedAddGroup E] : ContinuousENorm E where
  continuous_enorm := ENNReal.continuous_coe.comp continuous_nnnorm

instance [NormedAddGroup E] : ENormedAddMonoid E where
  enorm_eq_zero := by simp [enorm_eq_nnnorm]
  -- enorm_neg := by
  --   simp (config := {contextual := true}) [← eq_neg_iff_add_eq_zero, enorm_eq_nnnorm]
  enorm_add_le := by simp [enorm_eq_nnnorm, ← ENNReal.coe_add, nnnorm_add_le]

instance [NormedAddCommGroup E] : ENormedAddCommMonoid E where
  add_comm := by simp [add_comm]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
  enorm_smul := by simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

namespace MeasureTheory
section ContinuousENorm
variable {α E : Type*} {m : MeasurableSpace α} [ContinuousENorm E] {μ : Measure α}

export ContinuousENorm (continuous_enorm)

@[fun_prop]
protected theorem Continuous.enorm {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) : Continuous (fun x => (‖f x‖ₑ)) :=
  continuous_enorm.comp hf

@[fun_prop]
theorem measurable_enorm [MeasurableSpace E] [OpensMeasurableSpace E] :
    Measurable (fun a : E => (‖a‖ₑ)) :=
  continuous_enorm.measurable

@[fun_prop]
protected theorem AEMeasurable.enorm [MeasurableSpace E] [OpensMeasurableSpace E] {f : α → E}
    (hf : AEMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ :=
  measurable_enorm.comp_aemeasurable hf

/- Start of proof attempt -/
lemma round1_main_proof {f : α → E} (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  have h3 : StronglyMeasurable (fun a => ‖g a‖ₑ) := by
    have h31 : Continuous (fun x : E => ‖x‖ₑ) := ContinuousENorm.continuous_enorm
    exact h31.comp_stronglyMeasurable hg
  have h4 : Measurable (fun a => ‖g a‖ₑ) := h3.measurable
  have h6 : AEMeasurable (fun a => ‖g a‖ₑ) μ := h4.aemeasurable
  have h5 : (fun a => ‖f a‖ₑ) =ᵐ[μ] (fun a => ‖g a‖ₑ) := by
    filter_upwards [hfg] with a ha
    simp [ha]
  have h7 : AEMeasurable (fun a => ‖f a‖ₑ) μ := by
    apply AEMeasurable.congr h6
    filter_upwards [h5] with a ha
    <;> simp_all
  exact h7

theorem AEStronglyMeasurable.enorm' {f : α → E}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖ₑ)) μ  := by

  exact round1_main_proof hf
