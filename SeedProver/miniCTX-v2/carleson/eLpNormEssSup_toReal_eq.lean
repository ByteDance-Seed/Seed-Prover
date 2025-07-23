-- In carleson/Carleson/ToMathlib/WeakType.lean

import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Carleson.ToMathlib.ENorm
import Carleson.ToMathlib.Misc

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set Filter Topology Function

section move

variable {α 𝕜 E : Type*} {m : MeasurableSpace α}
  {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {p : ℝ≥0∞}

-- todo: move/rename/and perhaps reformulate in terms of ‖.‖ₑ
lemma ENNNorm_absolute_homogeneous {c : 𝕜} (z : E) : ofNNReal ‖c • z‖₊ = ↑‖c‖₊ * ↑‖z‖₊ :=
  (toReal_eq_toReal_iff' coe_ne_top coe_ne_top).mp (norm_smul c z)

lemma ENNNorm_add_le (y z : E) : ofNNReal ‖y + z‖₊ ≤ ↑‖y‖₊ + ↑‖z‖₊ :=
  (toReal_le_toReal coe_ne_top coe_ne_top).mp (nnnorm_add_le ..)

lemma measure_mono_ae' {A B : Set α} (h : μ (B \ A) = 0) :
    μ B ≤ μ A := by
  apply measure_mono_ae
  change μ {x | ¬ B x ≤ A x} = 0
  simp only [le_Prop_eq, Classical.not_imp]
  exact h

lemma eLpNormEssSup_toReal_le {f : α → ℝ≥0∞} :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  apply essSup_mono_ae
  apply Eventually.of_forall
  simp [implies_true]

/- Start of proof attempt -/
lemma round1_h2 (f : α → ℝ≥0∞) :
    eLpNormEssSup f μ = essSup f μ := by
  have h21 : ∀ x : α, ‖f x‖ₑ = f x := by
    intro x
    simp
  have h22 : (fun x : α => ‖f x‖ₑ) = f := by
    funext x
    exact h21 x
  have h23 : essSup (fun x => ‖f x‖ₑ) μ = essSup f μ := by
    rw [h22]
  have h24 : eLpNormEssSup f μ = essSup (fun x => ‖f x‖ₑ) μ := by
    simp [eLpNormEssSup]
  rw [h24]
  exact h23

lemma round1_h3 (f : α → ℝ≥0∞) (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ = essSup f μ := by
  have h31 : eLpNormEssSup (ENNReal.toReal ∘ f) μ = essSup (fun x => ‖(ENNReal.toReal ∘ f) x‖ₑ) μ := by
    simp [eLpNormEssSup]
  have h32 : ∀ᵐ x ∂μ, ‖(ENNReal.toReal ∘ f) x‖ₑ = f x := by
    filter_upwards [hf] with x hx
    have h321 : ‖(f x).toReal‖ₑ = f x := by
      simp [ENNReal.ofReal_toReal, hx]
      <;> aesop
    simpa using h321
  have h33 : essSup (fun x => ‖(ENNReal.toReal ∘ f) x‖ₑ) μ = essSup f μ := by
    apply essSup_congr_ae
    filter_upwards [h32] with x hx
    <;> simp_all
  rw [h31]
  exact h33

theorem eLpNormEssSup_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ = eLpNormEssSup f μ  := by

  have h2 : eLpNormEssSup f μ = essSup f μ := by
    exact round1_h2 f
  have h3 : eLpNormEssSup (ENNReal.toReal ∘ f) μ = essSup f μ := by
    exact round1_h3 f hf
  have h4 : eLpNormEssSup (ENNReal.toReal ∘ f) μ = essSup f μ := h3
  have h5 : essSup f μ = eLpNormEssSup f μ := by
    rw [h2]
    <;> rfl
  rw [h4, h5]
