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

lemma eLpNormEssSup_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNormEssSup (ENNReal.toReal ∘ f) μ = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, enorm_eq_self]
  apply essSup_congr_ae
  filter_upwards [hf] with x hx
  simp [hx]

lemma eLpNorm'_toReal_le {f : α → ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ ≤ eLpNorm' f p μ := by
  simp_rw [eLpNorm', enorm_eq_self]
  gcongr
  simp

lemma eLpNorm'_toReal_eq {f : α → ℝ≥0∞} {p : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm' (ENNReal.toReal ∘ f) p μ = eLpNorm' f p μ := by
  simp_rw [eLpNorm', enorm_eq_self]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hf] with x hx
  simp [hx]

lemma eLpNorm_toReal_le {f : α → ℝ≥0∞} :
    eLpNorm (ENNReal.toReal ∘ f) p μ ≤ eLpNorm f p μ := by
  simp_rw [eLpNorm]
  split_ifs
  · rfl
  · exact eLpNormEssSup_toReal_le
  · exact eLpNorm'_toReal_le toReal_nonneg

lemma eLpNorm_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    eLpNorm (ENNReal.toReal ∘ f) p μ = eLpNorm f p μ := by
  simp_rw [eLpNorm]
  split_ifs
  · rfl
  · exact eLpNormEssSup_toReal_eq hf
  · exact eLpNorm'_toReal_eq hf

end move

namespace MeasureTheory

variable {α α' ε ε₁ ε₂ ε₃ 𝕜 E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  (L : E₁ →L[𝕜] E₂ →L[𝕜] E₃)
  {t s x y : ℝ≥0∞}
  {T : (α → ε₁) → (α' → ε₂)}

section ENorm

variable [ENorm ε] {f g g₁ g₂ : α → ε}

/- Proofs for this file can be found in
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.3. -/

/-! # The distribution function `d_f` -/

/-- The distribution function of a function `f`.
Note that unlike the notes, we also define this for `t = ∞`.
Note: we also want to use this for functions with codomain `ℝ≥0∞`, but for those we just write
`μ { x | t < f x }` -/
def distribution (f : α → ε) (t : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  μ { x | t < ‖f x‖ₑ }

@[gcongr]
lemma distribution_mono_right (h : t ≤ s) : distribution f s μ ≤ distribution f t μ :=
  measure_mono fun _ a ↦ lt_of_le_of_lt h a

lemma distribution_mono_right' : (Antitone (fun t ↦ distribution f t μ)) :=
  fun _ _ h ↦ distribution_mono_right h

@[measurability, fun_prop]
lemma distribution_measurable₀ : Measurable (fun t ↦ distribution f t μ) :=
  Antitone.measurable (distribution_mono_right' (f := f) (μ := μ))

@[measurability, fun_prop]
lemma distribution_measurable {g : α' → ℝ≥0∞} (hg : Measurable g) :
    Measurable (fun y : α' ↦ distribution f (g y) μ) := by
  fun_prop

lemma distribution_toReal_le {f : α → ℝ≥0∞} :
    distribution (ENNReal.toReal ∘ f) t μ ≤ distribution f t μ := by
  simp_rw [distribution]
  apply measure_mono
  simp_rw [comp_apply, enorm_eq_self, setOf_subset_setOf]
  intro x hx
  exact hx.trans_le enorm_toReal_le

lemma distribution_toReal_eq {f : α → ℝ≥0∞} (hf : ∀ᵐ x ∂μ, f x ≠ ∞) :
    distribution (ENNReal.toReal ∘ f) t μ = distribution f t μ := by
  refine measure_congr (.set_eq ?_)
  filter_upwards [hf] with x hx
  simp [hx]

/- Start of proof attempt -/
lemma round1_h2 (A : ℝ≥0∞)
  (f g₁ g₂ : α → ε)
  (t s : ℝ≥0∞):
  ∀ x, (‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) → (A * (t + s) < ‖f x‖ₑ → (t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ)) := by
  intro x h1 h21
  by_contra h3
  have h5 : ¬(t < ‖g₁ x‖ₑ) := by tauto
  have h6 : ¬(s < ‖g₂ x‖ₑ) := by tauto
  have h71 : ‖g₁ x‖ₑ ≤ t ∨ t < ‖g₁ x‖ₑ := by
    exact?
  have h81 : ‖g₂ x‖ₑ ≤ s ∨ s < ‖g₂ x‖ₑ := by
    exact?
  have h7 : ‖g₁ x‖ₑ ≤ t := by
    cases h71 with
    | inl h71 =>
      exact h71
    | inr h71 =>
      contradiction
  have h8 : ‖g₂ x‖ₑ ≤ s := by
    cases h81 with
    | inl h81 =>
      exact h81
    | inr h81 =>
      contradiction
  have h9 : ‖g₁ x‖ₑ + ‖g₂ x‖ₑ ≤ t + s := by
    gcongr <;> tauto
  have h10 : A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ) ≤ A * (t + s) := by
    gcongr <;> tauto
  have h11 : ‖f x‖ₑ ≤ A * (t + s) := by
    calc
      ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ) := h1
      _ ≤ A * (t + s) := h10
  have h14 : A * (t + s) < A * (t + s) := by
    exact lt_of_lt_of_le h21 h11
  exact lt_irrefl (A * (t + s)) h14

lemma round1_h3 (A : ℝ≥0∞)
  (f g₁ g₂ : α → ε)
  (t s : ℝ≥0∞)
  (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ))
  (h2 : ∀ x, (‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) → (A * (t + s) < ‖f x‖ₑ → (t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ))):
  ∀ᵐ x ∂μ, (A * (t + s) < ‖f x‖ₑ → (t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ)) := by
  filter_upwards [h] with x hx
  exact h2 x hx

lemma round1_h4 (A : ℝ≥0∞)
  (f g₁ g₂ : α → ε)
  (t s : ℝ≥0∞)
  (h3 : ∀ᵐ x ∂μ, (A * (t + s) < ‖f x‖ₑ → (t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ))):
  ∀ᵐ x ∂μ, (x ∈ {x | A * (t + s) < ‖f x‖ₑ} → x ∈ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) := by
  filter_upwards [h3] with x h3
  intro h5
  have h5' : A * (t + s) < ‖f x‖ₑ := by simpa using h5
  have h6 : t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ := h3 h5'
  cases h6 with
  | inl h6 =>
    have h9 : x ∈ {x | t < ‖g₁ x‖ₑ} := by
      simp only [Set.mem_setOf_eq]
      exact h6
    have h10 : x ∈ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := by
      apply Or.inl
      exact h9
    exact h10
  | inr h6 =>
    have h9 : x ∈ {x | s < ‖g₂ x‖ₑ} := by
      simp only [Set.mem_setOf_eq]
      exact h6
    have h10 : x ∈ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := by
      apply Or.inr
      exact h9
    exact h10

lemma round1_h5 (A : ℝ≥0∞)
  (f g₁ g₂ : α → ε)
  (t s : ℝ≥0∞)
  (h4 : ∀ᵐ x ∂μ, (x ∈ {x | A * (t + s) < ‖f x‖ₑ} → x ∈ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}))):
  μ ({x | A * (t + s) < ‖f x‖ₑ} \ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
  have h51 : ∀ᵐ x ∂μ, x ∉ ({x | A * (t + s) < ‖f x‖ₑ} \ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) := by
    filter_upwards [h4] with x h4x
    intro h52
    have h521 : x ∈ {x | A * (t + s) < ‖f x‖ₑ} := h52.1
    have h522 : x ∉ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := h52.2
    have h53 : x ∈ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := h4x h521
    contradiction
  have h54 : μ ({x | A * (t + s) < ‖f x‖ₑ} \ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
    apply measure_zero_iff_ae_nmem.mpr
    exact h51
  exact h54

lemma round1_h6 (A : ℝ≥0∞)
  (f g₁ g₂ : α → ε)
  (t s : ℝ≥0∞)
  (h5 : μ ({x | A * (t + s) < ‖f x‖ₑ} \ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0):
  μ {x | A * (t + s) < ‖f x‖ₑ} ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := by
  exact measure_mono_ae' h5

theorem distribution_add_le_of_enorm {A : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) :
    distribution f (A * (t + s)) μ ≤ distribution g₁ t μ + distribution g₂ s μ  := by

  have h2 : ∀ x, (‖f x‖ₑ ≤ A * (‖g₁ x‖ₑ + ‖g₂ x‖ₑ)) → (A * (t + s) < ‖f x‖ₑ → (t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ)) := by
    exact round1_h2 A f g₁ g₂ t s
  have h3 : ∀ᵐ x ∂μ, (A * (t + s) < ‖f x‖ₑ → (t < ‖g₁ x‖ₑ ∨ s < ‖g₂ x‖ₑ)) := by
    exact round1_h3 A f g₁ g₂ t s h h2
  have h4 : ∀ᵐ x ∂μ, (x ∈ {x | A * (t + s) < ‖f x‖ₑ} → x ∈ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) := by
    exact round1_h4 A f g₁ g₂ t s h3
  have h5 : μ ({x | A * (t + s) < ‖f x‖ₑ} \ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ})) = 0 := by
    exact round1_h5 A f g₁ g₂ t s h4
  have h6 : μ {x | A * (t + s) < ‖f x‖ₑ} ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := by
    exact round1_h6 A f g₁ g₂ t s h5
  have h7 : μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := by
    apply measure_union_le
  have h_final : μ {x | A * (t + s) < ‖f x‖ₑ} ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := by
    calc
      μ {x | A * (t + s) < ‖f x‖ₑ} ≤ μ ({x | t < ‖g₁ x‖ₑ} ∪ {x | s < ‖g₂ x‖ₑ}) := h6
      _ ≤ μ {x | t < ‖g₁ x‖ₑ} + μ {x | s < ‖g₂ x‖ₑ} := h7
  simp only [distribution] at *
  exact h_final
