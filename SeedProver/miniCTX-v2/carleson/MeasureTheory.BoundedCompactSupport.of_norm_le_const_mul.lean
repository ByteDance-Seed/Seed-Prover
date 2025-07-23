-- In carleson/Carleson/ToMathlib/BoundedCompactSupport.lean

/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos, Sébastien Gouëzel
-/

import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.ENatENNReal
import Carleson.ToMathlib.Misc

/-!

EXPERIMENTAL

# Bounded compactly supported functions

The purpose of this file is to provide helper lemmas to streamline proofs that
functions are (essentially) bounded, compactly supported and measurable.

Most functions we need to deal with are of this class.
This can be a useful way to streamline proofs of `L^p` membership,
in particular integrability.

Todo: make `Mathlib.Tactic.FunProp` work for this

This can be expanded as needed

-/

set_option linter.unusedSectionVars false -- remove for mathlib

namespace MeasureTheory

open Bornology Function Set HasCompactSupport
open scoped ENNReal

section

-- This setting should be enough for this project, but
-- for mathlib should generalize to vector-valued, and use `MeasurableSpace X`, `Measure μ`
variable {X 𝕜} [MeasurableSpace X] [RCLike 𝕜] {f : X → 𝕜} {μ : Measure X}
variable [TopologicalSpace X]
-- variable [T2Space X] -- for mathlib should remove this
-- variable [IsFiniteMeasureOnCompacts μ]
-- variable [SigmaFinite (volume : Measure X)]

/-- Bounded compactly supported measurable functions -/
-- There are various alternative definitions one could use here
-- After all it does seem to be better to use `IsBounded (range f)`
-- Todo: Refactor accordingly
structure BoundedCompactSupport (f : X → 𝕜) : Prop where
  isBounded : IsBounded (range f)
  stronglyMeasurable : StronglyMeasurable f
  hasCompactSupport : HasCompactSupport f

lemma isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by convert isBounded_iff_forall_norm_le; simp

omit [TopologicalSpace X] in
lemma _root_.Bornology.IsBounded.eLpNorm_top_lt_top (hf : IsBounded (range f)) :
    eLpNorm f ⊤ μ < ⊤ := by
  obtain ⟨C, hC⟩ := isBounded_range_iff_forall_norm_le.mp hf
  apply eLpNormEssSup_lt_top_of_ae_bound (C := C)
  exact ae_of_all μ hC

omit [TopologicalSpace X] in
-- maybe in mathlib, but couldn't find it
theorem ae_le_of_eLpNorm_top_lt_top (hf : eLpNorm f ⊤ μ < ⊤) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤ μ) := by
  have := coe_nnnorm_ae_le_eLpNormEssSup f μ
  filter_upwards [this] with x hx
  have : ENNReal.ofReal ‖f x‖₊ ≠ ⊤ := ENNReal.ofReal_ne_top
  convert (ENNReal.toReal_le_toReal this ?_).mpr ?_
  · simp
  · exact hf.ne_top
  · exact trans ENNReal.ofReal_coe_nnreal hx

namespace BoundedCompactSupport

protected theorem zero : BoundedCompactSupport (fun (_ : X) ↦ (0 : 𝕜)) where
  isBounded := isBounded_range_iff_forall_norm_le.2 ⟨0, by simp⟩
  stronglyMeasurable := stronglyMeasurable_const
  hasCompactSupport := HasCompactSupport.zero

theorem indicator_of_isBounded_range {X : Type*} [MetricSpace X] [ProperSpace X]
    [MeasurableSpace X] [BorelSpace X] {f : X → 𝕜} (hf : IsBounded (range f))
    (h'f : StronglyMeasurable f) {s : Set X} (h's : IsBounded s) (hs : MeasurableSet s) :
    BoundedCompactSupport (s.indicator f) where
  stronglyMeasurable := h'f.indicator hs
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf with ⟨C, hC⟩
    apply isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
    simp only [indicator]
    split_ifs
    · exact hC x
    · simp only [norm_zero]
      apply (norm_nonneg _).trans (hC x)
  hasCompactSupport := by
    apply HasCompactSupport.intro (K := closure s)
    · apply Metric.isCompact_of_isClosed_isBounded isClosed_closure h's.closure
    · intro x hx
      have : x ∉ s := by
        contrapose! hx; exact subset_closure hx
      simp [this]

variable {f : X → 𝕜}
variable {g : X → 𝕜}

variable (hf : BoundedCompactSupport f)
variable (hg : BoundedCompactSupport g)

section Includehf

include hf

theorem aestronglyMeasurable : AEStronglyMeasurable f μ :=
  hf.stronglyMeasurable.aestronglyMeasurable

theorem memℒp_top : Memℒp f ⊤ μ :=
  ⟨hf.aestronglyMeasurable, hf.isBounded.eLpNorm_top_lt_top⟩

theorem ae_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ ENNReal.toReal (eLpNorm f ⊤ μ) :=
  ae_le_of_eLpNorm_top_lt_top hf.memℒp_top.2

/-- Bounded compactly supported functions are in all `Lᵖ` spaces. -/
theorem memℒp [IsFiniteMeasureOnCompacts μ] (p : ENNReal) : Memℒp f p μ :=
  hf.hasCompactSupport.memℒp_of_bound hf.aestronglyMeasurable _ hf.ae_le

/-- Bounded compactly supported functions are integrable. -/
theorem integrable [IsFiniteMeasureOnCompacts μ] : Integrable f μ :=
  memℒp_one_iff_integrable.mp <| memℒp hf 1

theorem mul_bdd_right (hg : IsBounded (range g)) (h2g : StronglyMeasurable g) :
    BoundedCompactSupport (f * g) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg with ⟨D, hD⟩
    apply isBounded_range_iff_forall_norm_le.2 ⟨C * D, fun x ↦ ?_⟩
    simp only [Pi.mul_apply, norm_mul]
    gcongr
    · apply (norm_nonneg _).trans (hC x)
    · exact hC x
    · exact hD x
  stronglyMeasurable := hf.stronglyMeasurable.mul h2g
  hasCompactSupport := hf.hasCompactSupport.mul_right

theorem mul_bdd_left (hg : IsBounded (range g)) (h2g : StronglyMeasurable g) :
    BoundedCompactSupport (g * f) := by
  rw [mul_comm]; exact mul_bdd_right hf hg h2g

-- doesn't use compact support but is convenient to have here
theorem integrable_mul (hg : Integrable g μ) : Integrable (f * g) μ :=
  Integrable.bdd_mul' hg hf.aestronglyMeasurable hf.ae_le

theorem conj : BoundedCompactSupport (star f) where
  isBounded := by simpa [star, isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := RCLike.continuous_conj.comp_stronglyMeasurable hf.stronglyMeasurable
  hasCompactSupport := by -- mathlib should have a lemma `HasCompactSupport.conj`?
    simp only [star, RCLike.star_def]
    apply (hasCompactSupport_comp_left (by simp)).2 hf.hasCompactSupport

theorem norm : BoundedCompactSupport (‖f ·‖) where
  isBounded := by simpa [isBounded_range_iff_forall_norm_le] using hf.isBounded
  stronglyMeasurable := hf.stronglyMeasurable.norm
  hasCompactSupport := hf.hasCompactSupport.norm

theorem const_mul (c : 𝕜) : BoundedCompactSupport (fun x ↦ c * (f x)) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    apply isBounded_range_iff_forall_norm_le.2 ⟨‖c‖ * C, fun x ↦ ?_⟩
    simp only [norm_mul]
    gcongr
    exact hC x
  stronglyMeasurable := hf.stronglyMeasurable.const_mul _
  hasCompactSupport := by
    suffices support (fun x ↦ c * (f x)) ⊆ support f from
      hf.hasCompactSupport.mono this
    exact support_mul_subset_right ..

theorem mul_const (c : 𝕜) : BoundedCompactSupport (fun x ↦ (f x) * c) := by
  simp_rw [mul_comm]; exact hf.const_mul _

end Includehf

section Includehfhg

include hf hg

theorem mul : BoundedCompactSupport (f * g) := mul_bdd_right hf hg.isBounded hg.stronglyMeasurable

protected theorem add : BoundedCompactSupport (f + g) where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hf.isBounded with ⟨C, hC⟩
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨D, hD⟩
    apply isBounded_range_iff_forall_norm_le.2 ⟨C + D, fun x ↦ ?_⟩
    apply (norm_add_le _ _).trans
    gcongr
    exacts [hC x, hD x]
  stronglyMeasurable := hf.stronglyMeasurable.add hg.stronglyMeasurable
  hasCompactSupport := hf.hasCompactSupport.add hg.hasCompactSupport

protected theorem sub : BoundedCompactSupport (f - g) := by
  rw [sub_eq_add_neg, neg_eq_neg_one_mul]
  exact hf.add (hg.const_mul (-1))

end Includehfhg

/-- If `‖f‖` is bounded by `g` and `g` is bounded compactly supported, then so is `f`. -/
theorem mono {g : X → ℝ} (hg : BoundedCompactSupport g) (hf : StronglyMeasurable f)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : BoundedCompactSupport f where
  isBounded := by
    rcases isBounded_range_iff_forall_norm_le.1 hg.isBounded with ⟨C, hC⟩
    refine isBounded_range_iff_forall_norm_le.2 ⟨C, fun x ↦ ?_⟩
    exact (hfg x).trans ((le_abs_self _).trans (hC x))
  hasCompactSupport := by
    refine hg.hasCompactSupport.mono ?_
    by_contra h
    simp only [support_subset_iff, ne_eq, mem_support, not_forall, Classical.not_imp,
      Decidable.not_not] at h
    obtain ⟨x, hfx, hgx⟩ := h
    specialize hfg x
    rw [hgx] at hfg
    exact hfx <| norm_le_zero_iff.mp hfg
  stronglyMeasurable := hf

/- Start of proof attempt -/
lemma round1_h13 (X : Type*) [MeasurableSpace X] [TopologicalSpace X] {g : X → ℝ}
  (hg : HasCompactSupport g) (M : ℝ) :
  HasCompactSupport (fun x : X => M * g x) := by
  by_cases hM : M = 0
  · -- Case 1: M = 0
    have h1 : (fun x : X => M * g x) = (fun x : X => 0) := by
      funext x
      simp [hM]
    rw [h1]
    exact HasCompactSupport.zero
  · -- Case 2: M ≠ 0
    have h2 : support (fun x : X => M * g x) ⊆ support g := by
      intro x hx
      simp only [mem_support] at *
      by_contra h
      have h' : g x = 0 := by simpa using h
      have h4 : M * g x = 0 := by rw [h']; ring
      contradiction
    have h3 : closure (support (fun x : X => M * g x)) ⊆ closure (support g) := by
      apply closure_mono h2
    have h4 : tsupport (fun x : X => M * g x) ⊆ tsupport g := h3
    have h5 : IsCompact (tsupport g) := hg
    have h6 : IsClosed (tsupport (fun x : X => M * g x)) := isClosed_tsupport (fun x : X => M * g x)
    have h7 : IsCompact (tsupport (fun x : X => M * g x)) := by
      apply IsCompact.of_isClosed_subset h5 h6 h4
    exact h7

lemma round1_h1 (X : Type*) [MeasurableSpace X] [TopologicalSpace X] {𝕜 : Type*} [RCLike 𝕜]
  {f : X → 𝕜} {g : X → ℝ} {M : ℝ} (hg : BoundedCompactSupport g)
  (hf : StronglyMeasurable f) (hfg : ∀ x, ‖f x‖ ≤ M * g x) :
  BoundedCompactSupport (fun x : X => M * g x) := by
  have h11 : IsBounded (range (fun x : X => M * g x)) := by
    have h111 : ∃ (C : ℝ), ∀ (x : X), ‖g x‖ ≤ C := by
      rcases isBounded_range_iff_forall_norm_le.mp hg.isBounded with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro x
      exact hC x
    rcases h111 with ⟨C, hC⟩
    have h112 : ∃ (D : ℝ), ∀ (x : X), ‖(M * g x)‖ ≤ D := by
      use |M| * C
      intro x
      have h1111 : ‖(M * g x)‖ = |M| * ‖g x‖ := by
        simp [norm_mul]
        <;> ring
      have h1112 : ‖g x‖ ≤ C := hC x
      have h1113 : |M| ≥ 0 := abs_nonneg M
      have h1114 : ‖(M * g x)‖ ≤ |M| * C := by
        rw [h1111]
        have h1115 : |M| * ‖g x‖ ≤ |M| * C := by
          exact mul_le_mul_of_nonneg_left h1112 h1113
        linarith
      linarith
    rcases h112 with ⟨D, hD⟩
    have h113 : IsBounded (range (fun x : X => M * g x)) := by
      apply isBounded_range_iff_forall_norm_le.mpr
      refine ⟨D, ?_⟩
      intro x
      exact hD x
    exact h113
  have h12 : StronglyMeasurable (fun x : X => M * g x) := by
    exact stronglyMeasurable_const.mul hg.stronglyMeasurable
  have h13 : HasCompactSupport (fun x : X => M * g x) := by
    exact round1_h13 X hg.hasCompactSupport M
  exact ⟨h11, h12, h13⟩

theorem of_norm_le_const_mul {g : X → ℝ} {M : ℝ} (hg : BoundedCompactSupport g)
    (hf : StronglyMeasurable f)
    (hfg : ∀ x, ‖f x‖ ≤ M * g x) : BoundedCompactSupport f  := by

  have h1 : BoundedCompactSupport (fun x : X => M * g x) := by
    exact round1_h1 X hg hf hfg
  have h3 : ∀ x, ‖f x‖ ≤ (fun x : X => M * g x) x := by
    intro x
    simpa using hfg x
  exact BoundedCompactSupport.mono h1 hf h3
