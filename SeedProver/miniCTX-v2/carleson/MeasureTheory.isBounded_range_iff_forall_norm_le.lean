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

/- Start of proof attempt -/
lemma round1_isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C := by
  constructor
  · -- Forward direction: IsBounded (range f) → ∃ C, ∀ x, ‖f x‖ ≤ C
    intro h
    have h1 : ∃ r, range f ⊆ Metric.closedBall (0 : α) r := by
      exact Bornology.IsBounded.subset_closedBall h (0 : α)
    rcases h1 with ⟨C, hC⟩
    refine' ⟨C, _⟩
    intro x
    have h11 : f x ∈ range f := ⟨x, rfl⟩
    have h12 : f x ∈ Metric.closedBall (0 : α) C := hC h11
    have h13 : dist (f x) 0 ≤ C := by simpa using h12
    simpa [dist_zero_right] using h13
  · -- Backward direction: (∃ C, ∀ x, ‖f x‖ ≤ C) → IsBounded (range f)
    rintro ⟨C, hC⟩
    have h1 : range f ⊆ Metric.closedBall (0 : α) C := by
      intro y hy
      rcases hy with ⟨x, rfl⟩
      have h2 : ‖f x‖ ≤ C := hC x
      simpa using h2
    exact Bornology.IsBounded.subset (Metric.isBounded_closedBall) h1

theorem isBounded_range_iff_forall_norm_le {α β} [SeminormedAddCommGroup α] {f : β → α} :
    IsBounded (range f) ↔ ∃ C, ∀ x, ‖f x‖ ≤ C  := by

  exact round1_isBounded_range_iff_forall_norm_le
