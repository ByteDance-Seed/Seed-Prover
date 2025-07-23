-- In FLT/FLT/HaarMeasure/MeasurableSpacePadics.lean

/-
Copyright (c) 2024 Yaël Dillies, David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Measurability and measures on the p-adics

This file endows `ℤ_[p]` and `ℚ_[p]` with their Borel sigma-algebra and their Haar measure that
makes `ℤ_[p]` (or the copy of `ℤ_[p]` inside `ℚ_[p]`) have norm `1`.
-/

open MeasureTheory Measure TopologicalSpace Topology

variable {p : ℕ} [Fact p.Prime]

namespace Padic

instance instMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
instance instBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

-- Should we more generally make a map from `CompactOpens` to `PositiveCompacts`?
private def unitBall_positiveCompact : PositiveCompacts ℚ_[p] where
  carrier := {y | ‖y‖ ≤ 1}
  isCompact' := by simpa only [Metric.closedBall, dist_zero_right] using
    isCompact_closedBall (0 : ℚ_[p]) 1
  interior_nonempty' := by
    rw [IsOpen.interior_eq]
    · exact ⟨0, by simp⟩
    · simpa only [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

noncomputable instance instMeasureSpace : MeasureSpace ℚ_[p] :=
  ⟨addHaarMeasure unitBall_positiveCompact⟩

instance instIsAddHaarMeasure : IsAddHaarMeasure (volume : Measure ℚ_[p]) :=
  isAddHaarMeasure_addHaarMeasure _

/- Start of proof attempt -/
lemma round1_h1 : volume (unitBall_positiveCompact : PositiveCompacts ℚ_[p]).carrier = 1 := by
  simp [instMeasureSpace, addHaarMeasure_self]

lemma round1_h2 : (unitBall_positiveCompact : PositiveCompacts ℚ_[p]).carrier = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
  rfl

theorem volume_closedBall_one : volume {x : ℚ_[p] | ‖x‖ ≤ 1} = 1  := by

  have h1 : volume (unitBall_positiveCompact : PositiveCompacts ℚ_[p]).carrier = 1 := by
    exact round1_h1
  have h2 : (unitBall_positiveCompact : PositiveCompacts ℚ_[p]).carrier = {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    exact round1_h2
  rw [h2] at h1
  exact h1
