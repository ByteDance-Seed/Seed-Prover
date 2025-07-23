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

lemma volume_closedBall_one : volume {x : ℚ_[p] | ‖x‖ ≤ 1} = 1 := addHaarMeasure_self

end Padic

namespace PadicInt

instance instMeasurableSpace : MeasurableSpace ℤ_[p] := Subtype.instMeasurableSpace
instance instBorelSpace : BorelSpace ℤ_[p] := Subtype.borelSpace _

/- Start of proof attempt -/
lemma round1_h1 : Measurable (fun (x : ℤ_[p]) => (x : ℚ_[p])) := by
  apply Continuous.measurable
  exact continuous_subtype_val

lemma round1_h2 : Function.Injective (fun (x : ℤ_[p]) => (x : ℚ_[p])) := by
  exact Subtype.coe_injective

lemma round1_h3 : ∀ (s : Set ℤ_[p]), MeasurableSet s → MeasurableSet (((fun (x : ℤ_[p]) => (x : ℚ_[p])) '' s)) := by
  intro s hs
  rcases hs with ⟨u, hu, rfl⟩
  have h5 : IsClosed ({x : ℚ_[p] | ‖x‖ ≤ 1} : Set ℚ_[p]) := by
    have h51 : Continuous (fun (x : ℚ_[p]) => ‖x‖) := by continuity
    have h52 : IsClosed (Set.Iic (1 : ℝ)) := isClosed_Iic
    have h53 : {x : ℚ_[p] | ‖x‖ ≤ 1} = (fun (x : ℚ_[p]) => ‖x‖) ⁻¹' (Set.Iic (1 : ℝ)) := by
      ext x
      simp [Set.mem_setOf_eq, Set.mem_Iic]
      <;> aesop
    rw [h53]
    exact IsClosed.preimage h51 h52
  have h54 : MeasurableSet ({x : ℚ_[p] | ‖x‖ ≤ 1} : Set ℚ_[p]) := by
    exact IsClosed.measurableSet h5
  have h55 : MeasurableSet (u ∩ {x : ℚ_[p] | ‖x‖ ≤ 1}) := by
    exact MeasurableSet.inter hu h54
  have h6 : (fun (x : ℤ_[p]) => (x : ℚ_[p])) '' ((Subtype.val : ℤ_[p] → ℚ_[p]) ⁻¹' u) = u ∩ {x : ℚ_[p] | ‖x‖ ≤ 1} := by
    apply Set.ext
    intro z
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx1, rfl⟩
      have h61 : (x : ℚ_[p]) ∈ u := by simpa using hx1
      have h62 : ‖(x : ℚ_[p])‖ ≤ 1 := x.2
      exact ⟨h61, h62⟩
    · rintro ⟨hz1, hz2⟩
      have h7 : ∃ (y : ℤ_[p]), (y : ℚ_[p]) = z := by
        refine ⟨⟨z, hz2⟩, ?_⟩
        simp
      rcases h7 with ⟨y, hy⟩
      have hy1 : (y : ℚ_[p]) ∈ u := by
        rw [hy]
        exact hz1
      have hy2 : y ∈ (Subtype.val : ℤ_[p] → ℚ_[p]) ⁻¹' u := by simpa using hy1
      refine ⟨y, hy2, ?_⟩
      simp [hy]
      <;> aesop
  rw [h6]
  exact h55

theorem isMeasurableEmbedding_coe : MeasurableEmbedding ((↑) : ℤ_[p] → ℚ_[p])  := by

  have h1 : Measurable (fun (x : ℤ_[p]) => (x : ℚ_[p])) := round1_h1
  have h2 : Function.Injective (fun (x : ℤ_[p]) => (x : ℚ_[p])) := round1_h2
  have h3 : ∀ (s : Set ℤ_[p]), MeasurableSet s → MeasurableSet (((fun (x : ℤ_[p]) => (x : ℚ_[p])) '' s)) := round1_h3
  exact MeasurableEmbedding.mk h2 h1 h3
