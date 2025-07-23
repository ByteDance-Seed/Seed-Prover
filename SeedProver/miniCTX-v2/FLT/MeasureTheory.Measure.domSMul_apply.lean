-- In FLT/FLT/HaarMeasure/DomMulActMeasure.lean

/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory.Measure

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [MeasurableSpace A]
  -- We only need `MeasurableConstSMul G A` but we don't have this class. So we erroneously must
  -- assume `MeasurableSpace G` + `MeasurableSMul G A`
  [MeasurableSpace G] [MeasurableSMul G A]
variable {μ ν : Measure A} {g : G}

/- Start of proof attempt -/
lemma round1_domSMul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) :
    (g • μ) s = μ ((DomMulAct.mk.symm g) • s) := by
  exact?

theorem domSMul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) :
    (g • μ) s = μ ((DomMulAct.mk.symm g) • s)  := by

  exact round1_domSMul_apply μ g s
