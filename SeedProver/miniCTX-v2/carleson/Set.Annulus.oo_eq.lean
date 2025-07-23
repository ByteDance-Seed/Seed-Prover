-- In carleson/Carleson/ToMathlib/Annulus.lean

/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Annulus

In this file we define an annulus in a pseudometric space `X` to be a set consisting of all `y`
such that `dist x y` lies in an interval between `r` and `R`. An annulus is defined for each type
of interval (`Ioo`, `Ioc`, etc.) with a parallel naming scheme, except that we do not define annuli
for `Iio` and `Ico`, as they would be balls.

We also define `EAnnulus` similarly using `edist` instead of `dist`.

## Tags

annulus, eannulus
-/

open Set Metric ENNReal

variable {X : Type*} [PseudoMetricSpace X]

namespace Set

namespace Annulus

def oo (x : X) (r R : ℝ) := {y | dist x y ∈ Ioo r R}
def oc (x : X) (r R : ℝ) := {y | dist x y ∈ Ioc r R}
def co (x : X) (r R : ℝ) := {y | dist x y ∈ Ico r R}
def cc (x : X) (r R : ℝ) := {y | dist x y ∈ Icc r R}
def oi (x : X) (r : ℝ) := {y | dist x y ∈ Ioi r}
def ci (x : X) (r : ℝ) := {y | dist x y ∈ Ici r}

/- Start of proof attempt -/
lemma round1_oo_eq {X : Type*} [PseudoMetricSpace X] {x : X} {r R : ℝ} :
  ({y : X | dist x y ∈ Set.Ioo r R} : Set X) = Metric.ball x R ∩ (Metric.closedBall x r)ᶜ := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall, Set.mem_compl_iff]
  constructor
  · -- Assume r < dist x y ∧ dist x y < R
    rintro ⟨h1, h2⟩
    constructor
    · -- Prove dist y x < R
      have h21 : dist y x = dist x y := by rw [dist_comm]
      linarith
    · -- Prove ¬(dist y x ≤ r)
      intro h3
      have h4 : dist x y = dist y x := by rw [dist_comm]
      linarith
  · -- Assume dist y x < R ∧ ¬(dist y x ≤ r)
    rintro ⟨h2, h3⟩
    constructor
    · -- Prove r < dist x y
      by_contra h4
      have h41 : dist x y ≤ r := by linarith
      have h5 : dist y x ≤ r := by
        have h51 : dist y x = dist x y := by rw [dist_comm]
        linarith
      contradiction
    · -- Prove dist x y < R
      have h21 : dist x y = dist y x := by rw [dist_comm]
      linarith

theorem oo_eq {x : X} {r R : ℝ} : oo x r R = ball x R ∩ (closedBall x r)ᶜ  := by

  exact round1_oo_eq
