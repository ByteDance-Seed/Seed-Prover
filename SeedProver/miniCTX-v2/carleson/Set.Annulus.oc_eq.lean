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

lemma oo_eq {x : X} {r R : ℝ} : oo x r R = ball x R ∩ (closedBall x r)ᶜ := by
  ext; simp [oo, dist_comm, and_comm]

/- Start of proof attempt -/
lemma round1_oc_eq {X : Type*} [PseudoMetricSpace X] {x : X} {r R : ℝ} :
  Set.Annulus.oc x r R = closedBall x R ∩ (closedBall x r)ᶜ := by
  have h_main : ∀ (y : X), y ∈ Set.Annulus.oc x r R ↔ y ∈ closedBall x R ∩ (closedBall x r)ᶜ := by
    intro y
    have h1 : dist x y = dist y x := by rw [dist_comm]
    constructor
    · -- Assume `y ∈ Set.Annulus.oc x r R`
      intro h
      have h2 : r < dist x y ∧ dist x y ≤ R := by
        simpa [Set.Annulus.oc, mem_setOf_eq, mem_Ioc] using h
      have h21 : r < dist x y := h2.1
      have h22 : dist x y ≤ R := h2.2
      have h3 : r < dist y x := by linarith [h1]
      have h4 : dist y x ≤ R := by linarith [h1]
      constructor
      · -- Prove `y ∈ closedBall x R`
        simpa [mem_closedBall] using h4
      · -- Prove `y ∉ closedBall x r`
        intro h5
        have h51 : dist y x ≤ r := by simpa [mem_closedBall] using h5
        linarith
    · -- Assume `y ∈ closedBall x R ∩ (closedBall x r)ᶜ`
      intro h
      have h2 : y ∈ closedBall x R ∧ y ∉ closedBall x r := h
      have h21 : y ∈ closedBall x R := h2.1
      have h22 : y ∉ closedBall x r := h2.2
      have h3 : dist y x ≤ R := by simpa [mem_closedBall] using h21
      have h4 : ¬(dist y x ≤ r) := by
        intro h41
        have h42 : y ∈ closedBall x r := by simpa [mem_closedBall] using h41
        exact h22 h42
      have h43 : r < dist y x := by linarith
      have h5 : r < dist x y := by linarith [h1]
      have h6 : dist x y ≤ R := by linarith [h1]
      simpa [Set.Annulus.oc, mem_setOf_eq, mem_Ioc] using ⟨h5, h6⟩
  ext y
  exact h_main y

theorem oc_eq {x : X} {r R : ℝ} : oc x r R = closedBall x R ∩ (closedBall x r)ᶜ  := by

  exact round1_oc_eq
