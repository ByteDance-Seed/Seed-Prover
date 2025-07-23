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

lemma oc_eq {x : X} {r R : ℝ} : oc x r R = closedBall x R ∩ (closedBall x r)ᶜ := by
  ext; simp [oc, dist_comm, and_comm]

lemma co_eq {x : X} {r R : ℝ} : co x r R = ball x R ∩ (ball x r)ᶜ := by
  ext; simp [co, dist_comm, and_comm]

lemma cc_eq {x : X} {r R : ℝ} : cc x r R = closedBall x R ∩ (ball x r)ᶜ := by
  ext; simp [cc, dist_comm, and_comm]

lemma oi_eq {x : X} {r : ℝ} : oi x r = (closedBall x r)ᶜ := by
  ext; simp [oi, dist_comm]

lemma ci_eq {x : X} {r : ℝ} : ci x r = (ball x r)ᶜ := by
  ext; simp [ci, dist_comm]

@[simp]
lemma oo_eq_empty {x : X} {r R : ℝ} (h : r ≥ R) : oo x r R = ∅ := by
  simp [oo, Ioo_eq_empty_of_le h]

/- Start of proof attempt -/
lemma round1_oc_eq_empty {x : X} {r R : ℝ} (h : r ≥ R) : oc x r R = ∅ := by
  have h1 : ∀ (y : X), y ∉ oc x r R := by
    intro y hy
    have h2 : dist x y ∈ Ioc r R := hy
    have h21 : r < dist x y := h2.1
    have h22 : dist x y ≤ R := h2.2
    linarith
  exact Set.eq_empty_iff_forall_not_mem.mpr h1

theorem oc_eq_empty {x : X} {r R : ℝ} (h : r ≥ R) : oc x r R = ∅  := by

  exact round1_oc_eq_empty h
