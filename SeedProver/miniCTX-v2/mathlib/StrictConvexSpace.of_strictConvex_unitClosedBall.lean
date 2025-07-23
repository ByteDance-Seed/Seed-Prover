-- In mathlib/Mathlib/Analysis/Convex/StrictConvexSpace.lean

/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yury Kudryashov
-/
import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Normed.Module.Ray

/-!
# Strictly convex spaces

This file defines strictly convex spaces. A normed space is strictly convex if all closed balls are
strictly convex. This does **not** mean that the norm is strictly convex (in fact, it never is).

## Main definitions

`StrictConvexSpace`: a typeclass saying that a given normed space over a normed linear ordered
field (e.g., `ℝ` or `ℚ`) is strictly convex. The definition requires strict convexity of a closed
ball of positive radius with center at the origin; strict convexity of any other closed ball follows
from this assumption.

## Main results

In a strictly convex space, we prove

- `strictConvex_closedBall`: a closed ball is strictly convex.
- `combo_mem_ball_of_ne`, `openSegment_subset_ball_of_ne`, `norm_combo_lt_of_ne`:
  a nontrivial convex combination of two points in a closed ball belong to the corresponding open
  ball;
- `norm_add_lt_of_not_sameRay`, `sameRay_iff_norm_add`, `dist_add_dist_eq_iff`:
  the triangle inequality `dist x y + dist y z ≤ dist x z` is a strict inequality unless `y` belongs
  to the segment `[x -[ℝ] z]`.
- `Isometry.affineIsometryOfStrictConvexSpace`: an isometry of `NormedAddTorsor`s for real
  normed spaces, strictly convex in the case of the codomain, is an affine isometry.

We also provide several lemmas that can be used as alternative constructors for `StrictConvex ℝ E`:

- `StrictConvexSpace.of_strictConvex_unitClosedBall`: if `closed_ball (0 : E) 1` is strictly
  convex, then `E` is a strictly convex space;

- `StrictConvexSpace.of_norm_add`: if `‖x + y‖ = ‖x‖ + ‖y‖` implies `SameRay ℝ x y` for all
  nonzero `x y : E`, then `E` is a strictly convex space.

## Implementation notes

While the definition is formulated for any normed linear ordered field, most of the lemmas are
formulated only for the case `𝕜 = ℝ`.

## Tags

convex, strictly convex
-/

open Convex Pointwise Set Metric

/-- A *strictly convex space* is a normed space where the closed balls are strictly convex. We only
require balls of positive radius with center at the origin to be strictly convex in the definition,
then prove that any closed ball is strictly convex in `strictConvex_closedBall` below.

See also `StrictConvexSpace.of_strictConvex_unitClosedBall`. -/
class StrictConvexSpace (𝕜 E : Type*) [NormedLinearOrderedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] : Prop where
  strictConvex_closedBall : ∀ r : ℝ, 0 < r → StrictConvex 𝕜 (closedBall (0 : E) r)

variable (𝕜 : Type*) {E : Type*} [NormedLinearOrderedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]

/-- A closed ball in a strictly convex space is strictly convex. -/
theorem strictConvex_closedBall [StrictConvexSpace 𝕜 E] (x : E) (r : ℝ) :
    StrictConvex 𝕜 (closedBall x r) := by
  rcases le_or_lt r 0 with hr | hr
  · exact (subsingleton_closedBall x hr).strictConvex
  rw [← vadd_closedBall_zero]
  exact (StrictConvexSpace.strictConvex_closedBall r hr).vadd _

variable [NormedSpace ℝ E]

/- Start of proof attempt -/
lemma round1_h2 (𝕜 E : Type*) [NormedLinearOrderedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [LinearMap.CompatibleSMul E E 𝕜 ℝ]
  (h : StrictConvex 𝕜 (closedBall (0 : E) 1)) (r : ℝ)
  (hr : 0 < r)
  (hr' : 0 ≤ r):
  StrictConvex 𝕜 (r • (closedBall (0 : E) 1)) := by
  exact StrictConvex.smul h r

lemma round1_h3 (𝕜 E : Type*) [NormedLinearOrderedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  (r : ℝ)
  (hr' : 0 ≤ r):
  r • (closedBall (0 : E) 1) = closedBall (0 : E) r := by
  exact smul_unitClosedBall_of_nonneg hr'

/-- A real normed vector space is strictly convex provided that the unit ball is strictly convex. -/
theorem StrictConvexSpace.of_strictConvex_unitClosedBall [LinearMap.CompatibleSMul E E 𝕜 ℝ]
    (h : StrictConvex 𝕜 (closedBall (0 : E) 1)) : StrictConvexSpace 𝕜 E  := by

  have h1 : ∀ (r : ℝ), 0 < r → StrictConvex 𝕜 (closedBall (0 : E) r) := by
    intro r hr
    have hr' : 0 ≤ r := by linarith
    have h2 : StrictConvex 𝕜 (r • (closedBall (0 : E) 1)) := by
      exact round1_h2 𝕜 E h r hr hr'
    have h3 : r • (closedBall (0 : E) 1) = closedBall (0 : E) r := by
      exact round1_h3 𝕜 E r hr'
    rw [h3] at h2
    exact h2
  exact ⟨h1⟩
