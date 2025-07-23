-- In carleson/Carleson/ToMathlib/Analysis/Convex/SpecificFunctions/Basic.lean

import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set Bornology Function ENNReal Metric

-- TODO: Not needed, but good for completeness
-- theorem strictConvexOn_rpow_left (b : ℝ) (hb : 0 < b) :
--     StrictConvexOn ℝ Set.univ (fun (x : ℝ) => b ^ x) := by
--   sorry

/- Start of proof attempt -/
lemma round1_h1 (b : ℝ)
  (hb : 0 < b):
  ∀ (x : ℝ), b ^ x = Real.exp (x * Real.log b) := by
  intro x
  have h11 : b ^ x = Real.exp (Real.log b * x) := by
    rw [Real.rpow_def_of_pos hb]
  have h12 : Real.log b * x = x * Real.log b := by ring
  rw [h11, h12]

lemma round1_h2 (b : ℝ)
  (hb : 0 < b)
  (h1 : ∀ (x : ℝ), b ^ x = Real.exp (x * Real.log b)):
  ∀ (x y u v : ℝ), u ≥ 0 → v ≥ 0 → u + v = 1 → b ^ (u * x + v * y) ≤ u * (b ^ x) + v * (b ^ y) := by
  intro x y u v hu hv hsum
  have h3 : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
  have h31 : ∀ (s t : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 → Real.exp (u * s + v * t) ≤ u * Real.exp s + v * Real.exp t := by
    intro s t hu' hv' hsum'
    have h311 : (s : ℝ) ∈ (Set.univ : Set ℝ) := by simp
    have h312 : (t : ℝ) ∈ (Set.univ : Set ℝ) := by simp
    have h : Real.exp (u • s + v • t) ≤ u • Real.exp s + v • Real.exp t := by
      apply h3.2 h311 h312
      all_goals linarith
    have h313 : u • s + v • t = u * s + v * t := by simp [smul_eq_mul]
    have h314 : u • Real.exp s + v • Real.exp t = u * Real.exp s + v * Real.exp t := by simp [smul_eq_mul]
    rw [h313, h314] at h
    linarith
  have h4 := h31 (x * Real.log b) (y * Real.log b) hu hv hsum
  have h5 : u * (x * Real.log b) + v * (y * Real.log b) = (u * x + v * y) * Real.log b := by ring
  have h6 : Real.exp (u * (x * Real.log b) + v * (y * Real.log b)) ≤ u * Real.exp (x * Real.log b) + v * Real.exp (y * Real.log b) := by simpa using h4
  have h6' : Real.exp ((u * x + v * y) * Real.log b) ≤ u * Real.exp (x * Real.log b) + v * Real.exp (y * Real.log b) := by
    rw [h5] at h6
    linarith
  have h7 : b ^ (u * x + v * y) = Real.exp ((u * x + v * y) * Real.log b) := by
    have h71 := h1 (u * x + v * y)
    linarith
  have h8 : b ^ x = Real.exp (x * Real.log b) := by
    have h81 := h1 x
    linarith
  have h9 : b ^ y = Real.exp (y * Real.log b) := by
    have h91 := h1 y
    linarith
  have h10 : b ^ (u * x + v * y) ≤ u * (b ^ x) + v * (b ^ y) := by
    rw [h7, h8, h9]
    linarith
  linarith

theorem ConvexOn_rpow_left (b : ℝ) (hb : 0 < b) :
    ConvexOn ℝ Set.univ (fun (x : ℝ) => b ^ x)  := by

  have h1 : ∀ (x : ℝ), b ^ x = Real.exp (x * Real.log b) := by
    exact round1_h1 b hb
  have h2 : ∀ (x y u v : ℝ), u ≥ 0 → v ≥ 0 → u + v = 1 → b ^ (u * x + v * y) ≤ u * (b ^ x) + v * (b ^ y) := by
    exact round1_h2 b hb h1
  constructor
  · exact convex_univ
  · intro x _ y _ a v ha hv hsum
    have h11 := h2 x y a v ha hv hsum
    simpa using h11
