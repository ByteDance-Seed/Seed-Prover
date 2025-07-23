-- In carleson/Carleson/Classical/HilbertStrongType.lean

import Carleson.Classical.HilbertKernel
import Carleson.Classical.DirichletKernel
import Carleson.Classical.SpectralProjectionBound

/- This file contains the proof that the Hilbert kernel is a bounded operator. -/

noncomputable section

open scoped Real ENNReal
open Complex ComplexConjugate MeasureTheory Bornology Set
-- open MeasureTheory Function Metric Bornology Real ENNReal MeasureTheory.ENNReal MeasureTheory

section
@[reducible]
def doublingMeasure_real_two : DoublingMeasure ℝ 2 :=
  InnerProductSpace.DoublingMeasure.mono (by simp)

instance doublingMeasure_real_16 : DoublingMeasure ℝ (2 ^ 4 : ℕ) :=
  doublingMeasure_real_two.mono (by norm_num)
end

/-- The modulation operator `M_n g`, defined in (11.3.1) -/
def modulationOperator (n : ℤ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  g x * Complex.exp (.I * n * x)

/-- The approximate Hilbert transform `L_N g`, defined in (11.3.2).
defined slightly differently. -/
def approxHilbertTransform (n : ℕ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k ∈ .Ico n (2 * n),
    modulationOperator (-k) (partialFourierSum k (modulationOperator k g)) x

/-- The kernel `k_r(x)` defined in (11.3.11).
When used, we may assume that `r ∈ Ioo 0 1`.
Todo: find better name? -/
def niceKernel (r : ℝ) (x : ℝ) : ℝ :=
  if Complex.exp (.I * x) = 1 then r⁻¹ else
    min r⁻¹ (1 + r / normSq (1 - Complex.exp (.I * x)))

-- todo: write lemmas for `niceKernel` (periodicity, evenness)

/- Start of proof attempt -/
lemma round1_h5 :
  ∀ (z : ℂ), Complex.exp z = 1 → ∀ (n : ℤ), Complex.exp ((n : ℂ) * z) = 1 := by
  intro z hz
  have h51 : ∀ (k : ℕ), Complex.exp ((k : ℂ) * z) = 1 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      calc
        Complex.exp (((k + 1 : ℕ) : ℂ) * z) = Complex.exp (((k : ℂ) + 1) * z) := by simp
        _ = Complex.exp ((k : ℂ) * z + z) := by
          ring_nf
        _ = Complex.exp ((k : ℂ) * z) * Complex.exp z := by rw [Complex.exp_add]
        _ = 1 * 1 := by rw [ih, hz]
        _ = 1 := by ring
  intro n
  by_cases h62 : 0 ≤ n
  · -- Case 1: 0 ≤ n
    have h621 : ∃ (k : ℕ), (n : ℤ) = (k : ℤ) := by
      refine ⟨n.toNat,?_⟩
      simp [Int.toNat_of_nonneg h62]
    rcases h621 with ⟨k, hk⟩
    have h622 : (n : ℂ) = (k : ℂ) := by
      norm_cast <;> simp [hk]
    rw [h622]
    exact h51 k
  · -- Case 2: n < 0
    have h623 : n < 0 := by linarith
    have h624 : 0 ≤ -n := by linarith
    have h625 : ∃ (k : ℕ), (-n : ℤ) = (k : ℤ) := by
      refine ⟨(-n).toNat,?_⟩
      simp [Int.toNat_of_nonneg h624]
    rcases h625 with ⟨k, hk⟩
    have h626 : (n : ℂ) * z = - ((k : ℂ) * z) := by
      have h6261 : (n : ℂ) = - (k : ℂ) := by
        have h62611 : (-n : ℤ) = (k : ℤ) := hk
        have h62612 : (n : ℤ) = - (k : ℤ) := by linarith
        norm_cast at h62612 ⊢ <;> simp [h62612]
        <;> ring
      calc
        (n : ℂ) * z = (- (k : ℂ)) * z := by rw [h6261]
        _ = - ((k : ℂ) * z) := by ring
    have h627 : Complex.exp ((n : ℂ) * z) = Complex.exp (- ((k : ℂ) * z)) := by rw [h626]
    have h628 : Complex.exp (- ((k : ℂ) * z)) = 1 / Complex.exp ((k : ℂ) * z) := by
      rw [Complex.exp_neg]
      <;> field_simp
    have h629 : Complex.exp ((k : ℂ) * z) = 1 := h51 k
    rw [h627, h628, h629]
    <;> norm_num

lemma round1_h631 (n : ℤ)
  (hn : n ≠ 0)
  (h5 : ∀ (z : ℂ), Complex.exp z = 1 → ∀ (n : ℤ), Complex.exp ((n : ℂ) * z) = 1):
  Complex.exp (Complex.I * (n : ℂ) * (2 * Real.pi)) = 1 := by
  have h4 : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
    have h41 : Complex.exp (2 * Real.pi * Complex.I) = Complex.exp (Real.pi * Complex.I + Real.pi * Complex.I) := by ring_nf
    have h42 : Complex.exp (Real.pi * Complex.I + Real.pi * Complex.I) = Complex.exp (Real.pi * Complex.I) * Complex.exp (Real.pi * Complex.I) := by rw [Complex.exp_add]
    have h43 : Complex.exp (Real.pi * Complex.I) = -1 := Complex.exp_pi_mul_I
    rw [h41, h42, h43]
    <;> ring
  have h63 : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    exact h5 (2 * Real.pi * Complex.I) h4 n
  have h632 : (n : ℂ) * (2 * Real.pi * Complex.I) = Complex.I * (n : ℂ) * (2 * Real.pi) := by
    ring
  have h633 : Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = Complex.exp (Complex.I * (n : ℂ) * (2 * Real.pi)) := by rw [h632]
  rw [h633] at h63
  exact h63

/-- Lemma 11.1.8 -/
theorem mean_zero_oscillation {n : ℤ} (hn : n ≠ 0) :
    ∫ x in (0)..2 * π, Complex.exp (.I * n * x) = 0  := by

  have h1 : (n : ℂ) ≠ 0 := by
    intro h
    have h11 : n = 0 := by exact_mod_cast h
    contradiction
  have h2 : Complex.I ≠ 0 := Complex.I_ne_zero
  have h3 : Complex.I * (n : ℂ) ≠ 0 := mul_ne_zero h2 h1
  have h5 : ∀ (z : ℂ), Complex.exp z = 1 → ∀ (n : ℤ), Complex.exp ((n : ℂ) * z) = 1 := by
    exact round1_h5
  have h631 : Complex.exp (Complex.I * (n : ℂ) * (2 * Real.pi)) = 1 := by
    exact round1_h631 n hn h5
  have h64 : Complex.exp (Complex.I * (n : ℂ) * 0) = 1 := by simp
  have h9 : ∫ (x : ℝ) in (0)..2 * Real.pi, Complex.exp ((Complex.I * (n : ℂ)) * ↑x) = (Complex.exp ((Complex.I * (n : ℂ)) * ↑(2 * Real.pi)) - Complex.exp ((Complex.I * (n : ℂ)) * ↑0)) / (Complex.I * (n : ℂ)) := by
    apply integral_exp_mul_complex
    exact h3
  have h10 : Complex.exp ((Complex.I * (n : ℂ)) * ↑(2 * Real.pi)) = 1 := by simpa using h631
  have h11 : Complex.exp ((Complex.I * (n : ℂ)) * ↑0) = 1 := by simpa using h64
  have h12 : ∫ (x : ℝ) in (0)..2 * Real.pi, Complex.exp ((Complex.I * (n : ℂ)) * ↑x) = (1 - 1) / (Complex.I * (n : ℂ)) := by
    rw [h9, h10, h11]
    <;> ring
  have h13 : (1 - 1 : ℂ) / (Complex.I * (n : ℂ)) = 0 := by ring
  have h14 : ∫ (x : ℝ) in (0)..2 * Real.pi, Complex.exp ((Complex.I * (n : ℂ)) * ↑x) = 0 := by
    rw [h12, h13]
  have h15 : ∫ (x : ℝ) in (0)..2 * Real.pi, Complex.exp (.I * n * x) = ∫ (x : ℝ) in (0)..2 * Real.pi, Complex.exp ((Complex.I * (n : ℂ)) * ↑x) := by
    apply intervalIntegral.integral_congr
    intro x _
    <;> ring_nf
  rw [h15]
  exact h14
