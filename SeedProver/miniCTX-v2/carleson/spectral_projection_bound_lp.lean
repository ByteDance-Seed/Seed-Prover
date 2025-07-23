-- In carleson/Carleson/Classical/SpectralProjectionBound.lean

/- This file contains the proof of Lemma 11.1.10 (spectral projection bound).
   At the moment, its results are not used as the section about truncated Hilbert transforms
   is still missing.
   Thus, the result here might not yet have the exact form needed later.
-/

import Carleson.Classical.Basic

open MeasureTheory AddCircle
open scoped InnerProductSpace

--TODO: move somewhere else?
lemma L2norm_sq_eq {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖f‖ ^ 2 = ∫ (x : AddCircle T), ‖f x‖ ^ 2 ∂haarAddCircle := by
  /- The proof is inspired by parts of the proof of tsum_sq_fourierCoeff. -/
  rw [@norm_sq_eq_inner ℂ, @L2.inner_def (AddCircle T) ℂ ℂ _ _ _ _ _ f f, ← integral_re (L2.integrable_inner f f)]
  simp only [← norm_sq_eq_inner]

lemma fourierCoeff_eq_innerProduct {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ 2)] {f : ↥(Lp ℂ 2 haarAddCircle)} {n : ℤ} :
    fourierCoeff f n = ⟪@fourierLp T hT 2 h2 n, f⟫_ℂ := by
  rw [← coe_fourierBasis, ← fourierBasis_repr]
  exact HilbertBasis.repr_apply_apply fourierBasis f n

noncomputable section
def partialFourierSumLp {T : ℝ} [hT : Fact (0 < T)] (p : ENNReal) [Fact (1 ≤ p)] (N : ℕ) (f : ↥(Lp ℂ 2 (@haarAddCircle T hT))) : Lp ℂ p (@haarAddCircle T hT) :=
    ∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • fourierLp p n

--TODO: add some lemma relating partialFourierSum and partialFourierSumLp

lemma partialFourierSumL2_norm {T : ℝ} [hT : Fact (0 < T)] [h2 : Fact (1 ≤ (2 : ENNReal))] {f : ↥(Lp ℂ 2 haarAddCircle)} {N : ℕ} :
    ‖partialFourierSumLp 2 N f‖ ^ 2 = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖@fourierCoeff T hT _ _ _ f n‖ ^ 2 := by
  calc ‖partialFourierSumLp 2 N f‖ ^ 2
    _ = ‖partialFourierSumLp 2 N f‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast]; rfl
    _ = ‖fourierBasis.repr (partialFourierSumLp 2 N f)‖ ^ (2 : ℝ) := by
      rw [fourierBasis.repr.norm_map (partialFourierSumLp 2 N f)]
    _ = ‖∑ n ∈ Finset.Icc (-Int.ofNat N) N, fourierCoeff f n • (fourierBasis.repr (@fourierLp T hT 2 h2 n))‖ ^ (2 : ℝ) := by
      rw [partialFourierSumLp, map_sum]
      simp_rw [LinearMapClass.map_smul]
    _ = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ (2 : ℝ) := by
      rw [← coe_fourierBasis]
      simp only [LinearIsometryEquiv.apply_symm_apply, lp.coeFn_smul, Pi.smul_apply, ← lp.single_smul]
      have : 2 = (2 : ENNReal).toReal := by simp
      rw [this, ← lp.norm_sum_single (by simp), ← this]
      congr 2
      refine Finset.sum_congr (by simp) fun n ↦ ?_
      simp only [smul_eq_mul, mul_one]
      congr!
    _ = ∑ n ∈ Finset.Icc (-Int.ofNat N) N, ‖fourierCoeff f n‖ ^ 2 := by
      simp_rw [← Real.rpow_natCast]; rfl

lemma spectral_projection_bound_sq {T : ℝ} [hT : Fact (0 < T)] (N : ℕ) (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 N f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  rw [partialFourierSumL2_norm]
  simp_rw [fourierCoeff_eq_innerProduct]
  exact orthonormal_fourier.sum_inner_products_le _

lemma spectral_projection_bound_sq_integral {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ∫ t : AddCircle T, ‖partialFourierSumLp 2 N f t‖ ^ 2 ∂haarAddCircle ≤ ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂haarAddCircle := by
  rw [← L2norm_sq_eq, ← L2norm_sq_eq]
  exact spectral_projection_bound_sq _ _

/- Start of proof attempt -/
lemma round1_spectral_projection_bound_lp {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 N f‖ ≤ ‖f‖ := by
  have h1 : ‖partialFourierSumLp 2 N f‖ ^ 2 ≤ ‖f‖ ^ 2 := spectral_projection_bound_sq N f
  have h2 : ‖partialFourierSumLp 2 N f‖ ≥ 0 := by positivity
  have h3 : ‖f‖ ≥ 0 := by positivity
  nlinarith [sq_nonneg (‖partialFourierSumLp 2 N f‖), sq_nonneg (‖f‖)]

theorem spectral_projection_bound_lp {N : ℕ} {T : ℝ} [hT : Fact (0 < T)] (f : Lp ℂ 2 <| @haarAddCircle T hT) :
    ‖partialFourierSumLp 2 N f‖ ≤ ‖f‖  := by

  exact round1_spectral_projection_bound_lp f
