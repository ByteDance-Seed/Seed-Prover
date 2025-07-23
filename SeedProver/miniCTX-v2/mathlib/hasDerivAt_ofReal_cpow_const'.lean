-- In mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Derivatives of power function on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`

We also prove differentiability and provide derivatives for the power functions `x ^ y`.
-/

noncomputable section

open scoped Real Topology NNReal ENNReal
open Filter

namespace Complex

theorem hasStrictFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
  have A : p.1 ≠ 0 := slitPlane_ne_zero hp
  have : (fun x : ℂ × ℂ => x.1 ^ x.2) =ᶠ[𝓝 p] fun x => exp (log x.1 * x.2) :=
    ((isOpen_ne.preimage continuous_fst).eventually_mem A).mono fun p hp =>
      cpow_def_of_ne_zero hp _
  rw [cpow_sub _ _ A, cpow_one, mul_div_left_comm, mul_smul, mul_smul]
  refine HasStrictFDerivAt.congr_of_eventuallyEq ?_ this.symm
  simpa only [cpow_def_of_ne_zero A, div_eq_mul_inv, mul_smul, add_comm, smul_add] using
    ((hasStrictFDerivAt_fst.clog hp).mul hasStrictFDerivAt_snd).cexp

theorem hasStrictFDerivAt_cpow' {x y : ℂ} (hp : x ∈ slitPlane) :
    HasStrictFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((y * x ^ (y - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (x ^ y * log x) • ContinuousLinearMap.snd ℂ ℂ ℂ) (x, y) :=
  @hasStrictFDerivAt_cpow (x, y) hp

theorem hasStrictDerivAt_const_cpow {x y : ℂ} (h : x ≠ 0 ∨ y ≠ 0) :
    HasStrictDerivAt (fun y => x ^ y) (x ^ y * log x) y := by
  rcases em (x = 0) with (rfl | hx)
  · replace h := h.neg_resolve_left rfl
    rw [log_zero, mul_zero]
    refine (hasStrictDerivAt_const y 0).congr_of_eventuallyEq ?_
    exact (isOpen_ne.eventually_mem h).mono fun y hy => (zero_cpow hy).symm
  · simpa only [cpow_def_of_ne_zero hx, mul_one] using
      ((hasStrictDerivAt_id y).const_mul (log x)).cexp

theorem hasFDerivAt_cpow {p : ℂ × ℂ} (hp : p.1 ∈ slitPlane) :
    HasFDerivAt (fun x : ℂ × ℂ => x.1 ^ x.2)
      ((p.2 * p.1 ^ (p.2 - 1)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (p.1 ^ p.2 * log p.1) • ContinuousLinearMap.snd ℂ ℂ ℂ) p :=
  (hasStrictFDerivAt_cpow hp).hasFDerivAt

end Complex

section fderiv

open Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : E → ℂ} {f' g' : E →L[ℂ] ℂ}
  {x : E} {s : Set E} {c : ℂ}

theorem HasStrictFDerivAt.cpow (hf : HasStrictFDerivAt f f' x) (hg : HasStrictFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert (@hasStrictFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)

theorem HasStrictFDerivAt.const_cpow (hf : HasStrictFDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).comp_hasStrictFDerivAt x hf

theorem HasFDerivAt.cpow (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasFDerivAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') x := by
  convert (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp x (hf.prod hg)

theorem HasFDerivAt.const_cpow (hf : HasFDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFDerivAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivAt x hf

theorem HasFDerivWithinAt.cpow (hf : HasFDerivWithinAt f f' s x) (hg : HasFDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasFDerivWithinAt (fun x => f x ^ g x)
      ((g x * f x ^ (g x - 1)) • f' + (f x ^ g x * Complex.log (f x)) • g') s x := by
  convert
    (@Complex.hasFDerivAt_cpow ((fun x => (f x, g x)) x) h0).comp_hasFDerivWithinAt x (hf.prod hg)

theorem HasFDerivWithinAt.const_cpow (hf : HasFDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasFDerivWithinAt (fun x => c ^ f x) ((c ^ f x * Complex.log c) • f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasFDerivWithinAt x hf

theorem DifferentiableAt.cpow (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (h0 : f x ∈ slitPlane) : DifferentiableAt ℂ (fun x => f x ^ g x) x :=
  (hf.hasFDerivAt.cpow hg.hasFDerivAt h0).differentiableAt

theorem DifferentiableAt.const_cpow (hf : DifferentiableAt ℂ f x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    DifferentiableAt ℂ (fun x => c ^ f x) x :=
  (hf.hasFDerivAt.const_cpow h0).differentiableAt

theorem DifferentiableAt.cpow_const (hf : DifferentiableAt ℂ f x) (h0 : f x ∈ slitPlane) :
    DifferentiableAt ℂ (fun x => f x ^ c) x :=
  hf.cpow (differentiableAt_const c) h0

theorem DifferentiableWithinAt.cpow (hf : DifferentiableWithinAt ℂ f s x)
    (hg : DifferentiableWithinAt ℂ g s x) (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ g x) s x :=
  (hf.hasFDerivWithinAt.cpow hg.hasFDerivWithinAt h0).differentiableWithinAt

theorem DifferentiableWithinAt.const_cpow (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : c ≠ 0 ∨ f x ≠ 0) : DifferentiableWithinAt ℂ (fun x => c ^ f x) s x :=
  (hf.hasFDerivWithinAt.const_cpow h0).differentiableWithinAt

theorem DifferentiableWithinAt.cpow_const (hf : DifferentiableWithinAt ℂ f s x)
    (h0 : f x ∈ slitPlane) :
    DifferentiableWithinAt ℂ (fun x => f x ^ c) s x :=
  hf.cpow (differentiableWithinAt_const c) h0

theorem DifferentiableOn.cpow (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    (h0 : Set.MapsTo f s slitPlane) : DifferentiableOn ℂ (fun x ↦ f x ^ g x) s :=
  fun x hx ↦ (hf x hx).cpow (hg x hx) (h0 hx)

theorem DifferentiableOn.const_cpow (hf : DifferentiableOn ℂ f s)
    (h0 : c ≠ 0 ∨ ∀ x ∈ s, f x ≠ 0) : DifferentiableOn ℂ (fun x ↦ c ^ f x) s :=
  fun x hx ↦ (hf x hx).const_cpow (h0.imp_right fun h ↦ h x hx)

theorem DifferentiableOn.cpow_const (hf : DifferentiableOn ℂ f s)
    (h0 : ∀ x ∈ s, f x ∈ slitPlane) :
    DifferentiableOn ℂ (fun x => f x ^ c) s :=
  hf.cpow (differentiableOn_const c) h0

theorem Differentiable.cpow (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h0 : ∀ x, f x ∈ slitPlane) : Differentiable ℂ (fun x ↦ f x ^ g x) :=
  fun x ↦ (hf x).cpow (hg x) (h0 x)

theorem Differentiable.const_cpow (hf : Differentiable ℂ f)
    (h0 : c ≠ 0 ∨ ∀ x, f x ≠ 0) : Differentiable ℂ (fun x ↦ c ^ f x) :=
  fun x ↦ (hf x).const_cpow (h0.imp_right fun h ↦ h x)

@[fun_prop]
lemma differentiable_const_cpow_of_neZero (z : ℂ) [NeZero z] :
    Differentiable ℂ fun s : ℂ ↦ z ^ s :=
  differentiable_id.const_cpow (.inl <| NeZero.ne z)

@[fun_prop]
lemma differentiableAt_const_cpow_of_neZero (z : ℂ) [NeZero z] (t : ℂ) :
    DifferentiableAt ℂ (fun s : ℂ ↦ z ^ s) t :=
  differentiableAt_id.const_cpow (.inl <| NeZero.ne z)

end fderiv

section deriv

open Complex

variable {f g : ℂ → ℂ} {s : Set ℂ} {f' g' x c : ℂ}

/-- A private lemma that rewrites the output of lemmas like `HasFDerivAt.cpow` to the form
expected by lemmas like `HasDerivAt.cpow`. -/
private theorem aux : ((g x * f x ^ (g x - 1)) • (1 : ℂ →L[ℂ] ℂ).smulRight f' +
    (f x ^ g x * log (f x)) • (1 : ℂ →L[ℂ] ℂ).smulRight g') 1 =
      g x * f x ^ (g x - 1) * f' + f x ^ g x * log (f x) * g' := by
  simp only [Algebra.id.smul_eq_mul, one_mul, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply, Pi.smul_apply,
    ContinuousLinearMap.coe_smul']

nonrec theorem HasStrictDerivAt.cpow (hf : HasStrictDerivAt f f' x) (hg : HasStrictDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasStrictDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa using (hf.cpow hg h0).hasStrictDerivAt

theorem HasStrictDerivAt.const_cpow (hf : HasStrictDerivAt f f' x) (h : c ≠ 0 ∨ f x ≠ 0) :
    HasStrictDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h).comp x hf

theorem Complex.hasStrictDerivAt_cpow_const (h : x ∈ slitPlane) :
    HasStrictDerivAt (fun z : ℂ => z ^ c) (c * x ^ (c - 1)) x := by
  simpa only [mul_zero, add_zero, mul_one] using
    (hasStrictDerivAt_id x).cpow (hasStrictDerivAt_const x c) h

theorem HasStrictDerivAt.cpow_const (hf : HasStrictDerivAt f f' x)
    (h0 : f x ∈ slitPlane) :
    HasStrictDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).comp x hf

theorem HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (h0 : f x ∈ slitPlane) : HasDerivAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') x := by
  simpa only [aux] using (hf.hasFDerivAt.cpow hg h0).hasDerivAt

theorem HasDerivAt.const_cpow (hf : HasDerivAt f f' x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp x hf

theorem HasDerivAt.cpow_const (hf : HasDerivAt f f' x) (h0 : f x ∈ slitPlane) :
    HasDerivAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp x hf

theorem HasDerivWithinAt.cpow (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x)
    (h0 : f x ∈ slitPlane) : HasDerivWithinAt (fun x => f x ^ g x)
      (g x * f x ^ (g x - 1) * f' + f x ^ g x * Complex.log (f x) * g') s x := by
  simpa only [aux] using (hf.hasFDerivWithinAt.cpow hg h0).hasDerivWithinAt

theorem HasDerivWithinAt.const_cpow (hf : HasDerivWithinAt f f' s x) (h0 : c ≠ 0 ∨ f x ≠ 0) :
    HasDerivWithinAt (fun x => c ^ f x) (c ^ f x * Complex.log c * f') s x :=
  (hasStrictDerivAt_const_cpow h0).hasDerivAt.comp_hasDerivWithinAt x hf

theorem HasDerivWithinAt.cpow_const (hf : HasDerivWithinAt f f' s x)
    (h0 : f x ∈ slitPlane) :
    HasDerivWithinAt (fun x => f x ^ c) (c * f x ^ (c - 1) * f') s x :=
  (Complex.hasStrictDerivAt_cpow_const h0).hasDerivAt.comp_hasDerivWithinAt x hf

/- Start of proof attempt -/
lemma round1_h33 (x : ℝ)
  (hx : x ≠ 0)
  (r : ℂ)
  (h5 : x > 0)
  (h4 : (x : ℂ) ∈ Complex.slitPlane):
  HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) x := by
  have h_simp : r + 1 - 1 = r := by ring
  have h511 : HasStrictDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (x : ℂ) ^ (r + 1 - 1)) (x : ℂ) :=
    Complex.hasStrictDerivAt_cpow_const h4
  have h51 : HasStrictDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) (x : ℂ) := by
    rw [h_simp] at h511
    exact h511
  have h52 : HasDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) (x : ℂ) := h51.hasDerivAt
  have h53 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) x := by
    exact h52.comp_ofReal
  exact h53

lemma round1_h17 (x : ℝ)
  (r : ℂ):
  HasDerivAt (fun y : ℝ => - (y : ℂ)) (-1) x := by
  have h171 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    have h1711 : HasDerivAt (fun z : ℂ => z) 1 (x : ℂ) := hasDerivAt_id (x : ℂ)
    exact h1711.comp_ofReal
  have h172 : HasDerivAt (fun y : ℝ => - (y : ℂ)) (-1) x := by
    exact h171.neg
  exact h172

lemma round1_h18' (x : ℝ)
  (r : ℂ)
  (h6 : x < 0)
  (h15 : (- (x : ℂ)) ∈ Complex.slitPlane)
  (h16 : HasDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (- (x : ℂ)) ^ r) (- (x : ℂ)))
  (h17 : HasDerivAt (fun y : ℝ => - (y : ℂ)) (-1) x):
  HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1)) (- (r + 1) * (- (x : ℂ)) ^ r) x := by
  have h181 : HasDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (- (x : ℂ)) ^ r) (- (x : ℂ)) := h16
  have h182 : HasDerivAt (fun y : ℝ => - (y : ℂ)) (-1) x := h17
  have h183 : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1)) (((r + 1) * (- (x : ℂ)) ^ r) * (-1)) x := by
    apply HasDerivAt.comp x h181 h182
  have h184 : ((r + 1) * (- (x : ℂ)) ^ r) * (-1) = - (r + 1) * (- (x : ℂ)) ^ r := by ring
  rw [h184] at h183
  exact h183

lemma round1_h23 (x : ℝ)
  (hx : x ≠ 0)
  (r : ℂ)
  (h6 : x < 0)
  (h14 : - Complex.exp (↑Real.pi * Complex.I * (r + 1)) * (r + 1) * ((- (x : ℂ)) ^ r) = (r + 1) * (x : ℂ) ^ r)
  (h15 : (- (x : ℂ)) ∈ Complex.slitPlane)
  (h16 : HasDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (- (x : ℂ)) ^ r) (- (x : ℂ)))
  (h17 : HasDerivAt (fun y : ℝ => - (y : ℂ)) (-1) x)
  (h18' : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1)) (- (r + 1) * (- (x : ℂ)) ^ r) x)
  (h19 : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) ((r + 1) * (x : ℂ) ^ r) x)
  (h21 : ∀ (y : ℝ), y ≤ 0 → (y : ℂ) ^ (r + 1) = (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1)))
  (h22 : (fun y : ℝ => (y : ℂ) ^ (r + 1)) =ᶠ[𝓝 x] (fun y : ℝ => (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1)))):
  HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) x := by
  apply HasDerivAt.congr_of_eventuallyEq h19 h22

/-- Although `fun x => x ^ r` for fixed `r` is *not* complex-differentiable along the negative real
line, it is still real-differentiable, and the derivative is what one would formally expect.
See `hasDerivAt_ofReal_cpow_const` for an alternate formulation. -/
theorem hasDerivAt_ofReal_cpow_const' {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ -1) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1) / (r + 1)) (x ^ r) x  := by

  have h1 : r + 1 ≠ 0 := by
    intro h
    have h2 : r = -1 := by
      calc
        r = (r + 1) - 1 := by ring
        _ = 0 - 1 := by rw [h]
        _ = -1 := by ring
    contradiction

  by_cases h5 : x > 0
  · -- Case 1: x > 0
    have h4 : (x : ℂ) ∈ Complex.slitPlane := by
      simp [Complex.slitPlane, h5]
      <;> norm_num <;> linarith

    have h33 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) x := by
      exact round1_h33 x hx r h5 h4

    have h34 : HasDerivAt (fun y : ℝ => ((y : ℂ) ^ (r + 1)) / (r + 1)) (((r + 1) * (x : ℂ) ^ r) / (r + 1)) x := by
      apply HasDerivAt.div_const
      exact h33

    have h35 : ((r + 1) * (x : ℂ) ^ r) / (r + 1) = (x : ℂ) ^ r := by
      field_simp [h1]
      <;> ring

    rw [h35] at h34
    exact h34

  · -- Case 2: x ≤ 0. Since x ≠ 0, then x < 0
    have h6 : x < 0 := by
      by_contra h6
      have h6' : x = 0 := by linarith
      contradiction

    have h7 : x ≤ 0 := by linarith

    have h10 : - Complex.exp (↑Real.pi * Complex.I * (r + 1)) = Complex.exp (↑Real.pi * Complex.I * r) := by
      have h11 : Complex.exp (↑Real.pi * Complex.I * (r + 1)) = Complex.exp (↑Real.pi * Complex.I * r + ↑Real.pi * Complex.I) := by ring_nf
      have h12 : Complex.exp (↑Real.pi * Complex.I * r + ↑Real.pi * Complex.I) = Complex.exp (↑Real.pi * Complex.I * r) * Complex.exp (↑Real.pi * Complex.I) := by rw [Complex.exp_add]
      have h13 : Complex.exp (↑Real.pi * Complex.I) = -1 := Complex.exp_pi_mul_I
      rw [h11, h12, h13]
      <;> ring

    have h14 : - Complex.exp (↑Real.pi * Complex.I * (r + 1)) * (r + 1) * ((- (x : ℂ)) ^ r) = (r + 1) * (x : ℂ) ^ r := by
      have h141 : (x : ℂ) ^ r = (- (x : ℂ)) ^ r * Complex.exp (↑Real.pi * Complex.I * r) := by
        rw [Complex.ofReal_cpow_of_nonpos h7 r]
        <;> ring
      calc
        - Complex.exp (↑Real.pi * Complex.I * (r + 1)) * (r + 1) * ((- (x : ℂ)) ^ r)
          = (- Complex.exp (↑Real.pi * Complex.I * (r + 1))) * (r + 1) * ((- (x : ℂ)) ^ r) := by ring
        _ = Complex.exp (↑Real.pi * Complex.I * r) * (r + 1) * ((- (x : ℂ)) ^ r) := by rw [h10]
        _ = (r + 1) * ((- (x : ℂ)) ^ r) * Complex.exp (↑Real.pi * Complex.I * r) := by ring
        _ = (r + 1) * ((- (x : ℂ)) ^ r * Complex.exp (↑Real.pi * Complex.I * r)) := by ring
        _ = (r + 1) * (x : ℂ) ^ r := by rw [h141]

    have h15 : (- (x : ℂ)) ∈ Complex.slitPlane := by
      simp [Complex.slitPlane, h6]
      <;> norm_num <;> linarith

    have h161 : HasStrictDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (- (x : ℂ)) ^ r) (- (x : ℂ)) := by
      have h162 := @Complex.hasStrictDerivAt_cpow_const (- (x : ℂ)) (r + 1) h15
      simpa using h162

    have h16 : HasDerivAt (fun z : ℂ => z ^ (r + 1)) ((r + 1) * (- (x : ℂ)) ^ r) (- (x : ℂ)) := h161.hasDerivAt

    have h17 : HasDerivAt (fun y : ℝ => - (y : ℂ)) (-1) x := by
      exact round1_h17 x r

    have h18' : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1)) (- (r + 1) * (- (x : ℂ)) ^ r) x := by
      exact round1_h18' x r h6 h15 h16 h17

    have h19 : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) ((r + 1) * (x : ℂ) ^ r) x := by
      have h191 : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) (((- (r + 1) * (- (x : ℂ)) ^ r)) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) x := by
        have h1911 : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1)) (- (r + 1) * (- (x : ℂ)) ^ r) x := h18'
        have h1912 : HasDerivAt (fun y : ℝ => (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) (((- (r + 1) * (- (x : ℂ)) ^ r)) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) x := by
          apply HasDerivAt.mul_const
          exact h1911
        simpa using h1912
      have h20 : (- (r + 1) * (- (x : ℂ)) ^ r) * Complex.exp (↑Real.pi * Complex.I * (r + 1)) = (r + 1) * (x : ℂ) ^ r := by
        have h201 : (- (r + 1) * (- (x : ℂ)) ^ r) * Complex.exp (↑Real.pi * Complex.I * (r + 1)) = - (r + 1) * (- (x : ℂ)) ^ r * Complex.exp (↑Real.pi * Complex.I * (r + 1)) := by ring
        have h202 : - (r + 1) * (- (x : ℂ)) ^ r * Complex.exp (↑Real.pi * Complex.I * (r + 1)) = - Complex.exp (↑Real.pi * Complex.I * (r + 1)) * (r + 1) * ((- (x : ℂ)) ^ r) := by ring
        rw [h201, h202]
        simpa using h14
      rw [h20] at h191
      exact h191

    have h21 : ∀ (y : ℝ), y ≤ 0 → (y : ℂ) ^ (r + 1) = (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1)) := by
      intro y hy
      have h211 : (y : ℂ) ^ (r + 1) = (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1)) := by
        rw [Complex.ofReal_cpow_of_nonpos hy (r + 1)]
        <;> ring
      exact h211

    have h22 : (fun y : ℝ => (y : ℂ) ^ (r + 1)) =ᶠ[𝓝 x] (fun y : ℝ => (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1))) := by
      have h221 : ∀ y : ℝ, y < 0 → (y : ℂ) ^ (r + 1) = (- (y : ℂ)) ^ (r + 1) * Complex.exp (↑Real.pi * Complex.I * (r + 1)) := by
        intro y hy
        exact h21 y (by linarith)
      have h222 : ∀ᶠ (y : ℝ) in 𝓝 x, y < 0 := by
        have h223 : ∃ ε > 0, ∀ y : ℝ, y ∈ Metric.ball x ε → y < 0 := by
          use (-x) / 2
          constructor
          · linarith
          · intro y hy
            have h224 : dist y x < (-x) / 2 := by simpa using hy
            have h225 : y < 0 := by
              have h226 : dist y x = |y - x| := by simp [Real.dist_eq]
              rw [h226] at h224
              cases' abs_cases (y - x) with h227 h227 <;> linarith
            linarith
        rcases h223 with ⟨ε, hε0, hε⟩
        refine Metric.eventually_nhds_iff.mpr ⟨ε, hε0, ?_⟩
        intro y hy
        exact hε y hy
      filter_upwards [h222] with y hy
      exact h221 y hy

    have h23 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * (x : ℂ) ^ r) x := by
      exact round1_h23 x hx r h6 h14 h15 h16 h17 h18' h19 h21 h22

    have h34 : HasDerivAt (fun y : ℝ => ((y : ℂ) ^ (r + 1)) / (r + 1)) (((r + 1) * (x : ℂ) ^ r) / (r + 1)) x := by
      apply HasDerivAt.div_const
      exact h23

    have h35 : ((r + 1) * (x : ℂ) ^ r) / (r + 1) = (x : ℂ) ^ r := by
      field_simp [h1]
      <;> ring

    rw [h35] at h34
    exact h34
