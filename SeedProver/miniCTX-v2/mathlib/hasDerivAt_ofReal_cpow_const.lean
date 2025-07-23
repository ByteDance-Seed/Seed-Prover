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

/-- Although `fun x => x ^ r` for fixed `r` is *not* complex-differentiable along the negative real
line, it is still real-differentiable, and the derivative is what one would formally expect.
See `hasDerivAt_ofReal_cpow_const` for an alternate formulation. -/
theorem hasDerivAt_ofReal_cpow_const' {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ -1) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1) / (r + 1)) (x ^ r) x := by
  rw [Ne, ← add_eq_zero_iff_eq_neg, ← Ne] at hr
  rcases lt_or_gt_of_ne hx.symm with (hx | hx)
  · -- easy case : `0 < x`
    -- Porting note: proof used to be
    -- convert (((hasDerivAt_id (x : ℂ)).cpow_const _).div_const (r + 1)).comp_ofReal using 1
    -- · rw [add_sub_cancel, id.def, mul_one, mul_comm, mul_div_cancel _ hr]
    -- · rw [id.def, ofReal_re]; exact Or.inl hx
    apply HasDerivAt.comp_ofReal (e := fun y => (y : ℂ) ^ (r + 1) / (r + 1))
    convert HasDerivAt.div_const (𝕜 := ℂ) ?_ (r + 1) using 1
    · exact (mul_div_cancel_right₀ _ hr).symm
    · convert HasDerivAt.cpow_const ?_ ?_ using 1
      · rw [add_sub_cancel_right, mul_comm]; exact (mul_one _).symm
      · exact hasDerivAt_id (x : ℂ)
      · simp [hx]
  · -- harder case : `x < 0`
    have : ∀ᶠ y : ℝ in 𝓝 x,
        (y : ℂ) ^ (r + 1) / (r + 1) = (-y : ℂ) ^ (r + 1) * exp (π * I * (r + 1)) / (r + 1) := by
      refine Filter.eventually_of_mem (Iio_mem_nhds hx) fun y hy => ?_
      rw [ofReal_cpow_of_nonpos (le_of_lt hy)]
    refine HasDerivAt.congr_of_eventuallyEq ?_ this
    rw [ofReal_cpow_of_nonpos (le_of_lt hx)]
    suffices HasDerivAt (fun y : ℝ => (-↑y) ^ (r + 1) * exp (↑π * I * (r + 1)))
        ((r + 1) * (-↑x) ^ r * exp (↑π * I * r)) x by
      convert this.div_const (r + 1) using 1
      conv_rhs => rw [mul_assoc, mul_comm, mul_div_cancel_right₀ _ hr]
    rw [mul_add ((π : ℂ) * _), mul_one, exp_add, exp_pi_mul_I, mul_comm (_ : ℂ) (-1 : ℂ),
      neg_one_mul]
    simp_rw [mul_neg, ← neg_mul, ← ofReal_neg]
    suffices HasDerivAt (fun y : ℝ => (↑(-y) : ℂ) ^ (r + 1)) (-(r + 1) * ↑(-x) ^ r) x by
      convert this.neg.mul_const _ using 1; ring
    suffices HasDerivAt (fun y : ℝ => (y : ℂ) ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) (-x) by
      convert @HasDerivAt.scomp ℝ _ ℂ _ _ x ℝ _ _ _ _ _ _ _ _ this (hasDerivAt_neg x) using 1
      rw [real_smul, ofReal_neg 1, ofReal_one]; ring
    suffices HasDerivAt (fun y : ℂ => y ^ (r + 1)) ((r + 1) * ↑(-x) ^ r) ↑(-x) by
      exact this.comp_ofReal
    conv in ↑_ ^ _ => rw [(by ring : r = r + 1 - 1)]
    convert HasDerivAt.cpow_const ?_ ?_ using 1
    · rw [add_sub_cancel_right, add_sub_cancel_right]; exact (mul_one _).symm
    · exact hasDerivAt_id ((-x : ℝ) : ℂ)
    · simp [hx]

@[deprecated (since := "2024-12-15")] alias hasDerivAt_ofReal_cpow := hasDerivAt_ofReal_cpow_const'

/- Start of proof attempt -/
lemma round1_h1 (x : ℝ)
  (r : ℂ)
  (hr : r ≠ 0):
  r - 1 ≠ -1 := by
  intro h
  have h2 : r = 0 := by
    calc
      r = (r - 1) + 1 := by ring
      _ = (-1) + 1 := by rw [h]
      _ = 0 := by norm_num
  contradiction

lemma round1_h3 (x : ℝ)
  (hx : x ≠ 0)
  (r : ℂ)
  (h1 : r - 1 ≠ -1):
  HasDerivAt (fun y : ℝ => (y : ℂ) ^ ((r - 1) + 1) / ((r - 1) + 1)) (x ^ (r - 1)) x := by
  apply hasDerivAt_ofReal_cpow_const' hx h1

lemma round1_h5 (x : ℝ)
  (hx : x ≠ 0)
  (r : ℂ)
  (hr : r ≠ 0)
  (h1 : r - 1 ≠ -1)
  (h3 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ ((r - 1) + 1) / ((r - 1) + 1)) (x ^ (r - 1)) x):
  HasDerivAt (fun y : ℝ => (y : ℂ) ^ r / r) (x ^ (r - 1)) x := by
  have h4 : (r - 1) + 1 = r := by ring
  have h3' : HasDerivAt (fun y : ℝ => (y : ℂ) ^ ((r - 1) + 1) / ((r - 1) + 1)) (x ^ (r - 1)) x := h3
  simp only [h4] at h3'
  exact h3'

lemma round1_h6 (x : ℝ)
  (hx : x ≠ 0)
  (r : ℂ)
  (hr : r ≠ 0)
  (h1 : r - 1 ≠ -1)
  (h5 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ r / r) (x ^ (r - 1)) x):
  HasDerivAt (fun y : ℝ => r * ((y : ℂ) ^ r / r)) (r * x ^ (r - 1)) x := by
  exact HasDerivAt.const_mul r h5

lemma round1_h7 (x : ℝ)
  (r : ℂ)
  (hr : r ≠ 0):
  ∀ (y : ℝ), r * ((y : ℂ) ^ r / r) = (y : ℂ) ^ r := by
  intro y
  field_simp [hr]
  <;> ring

/-- An alternate formulation of `hasDerivAt_ofReal_cpow_const'`. -/
theorem hasDerivAt_ofReal_cpow_const {x : ℝ} (hx : x ≠ 0) {r : ℂ} (hr : r ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ r) (r * x ^ (r - 1)) x  := by

  have h1 : r - 1 ≠ -1 := by
    exact round1_h1 x r hr
  have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ ((r - 1) + 1) / ((r - 1) + 1)) (x ^ (r - 1)) x := by
    exact round1_h3 x hx r h1
  have h5 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ r / r) (x ^ (r - 1)) x := by
    exact round1_h5 x hx r hr h1 h3
  have h6 : HasDerivAt (fun y : ℝ => r * ((y : ℂ) ^ r / r)) (r * x ^ (r - 1)) x := by
    exact round1_h6 x hx r hr h1 h5
  have h7 : ∀ (y : ℝ), r * ((y : ℂ) ^ r / r) = (y : ℂ) ^ r := by
    exact round1_h7 x r hr
  have h9 : (fun y : ℝ => r * ((y : ℂ) ^ r / r)) = fun y : ℝ => (y : ℂ) ^ r := by
    funext y
    exact h7 y
  rw [h9] at h6
  exact h6
