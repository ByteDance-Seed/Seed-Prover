-- In mathlib/Mathlib/RingTheory/Polynomial/HilbertPoly.lean

/-
Copyright (c) 2024 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.FieldSimp

/-!
# Hilbert polynomials

In this file, we formalise the following statement: if `F` is a field with characteristic `0`, then
given any `p : F[X]` and `d : ℕ`, there exists some `h : F[X]` such that for any large enough
`n : ℕ`, `h(n)` is equal to the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
This `h` is unique and is denoted as `Polynomial.hilbertPoly p d`.

For example, given `d : ℕ`, the power series expansion of `1/(1 - X)ᵈ⁺¹` in `F[X]`
is `Σₙ ((d + n).choose d)Xⁿ`, which equals `Σₙ ((n + 1)···(n + d)/d!)Xⁿ` and hence
`Polynomial.hilbertPoly (1 : F[X]) (d + 1)` is the polynomial `(X + 1)···(X + d)/d!`. Note that
if `d! = 0` in `F`, then the polynomial `(X + 1)···(X + d)/d!` no longer works, so we do not want
the characteristic of `F` to be divisible by `d!`. As `Polynomial.hilbertPoly` may take any
`p : F[X]` and `d : ℕ` as its inputs, it is necessary for us to assume that `CharZero F`.

## Main definitions

* `Polynomial.hilbertPoly p d`. Given a field `F`, a polynomial `p : F[X]` and a natural number `d`,
  if `F` is of characteristic `0`, then `Polynomial.hilbertPoly p d : F[X]` is the polynomial whose
  value at `n` equals the coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.

## TODO

* Hilbert polynomials of finitely generated graded modules over Noetherian rings.
-/

open Nat PowerSeries

variable (F : Type*) [Field F]

namespace Polynomial

/--
For any field `F` and natural numbers `d` and `k`, `Polynomial.preHilbertPoly F d k`
is defined as `(d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (X - (C (k : F)) + 1))`.
This is the most basic form of Hilbert polynomials. `Polynomial.preHilbertPoly ℚ d 0`
is exactly the Hilbert polynomial of the polynomial ring `ℚ[X_0,...,X_d]` viewed as
a graded module over itself. In fact, `Polynomial.preHilbertPoly F d k` is the
same as `Polynomial.hilbertPoly ((X : F[X]) ^ k) (d + 1)` for any field `F` and
`d k : ℕ` (see the lemma `Polynomial.hilbertPoly_X_pow_succ`). See also the lemma
`Polynomial.preHilbertPoly_eq_choose_sub_add`, which states that if `CharZero F`,
then for any `d k n : ℕ` with `k ≤ n`, `(Polynomial.preHilbertPoly F d k).eval (n : F)`
equals `(n - k + d).choose d`.
-/
noncomputable def preHilbertPoly (d k : ℕ) : F[X] :=
  (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1))

lemma natDegree_preHilbertPoly [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).natDegree = d := by
  have hne : (d ! : F) ≠ 0 := by norm_cast; positivity
  rw [preHilbertPoly, natDegree_smul _ (inv_ne_zero hne), natDegree_comp, ascPochhammer_natDegree,
    add_comm_sub, ← C_1, ← map_sub, natDegree_add_C, natDegree_X, mul_one]

lemma coeff_preHilbertPoly_self [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).coeff d = (d ! : F)⁻¹ := by
  delta preHilbertPoly
  have hne : (d ! : F) ≠ 0 := by norm_cast; positivity
  have heq : d = ((ascPochhammer F d).comp (X - C (k : F) + 1)).natDegree :=
    (natDegree_preHilbertPoly F d k).symm.trans (natDegree_smul _ (inv_ne_zero hne))
  nth_rw 3 [heq]
  calc
  _ = (d ! : F)⁻¹ • ((ascPochhammer F d).comp (X - C ((k : F) - 1))).leadingCoeff := by
    simp only [sub_add, ← C_1, ← map_sub, coeff_smul, coeff_natDegree]
  _ = (d ! : F)⁻¹ := by
    simp only [leadingCoeff_comp (ne_of_eq_of_ne (natDegree_X_sub_C _) one_ne_zero), Monic.def.1
      (monic_ascPochhammer _ _), one_mul, leadingCoeff_X_sub_C, one_pow, smul_eq_mul, mul_one]

lemma leadingCoeff_preHilbertPoly [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).leadingCoeff = (d ! : F)⁻¹ := by
  rw [leadingCoeff, natDegree_preHilbertPoly, coeff_preHilbertPoly_self]

lemma preHilbertPoly_eq_choose_sub_add [CharZero F] (d : ℕ) {k n : ℕ} (hkn : k ≤ n):
    (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d := by
  have : (d ! : F) ≠ 0 := by norm_cast; positivity
  calc
  _ = (↑d !)⁻¹ * eval (↑(n - k + 1)) (ascPochhammer F d) := by simp [cast_sub hkn, preHilbertPoly]
  _ = (n - k + d).choose d := by
    rw [ascPochhammer_nat_eq_natCast_ascFactorial];
    field_simp [ascFactorial_eq_factorial_mul_choose]

variable {F}

/--
`Polynomial.hilbertPoly p 0 = 0`; for any `d : ℕ`, `Polynomial.hilbertPoly p (d + 1)`
is defined as `∑ i ∈ p.support, (p.coeff i) • Polynomial.preHilbertPoly F d i`. If
`M` is a graded module whose Poincaré series can be written as `p(X)/(1 - X)ᵈ` for some
`p : ℚ[X]` with integer coefficients, then `Polynomial.hilbertPoly p d` is the Hilbert
polynomial of `M`. See also `Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval`,
which says that `PowerSeries.coeff F n (p * PowerSeries.invOneSubPow F d)` equals
`(Polynomial.hilbertPoly p d).eval (n : F)` for any large enough `n : ℕ`.
-/
noncomputable def hilbertPoly (p : F[X]) : (d : ℕ) → F[X]
  | 0 => 0
  | d + 1 => ∑ i ∈ p.support, (p.coeff i) • preHilbertPoly F d i

lemma hilbertPoly_zero_left (d : ℕ) : hilbertPoly (0 : F[X]) d = 0 := by
  delta hilbertPoly; induction d with
  | zero => simp only
  | succ d _ => simp only [coeff_zero, zero_smul, Finset.sum_const_zero]

lemma hilbertPoly_zero_right (p : F[X]) : hilbertPoly p 0 = 0 := rfl

lemma hilbertPoly_succ (p : F[X]) (d : ℕ) :
    hilbertPoly p (d + 1) = ∑ i ∈ p.support, (p.coeff i) • preHilbertPoly F d i := rfl

lemma hilbertPoly_X_pow_succ (d k : ℕ) :
    hilbertPoly ((X : F[X]) ^ k) (d + 1) = preHilbertPoly F d k := by
  delta hilbertPoly; simp

lemma hilbertPoly_add_left (p q : F[X]) (d : ℕ) :
    hilbertPoly (p + q) d = hilbertPoly p d + hilbertPoly q d := by
  delta hilbertPoly
  induction d with
  | zero => simp only [add_zero]
  | succ d _ =>
      simp only [← coeff_add]
      rw [← sum_def _ fun _ r => r • _]
      exact sum_add_index _ _ _ (fun _ => zero_smul ..) (fun _ _ _ => add_smul ..)

lemma hilbertPoly_smul (a : F) (p : F[X]) (d : ℕ) :
    hilbertPoly (a • p) d = a • hilbertPoly p d := by
  delta hilbertPoly
  induction d with
  | zero => simp only [smul_zero]
  | succ d _ =>
      simp only
      rw [← sum_def _ fun _ r => r • _, ← sum_def _ fun _ r => r • _, Polynomial.smul_sum,
        sum_smul_index' _ _ _ fun i => zero_smul F (preHilbertPoly F d i)]
      simp only [smul_assoc]

variable (F) in
/--
The function that sends any `p : F[X]` to `Polynomial.hilbertPoly p d` is an `F`-linear map from
`F[X]` to `F[X]`.
-/
noncomputable def hilbertPoly_linearMap (d : ℕ) : F[X] →ₗ[F] F[X] where
  toFun p := hilbertPoly p d
  map_add' p q := hilbertPoly_add_left p q d
  map_smul' r p := hilbertPoly_smul r p d

variable [CharZero F]

/--
The key property of Hilbert polynomials. If `F` is a field with characteristic `0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbertPoly p d).eval (n : F)` equals the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
theorem coeff_mul_invOneSubPow_eq_hilbertPoly_eval
    {p : F[X]} (d : ℕ) {n : ℕ} (hn : p.natDegree < n) :
    PowerSeries.coeff F n (p * invOneSubPow F d) = (hilbertPoly p d).eval (n : F) := by
  delta hilbertPoly; induction d with
  | zero => simp only [invOneSubPow_zero, Units.val_one, mul_one, coeff_coe, eval_zero]
            exact coeff_eq_zero_of_natDegree_lt hn
  | succ d hd =>
      simp only [eval_finset_sum, eval_smul, smul_eq_mul]
      rw [← Finset.sum_coe_sort]
      have h_le (i : p.support) : (i : ℕ) ≤ n :=
        le_trans (le_natDegree_of_ne_zero <| mem_support_iff.1 i.2) hn.le
      have h (i : p.support) : eval ↑n (preHilbertPoly F d ↑i) = (n + d - ↑i).choose d := by
        rw [preHilbertPoly_eq_choose_sub_add _ _ (h_le i), Nat.sub_add_comm (h_le i)]
      simp_rw [h]
      rw [Finset.sum_coe_sort _ (fun x => (p.coeff ↑x) * (_ + d - ↑x).choose _),
        PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ (zero_lt_succ d)]
      simp only [coeff_coe, coeff_mk]
      symm
      refine Finset.sum_subset_zero_on_sdiff (fun s hs ↦ ?_) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
      · rw [Finset.mem_range_succ_iff]
        exact h_le ⟨s, hs⟩
      · simp only [Finset.mem_sdiff, mem_support_iff, not_not] at hx
        rw [hx.2, zero_mul]
      · rw [add_comm, Nat.add_sub_assoc (h_le ⟨x, hx⟩), succ_eq_add_one, add_tsub_cancel_right]

/--
The polynomial satisfying the key property of `Polynomial.hilbertPoly p d` is unique.
-/
theorem existsUnique_hilbertPoly (p : F[X]) (d : ℕ) :
    ∃! h : F[X], ∃ N : ℕ, ∀ n > N,
    PowerSeries.coeff F n (p * invOneSubPow F d) = h.eval (n : F) := by
  use hilbertPoly p d; constructor
  · use p.natDegree
    exact fun n => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d
  · rintro h ⟨N, hhN⟩
    apply eq_of_infinite_eval_eq h (hilbertPoly p d)
    apply ((Set.Ioi_infinite (max N p.natDegree)).image cast_injective.injOn).mono
    rintro x ⟨n, hn, rfl⟩
    simp only [Set.mem_Ioi, sup_lt_iff, Set.mem_setOf_eq] at hn ⊢
    rw [← coeff_mul_invOneSubPow_eq_hilbertPoly_eval d hn.2, hhN n hn.1]

@[deprecated (since := "2024-12-17")] alias exists_unique_hilbertPoly := existsUnique_hilbertPoly

/--
If `h : F[X]` and there exists some `N : ℕ` such that for any number `n : ℕ` bigger than `N`
we have `PowerSeries.coeff F n (p * invOneSubPow F d) = h.eval (n : F)`, then `h` is exactly
`Polynomial.hilbertPoly p d`.
-/
theorem eq_hilbertPoly_of_forall_coeff_eq_eval
    {p h : F[X]} {d : ℕ} (N : ℕ) (hhN : ∀ n > N,
    PowerSeries.coeff F n (p * invOneSubPow F d) = h.eval (n : F)) :
    h = hilbertPoly p d :=
  ExistsUnique.unique (existsUnique_hilbertPoly p d) ⟨N, hhN⟩
    ⟨p.natDegree, fun _ x => coeff_mul_invOneSubPow_eq_hilbertPoly_eval d x⟩

lemma hilbertPoly_mul_one_sub_succ (p : F[X]) (d : ℕ) :
    hilbertPoly (p * (1 - X)) (d + 1) = hilbertPoly p d := by
  apply eq_hilbertPoly_of_forall_coeff_eq_eval (p * (1 - X)).natDegree
  intro n hn
  have heq : 1 - PowerSeries.X = ((1 - X : F[X]) : F⟦X⟧) := by simp only [coe_sub, coe_one, coe_X]
  rw [← one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val F d 1, pow_one, ← mul_assoc, heq,
    ← coe_mul, coeff_mul_invOneSubPow_eq_hilbertPoly_eval (d + 1) hn]

lemma hilbertPoly_mul_one_sub_pow_add (p : F[X]) (d e : ℕ) :
    hilbertPoly (p * (1 - X) ^ e) (d + e) = hilbertPoly p d := by
  induction e with
  | zero => simp
  | succ e he => rw [pow_add, pow_one, ← mul_assoc, ← add_assoc, hilbertPoly_mul_one_sub_succ, he]

lemma hilbertPoly_eq_zero_of_le_rootMultiplicity_one
    {p : F[X]} {d : ℕ} (hdp : d ≤ p.rootMultiplicity 1) :
    hilbertPoly p d = 0 := by
  by_cases hp : p = 0
  · rw [hp, hilbertPoly_zero_left]
  · rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1 with ⟨q, hq1, hq2⟩
    have heq : p = q * (- 1) ^ p.rootMultiplicity 1 * (1 - X) ^ p.rootMultiplicity 1 := by
      simp only [mul_assoc, ← mul_pow, neg_mul, one_mul, neg_sub]
      exact hq1.trans (mul_comm _ _)
    rw [heq, ← zero_add d, ← Nat.sub_add_cancel hdp, pow_add (1 - X), ← mul_assoc,
      hilbertPoly_mul_one_sub_pow_add, hilbertPoly]

/- Start of proof attempt -/
lemma round1_h10 (F : Type*) [Field F] :
  (X - C 1 : F[X]) = C (-1) * (1 - X) := by
  ext n
  simp [coeff_sub, coeff_X, coeff_C, coeff_one, coeff_mul, coeff_C_mul]
  <;> ring

lemma round1_h15 (F : Type*) [Field F] [CharZero F] (k d : ℕ) (p q : F[X]) (h14 : d = (d - k) + k)
  (h13 : p = (q * C ((-1 : F) ^ k)) * (1 - X) ^ k) :
  hilbertPoly p d = hilbertPoly (q * C ((-1 : F) ^ k)) (d - k) := by
  have h151 : hilbertPoly ((q * C ((-1 : F) ^ k)) * (1 - X) ^ k) ((d - k) + k) = hilbertPoly (q * C ((-1 : F) ^ k)) (d - k) := by
    exact hilbertPoly_mul_one_sub_pow_add (q * C ((-1 : F) ^ k)) (d - k) k
  have h152 : p = (q * C ((-1 : F) ^ k)) * (1 - X) ^ k := h13
  have h153 : hilbertPoly p ((d - k) + k) = hilbertPoly ((q * C ((-1 : F) ^ k)) * (1 - X) ^ k) ((d - k) + k) := by
    rw [h152]
  have h154 : hilbertPoly p d = hilbertPoly p ((d - k) + k) := by
    have h14' : d = (d - k) + k := h14
    rw [h14']
    <;> simp
  have h155 : hilbertPoly p d = hilbertPoly ((q * C ((-1 : F) ^ k)) * (1 - X) ^ k) ((d - k) + k) := by
    rw [h154, h153]
  rw [h155, h151]

lemma round1_h16 (F : Type*) [Field F] [CharZero F] (k d : ℕ) (p q : F[X]) (h13 : p = (q * C ((-1 : F) ^ k)) * (1 - X) ^ k)
  (h15 : hilbertPoly p d = hilbertPoly (q * C ((-1 : F) ^ k)) (d - k)) :
  hilbertPoly p d = ((-1 : F) ^ k) • hilbertPoly q (d - k) := by
  have h161 : q * C ((-1 : F) ^ k) = ((-1 : F) ^ k) • q := by
    simp [smul_eq_C_mul]
    <;> ring
  have h1611 : hilbertPoly (q * C ((-1 : F) ^ k)) (d - k) = hilbertPoly (((-1 : F) ^ k) • q) (d - k) := by
    rw [h161]
  have h162 : hilbertPoly (((-1 : F) ^ k) • q) (d - k) = ((-1 : F) ^ k) • hilbertPoly q (d - k) := by
    exact hilbertPoly_smul ((-1 : F) ^ k) q (d - k)
  calc
    hilbertPoly p d = hilbertPoly (q * C ((-1 : F) ^ k)) (d - k) := h15
    _ = hilbertPoly (((-1 : F) ^ k) • q) (d - k) := h1611
    _ = ((-1 : F) ^ k) • hilbertPoly q (d - k) := h162

lemma round1_h23 (F : Type*) [Field F] [CharZero F] (m : ℕ) (q : F[X]) (hq2 : ¬ (X - C 1 : F[X]) ∣ q) (hq'_ne_zero : q ≠ 0) :
  (hilbertPoly q (m + 1)).coeff m ≠ 0 := by
  have h231 : hilbertPoly q (m + 1) = ∑ i ∈ q.support, (q.coeff i) • preHilbertPoly F m i := by
    simp [hilbertPoly]
    <;> aesop
  have h232 : (hilbertPoly q (m + 1)).coeff m = ∑ i in q.support, (q.coeff i) * (preHilbertPoly F m i).coeff m := by
    rw [h231]
    simp [Finset.sum_apply, coeff_smul]
    <;> ring
  have h233 : ∀ i ∈ q.support, (preHilbertPoly F m i).coeff m = (m ! : F)⁻¹ := by
    intro i _
    exact coeff_preHilbertPoly_self F m i
  have h234 : (hilbertPoly q (m + 1)).coeff m = ∑ i in q.support, (q.coeff i) * (m ! : F)⁻¹ := by
    rw [h232]
    apply Finset.sum_congr rfl
    intro i hi
    rw [h233 i hi]
  have h235 : (hilbertPoly q (m + 1)).coeff m = (m ! : F)⁻¹ * ∑ i in q.support, q.coeff i := by
    have h : ∑ i in q.support, (q.coeff i) * (m ! : F)⁻¹ = (m ! : F)⁻¹ * ∑ i in q.support, q.coeff i := by
      rw [Finset.mul_sum]
      <;> simp [mul_comm]
      <;> ring
    rw [h234, h]
  have h2361 : ∑ i in q.support, q.coeff i = q.eval 1 := by
    have h : q.eval 1 = ∑ i in q.support, q.coeff i := by
      simp [Polynomial.eval_eq_sum, mul_one]
      <;> aesop
    exact h.symm
  have hq_eval_1_ne_zero : q.eval 1 ≠ 0 := by
    by_contra hq_eval_1_eq_zero
    have h22 : (X - C 1 : F[X]) ∣ q := by
      have h221 : IsRoot q 1 := by
        simpa [IsRoot] using hq_eval_1_eq_zero
      exact?
    contradiction
  have h237 : (m ! : F) ≠ 0 := by
    norm_cast
    <;> positivity
  have h238 : (m ! : F)⁻¹ ≠ 0 := inv_ne_zero h237
  have h239 : (hilbertPoly q (m + 1)).coeff m = (m ! : F)⁻¹ * q.eval 1 := by
    rw [h235, h2361]
  have h240 : (m ! : F)⁻¹ * q.eval 1 ≠ 0 := mul_ne_zero h238 hq_eval_1_ne_zero
  rw [h239]
  exact h240

lemma round1_h254 (F : Type*) [Field F] [CharZero F] (m : ℕ) (q : F[X]) (hq2 : ¬ (X - C 1 : F[X]) ∣ q) (hq'_ne_zero : q ≠ 0)
  (h23 : (hilbertPoly q (m + 1)).coeff m ≠ 0)
  (h24 : ∀ n : ℕ, n > m → (hilbertPoly q (m + 1)).coeff n = 0) :
  (hilbertPoly q (m + 1)).natDegree = m := by
  have h251 : (hilbertPoly q (m + 1)).coeff m ≠ 0 := h23
  have h253 : (hilbertPoly q (m + 1)).natDegree ≤ m := by
    by_contra h
    have h2531 : (hilbertPoly q (m + 1)).natDegree > m := by linarith
    have h2533 : (hilbertPoly q (m + 1)).coeff (hilbertPoly q (m + 1)).natDegree = 0 := by
      have h2534 := h24 (hilbertPoly q (m + 1)).natDegree (by linarith)
      simpa using h2534
    have h2535 : (hilbertPoly q (m + 1)).coeff (hilbertPoly q (m + 1)).natDegree = (hilbertPoly q (m + 1)).leadingCoeff := by
      simp [Polynomial.coeff_natDegree]
    rw [h2535] at h2533
    have h2536 : (hilbertPoly q (m + 1)).leadingCoeff = 0 := by simpa using h2533
    have h2537 : (hilbertPoly q (m + 1)) = 0 := by
      by_contra h25371
      have h25372 : (hilbertPoly q (m + 1)).leadingCoeff ≠ 0 := by
        exact?
      contradiction
    have h2538 : (hilbertPoly q (m + 1)).coeff m = 0 := by
      rw [h2537]
      <;> simp
    contradiction
  have h2541 : (hilbertPoly q (m + 1)).coeff m ≠ 0 := h23
  have h2542 : m ≤ (hilbertPoly q (m + 1)).natDegree := by
    by_contra h2542
    have h2543 : (hilbertPoly q (m + 1)).natDegree < m := by linarith
    have h2544 : (hilbertPoly q (m + 1)).coeff m = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact h2543
    contradiction
  have h2543 : (hilbertPoly q (m + 1)).natDegree ≤ m := h253
  have h2544 : m ≤ (hilbertPoly q (m + 1)).natDegree := h2542
  linarith

theorem natDegree_hilbertPoly_of_ne_zero_of_rootMultiplicity_lt
    {p : F[X]} {d : ℕ} (hp : p ≠ 0) (hpd : p.rootMultiplicity 1 < d) :
    (hilbertPoly p d).natDegree = d - p.rootMultiplicity 1 - 1  := by

  set k := p.rootMultiplicity 1 with hk_def
  have h1 : k < d := hpd
  have h2 : k ≤ d := by linarith
  have h3 : d - k ≥ 1 := by omega
  have h41 : ∃ m : ℕ, d - k = m + 1 := by
    refine ⟨d - k - 1,?_⟩
    omega
  rcases h41 with ⟨m, hm⟩
  have h42 : ∃ (q : F[X]), p = (X - C 1 : F[X]) ^ k * q ∧ ¬ (X - C 1 : F[X]) ∣ q := by
    have h421 := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 1
    rcases h421 with ⟨q, hq1, hq2⟩
    refine ⟨q,?_,?_⟩
    · exact hq1
    · simpa using hq2
  rcases h42 with ⟨q, hq1, hq2⟩
  have hq'_ne_zero : q ≠ 0 := by
    by_contra hq'_eq_zero
    have h21 : p = 0 := by
      rw [hq1, hq'_eq_zero]
      <;> ring
    contradiction

  have h10 : (X - C 1 : F[X]) = C (-1) * (1 - X) := by
    exact round1_h10 F

  have h101 : (X - C 1 : F[X]) ^ k = C ((-1 : F) ^ k) * (1 - X) ^ k := by
    have h1011 : (X - C 1 : F[X]) = C (-1) * (1 - X) := h10
    calc
      (X - C 1 : F[X]) ^ k = (C (-1) * (1 - X)) ^ k := by rw [h1011]
      _ = (C (-1)) ^ k * (1 - X) ^ k := by rw [mul_pow]
      _ = C ((-1 : F) ^ k) * (1 - X) ^ k := by simp [C_pow]
  
  have h13 : p = (q * C ((-1 : F) ^ k)) * (1 - X) ^ k := by
    have h131 : p = (X - C 1 : F[X]) ^ k * q := hq1
    have h132 : (X - C 1 : F[X]) ^ k = C ((-1 : F) ^ k) * (1 - X) ^ k := h101
    calc
      p = (X - C 1 : F[X]) ^ k * q := h131
      _ = (C ((-1 : F) ^ k) * (1 - X) ^ k) * q := by rw [h132]
      _ = (q * C ((-1 : F) ^ k)) * (1 - X) ^ k := by ring
  
  have h14 : d = (d - k) + k := by omega

  have h15 : hilbertPoly p d = hilbertPoly (q * C ((-1 : F) ^ k)) (d - k) := by
    exact round1_h15 F k d p q h14 h13

  have h16 : hilbertPoly p d = ((-1 : F) ^ k) • hilbertPoly q (d - k) := by
    exact round1_h16 F k d p q h13 h15

  have h18 : (hilbertPoly p d).natDegree = (hilbertPoly q (d - k)).natDegree := by
    rw [h16]
    have h17 : ((-1 : F) ^ k) ≠ 0 := by
      have h171 : (-1 : F) ≠ 0 := by norm_num
      have h172 : ∀ n : ℕ, (-1 : F) ^ n ≠ 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          simp [pow_succ, ih, h171]
          <;> aesop
      exact h172 k
    have h : (( (-1 : F) ^ k) • hilbertPoly q (d - k)).natDegree = (hilbertPoly q (d - k)).natDegree := by
      apply Polynomial.natDegree_smul
      exact h17
    simpa using h

  have h20 : d - k = m + 1 := by omega

  have h19 : (hilbertPoly p d).natDegree = (hilbertPoly q (m + 1)).natDegree := by
    have h201 : d - k = m + 1 := by omega
    rw [h18]
    rw [h201]
    <;> simp

  have h23 : (hilbertPoly q (m + 1)).coeff m ≠ 0 := by
    exact round1_h23 F m q hq2 hq'_ne_zero

  have h24 : ∀ n : ℕ, n > m → (hilbertPoly q (m + 1)).coeff n = 0 := by
    intro n hn
    have h241 : hilbertPoly q (m + 1) = ∑ i in q.support, (q.coeff i) • preHilbertPoly F m i := by
      simp [hilbertPoly]
      <;> aesop
    have h242 : (hilbertPoly q (m + 1)).coeff n = ∑ i in q.support, (q.coeff i) * (preHilbertPoly F m i).coeff n := by
      rw [h241]
      simp [Finset.sum_apply, coeff_smul]
      <;> ring
    have h243 : ∀ i ∈ q.support, (preHilbertPoly F m i).coeff n = 0 := by
      intro i _
      have h2431 : (preHilbertPoly F m i).natDegree = m := natDegree_preHilbertPoly F m i
      have h2432 : (preHilbertPoly F m i).coeff n = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [h2431]
        <;> linarith
      exact h2432
    have h244 : (hilbertPoly q (m + 1)).coeff n = 0 := by
      rw [h242]
      have h2441 : ∀ i ∈ q.support, (q.coeff i) * (preHilbertPoly F m i).coeff n = 0 := by
        intro i hi
        rw [h243 i hi]
        <;> ring
      have h2442 : ∑ i in q.support, (q.coeff i) * (preHilbertPoly F m i).coeff n = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact h2441 i hi
      simpa using h2442
    exact h244

  have h254 : (hilbertPoly q (m + 1)).natDegree = m := by
    exact round1_h254 F m q hq2 hq'_ne_zero h23 h24

  have h26 : (hilbertPoly p d).natDegree = m := by linarith [h19, h254]

  have h27 : m = d - k - 1 := by omega
  have h28 : (hilbertPoly p d).natDegree = d - k - 1 := by linarith
  have h29 : k = p.rootMultiplicity 1 := by simp [hk_def]
  rw [h28, h29]
  <;> omega
