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

/- Start of proof attempt -/
lemma round1_coeff_mul_invOneSubPow_succ {F : Type*} [Field F] [CharZero F] (p : F[X]) (d' n : ℕ) (hn : p.natDegree < n) :
    PowerSeries.coeff F n ((p : PowerSeries F) * PowerSeries.invOneSubPow F (d' + 1)) = ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) := by
  have h4 : PowerSeries.coeff F n ((p : PowerSeries F) * PowerSeries.invOneSubPow F (d' + 1)) = 
    ∑ p' in Finset.antidiagonal n, (PowerSeries.coeff F p'.1) (p : PowerSeries F) * (PowerSeries.coeff F p'.2) (PowerSeries.invOneSubPow F (d' + 1)) := by
    rw [PowerSeries.coeff_mul]
  have h5 : ∀ p' : ℕ × ℕ, p' ∈ Finset.antidiagonal n → (PowerSeries.coeff F p'.2) (PowerSeries.invOneSubPow F (d' + 1)) = ((d' + p'.2).choose d' : F) := by
    intro p' _
    have h51 : (PowerSeries.invOneSubPow F (d' + 1) : PowerSeries F) = PowerSeries.mk fun n => ((d' + n).choose d' : F) := PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose F d'
    have h52 : (PowerSeries.coeff F p'.2) (PowerSeries.invOneSubPow F (d' + 1)) = (PowerSeries.coeff F p'.2) (PowerSeries.mk fun n => ((d' + n).choose d' : F)) := by rw [h51]
    have h53 : (PowerSeries.coeff F p'.2) (PowerSeries.mk fun n => ((d' + n).choose d' : F)) = ((d' + p'.2).choose d' : F) := by simp [PowerSeries.coeff_mk]
    rw [h52, h53]
  have h6 : PowerSeries.coeff F n ((p : PowerSeries F) * PowerSeries.invOneSubPow F (d' + 1)) = ∑ p' in Finset.antidiagonal n, (p.coeff p'.1) * ((d' + p'.2).choose d' : F) := by
    rw [h4]
    apply Finset.sum_congr rfl
    intro p' hp'
    have h61 : (PowerSeries.coeff F p'.1) (p : PowerSeries F) = p.coeff p'.1 := by
      rw [Polynomial.coeff_coe]
    have h62 : (PowerSeries.coeff F p'.2) (PowerSeries.invOneSubPow F (d' + 1)) = ((d' + p'.2).choose d' : F) := h5 p' hp'
    rw [h61, h62]
  have h7 : ∀ p' ∈ Finset.antidiagonal n, (p.coeff p'.1) * ((d' + p'.2).choose d' : F) = (p.coeff p'.1) * ((n - p'.1 + d').choose d' : F) := by
    intro p' hp'
    have h71 : p'.1 + p'.2 = n := by simpa [Finset.mem_antidiagonal] using hp'
    have h72 : p'.2 = n - p'.1 := by omega
    have h73 : d' + p'.2 = n - p'.1 + d' := by omega
    have h74 : ((d' + p'.2).choose d' : F) = ((n - p'.1 + d').choose d' : F) := by
      rw [h73]
      <;> simp
    rw [h74]
  have h8 : ∑ p' in Finset.antidiagonal n, (p.coeff p'.1) * ((d' + p'.2).choose d' : F) = ∑ p' in Finset.antidiagonal n, (p.coeff p'.1) * ((n - p'.1 + d').choose d' : F) := by
    apply Finset.sum_congr rfl
    intro p' hp'
    exact h7 p' hp'
  have h9 : ∑ p' in Finset.antidiagonal n, (p.coeff p'.1) * ((n - p'.1 + d').choose d' : F) = ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) := by
    have h91 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun (p' : ℕ × ℕ) => (p.coeff p'.1) * ((n - p'.1 + d').choose d' : F)) n
    simpa using h91
  rw [h6, h8, h9]

lemma round1_hilbertPoly_eval_eq_sum {F : Type*} [Field F] [CharZero F] (p : F[X]) (d' n : ℕ) (hn : p.natDegree < n) :
    (hilbertPoly p (d' + 1)).eval (n : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) := by
  have h111 : hilbertPoly p (d' + 1) = ∑ i in p.support, (p.coeff i) • preHilbertPoly F d' i := rfl
  have h112 : (hilbertPoly p (d' + 1)).eval (n : F) = (∑ i in p.support, (p.coeff i) • preHilbertPoly F d' i).eval (n : F) := by rw [h111]
  have h113 : (∑ i in p.support, (p.coeff i) • preHilbertPoly F d' i).eval (n : F) = ∑ i in p.support, ((p.coeff i) • preHilbertPoly F d' i).eval (n : F) := by
    rw [Polynomial.eval_finset_sum]
  have h114 : ∀ i ∈ p.support, ((p.coeff i) • preHilbertPoly F d' i).eval (n : F) = (p.coeff i) * (preHilbertPoly F d' i).eval (n : F) := by
    intro i _
    rw [Polynomial.eval_smul]
    <;> simp
  have h115 : (∑ i in p.support, (p.coeff i) • preHilbertPoly F d' i).eval (n : F) = ∑ i in p.support, (p.coeff i) * (preHilbertPoly F d' i).eval (n : F) := by
    rw [h113]
    apply Finset.sum_congr rfl
    intro i hi
    exact h114 i hi
  have h116 : ∀ i ∈ p.support, (preHilbertPoly F d' i).eval (n : F) = ((n - i + d').choose d' : F) := by
    intro i hi
    have h1161 : i ≤ p.natDegree := by
      have h11611 : p.coeff i ≠ 0 := by
        have h11612 : i ∈ p.support := hi
        simp only [Polynomial.mem_support_iff] at h11612
        tauto
      exact?
    have h1162 : i ≤ n := by linarith
    exact preHilbertPoly_eq_choose_sub_add F d' h1162
  have h117 : ∑ i in p.support, (p.coeff i) * (preHilbertPoly F d' i).eval (n : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [h116 i hi]
    <;> ring
  rw [h112, h115, h117]

lemma round1_sum_range_eq_sum_support {F : Type*} [Field F] [CharZero F] (p : F[X]) (d' n : ℕ) (hn : p.natDegree < n) :
    ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) := by
  have h12 : p.support ⊆ Finset.range n.succ := by
    intro i hi
    have h121 : i ≤ p.natDegree := by
      have h1211 : p.coeff i ≠ 0 := by
        have h1212 : i ∈ p.support := hi
        simp only [Polynomial.mem_support_iff] at h1212
        tauto
      exact?
    have h122 : p.natDegree < n := hn
    have h123 : i ≤ n := by linarith
    simp [Finset.mem_range]
    <;> omega
  have h13 : ∀ i ∈ Finset.range n.succ, i ∉ p.support → (p.coeff i) * ((n - i + d').choose d' : F) = 0 := by
    intro i _ h131
    have h132 : p.coeff i = 0 := by
      by_contra h1321
      have h1322 : i ∈ p.support := by
        simp only [Polynomial.mem_support_iff]
        tauto
      contradiction
    rw [h132]
    <;> ring
  have h142 : ∀ i ∈ (Finset.range n.succ \ p.support), (p.coeff i) * ((n - i + d').choose d' : F) = 0 := by
    intro i hi
    have h1421 : i ∈ Finset.range n.succ := (Finset.mem_sdiff.mp hi).1
    have h1422 : i ∉ p.support := (Finset.mem_sdiff.mp hi).2
    exact h13 i h1421 h1422
  have h143 : ∑ i in (Finset.range n.succ \ p.support), (p.coeff i) * ((n - i + d').choose d' : F) = 0 := by
    apply Finset.sum_eq_zero
    exact h142
  have h1441 : Disjoint p.support (Finset.range n.succ \ p.support) := by
    apply Finset.disjoint_sdiff
  have h1442 : p.support ∪ (Finset.range n.succ \ p.support) = Finset.range n.succ := by
    apply Finset.union_sdiff_of_subset h12
  have h1443 : ∑ i in (p.support ∪ (Finset.range n.succ \ p.support)), (p.coeff i) * ((n - i + d').choose d' : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) + ∑ i in (Finset.range n.succ \ p.support), (p.coeff i) * ((n - i + d').choose d' : F) := by
    rw [Finset.sum_union h1441]
    <;> ring
  have h1444 : ∑ i in (p.support ∪ (Finset.range n.succ \ p.support)), (p.coeff i) * ((n - i + d').choose d' : F) = ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) := by
    rw [h1442]
  have h144 : ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) + ∑ i in (Finset.range n.succ \ p.support), (p.coeff i) * ((n - i + d').choose d' : F) := by
    rw [←h1444]
    exact h1443
  have h145 : ∑ i in (Finset.range n.succ \ p.support), (p.coeff i) * ((n - i + d').choose d' : F) = 0 := h143
  rw [h145] at h144
  rw [add_zero] at h144
  exact h144

/--
The key property of Hilbert polynomials. If `F` is a field with characteristic `0`, `p : F[X]` and
`d : ℕ`, then for any large enough `n : ℕ`, `(Polynomial.hilbertPoly p d).eval (n : F)` equals the
coefficient of `Xⁿ` in the power series expansion of `p/(1 - X)ᵈ`.
-/
theorem coeff_mul_invOneSubPow_eq_hilbertPoly_eval
    {p : F[X]} (d : ℕ) {n : ℕ} (hn : p.natDegree < n) :
    PowerSeries.coeff F n (p * invOneSubPow F d) = (hilbertPoly p d).eval (n : F)  := by

  by_cases h : d = 0
  · -- Case 1: d = 0
    subst h
    have h1 : PowerSeries.invOneSubPow F 0 = 1 := PowerSeries.invOneSubPow_zero F
    have h2 : (p : PowerSeries F) * PowerSeries.invOneSubPow F 0 = (p : PowerSeries F) := by
      rw [h1]
      <;> simp
    have h21 : PowerSeries.coeff F n ((p : PowerSeries F) * PowerSeries.invOneSubPow F 0) = PowerSeries.coeff F n (p : PowerSeries F) := by rw [h2]
    have h22 : PowerSeries.coeff F n (p : PowerSeries F) = p.coeff n := Polynomial.coeff_coe p n
    have h23 : p.coeff n = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hn
    have h3 : hilbertPoly p 0 = 0 := hilbertPoly_zero_right p
    have h31 : (hilbertPoly p 0).eval (n : F) = 0 := by
      rw [h3]
      simp
    simp only [h21, h22, h23, h31] at *
    <;> norm_num
  · -- Case 2: d ≠ 0
    have hpos : ∃ d', d = d' + 1 := by
      use d - 1
      omega
    rcases hpos with ⟨d', hd⟩
    subst hd
    have h10 : PowerSeries.coeff F n ((p : PowerSeries F) * PowerSeries.invOneSubPow F (d' + 1)) = ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) := by
      exact round1_coeff_mul_invOneSubPow_succ p d' n hn
    have h11 : (hilbertPoly p (d' + 1)).eval (n : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) := by
      exact round1_hilbertPoly_eval_eq_sum p d' n hn
    have h14 : ∑ i in Finset.range n.succ, (p.coeff i) * ((n - i + d').choose d' : F) = ∑ i in p.support, (p.coeff i) * ((n - i + d').choose d' : F) := by
      exact round1_sum_range_eq_sum_support p d' n hn
    simp_all [mul_comm]
    <;> aesop
