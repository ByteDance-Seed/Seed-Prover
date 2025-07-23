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

/- Start of proof attempt -/
lemma round1_hilbertPoly_unique (F : Type*) [Field F] [CharZero F] (p : F[X]) (d : ℕ)
    (h' : F[X]) (h_property : ∃ N : ℕ, ∀ n > N, PowerSeries.coeff F n (p * invOneSubPow F d) = h'.eval (n : F)) :
    h' = hilbertPoly p d := by
  rcases h_property with ⟨N, hN⟩
  have h2 : ∀ n > p.natDegree, PowerSeries.coeff F n (p * invOneSubPow F d) = (hilbertPoly p d).eval (n : F) := by
    intro n hn
    exact coeff_mul_invOneSubPow_eq_hilbertPoly_eval d (by linarith)
  have h3 : ∀ n : ℕ, n > max N p.natDegree → (h' - hilbertPoly p d).eval (n : F) = 0 := by
    intro n hn
    have h4 : n > N := by
      have h41 : N ≤ max N p.natDegree := le_max_left N p.natDegree
      linarith
    have h5 : n > p.natDegree := by
      have h51 : p.natDegree ≤ max N p.natDegree := le_max_right N p.natDegree
      linarith
    have h6 : PowerSeries.coeff F n (p * invOneSubPow F d) = h'.eval (n : F) := hN n h4
    have h7 : PowerSeries.coeff F n (p * invOneSubPow F d) = (hilbertPoly p d).eval (n : F) := h2 n h5
    have h8 : h'.eval (n : F) = (hilbertPoly p d).eval (n : F) := by
      have h6' : h'.eval (n : F) = PowerSeries.coeff F n (p * invOneSubPow F d) := by rw [h6]
      have h7' : (hilbertPoly p d).eval (n : F) = PowerSeries.coeff F n (p * invOneSubPow F d) := by rw [h7]
      rw [h6', h7']
    simp [h8, sub_eq_zero]
    <;> aesop
  by_cases hq : h' - hilbertPoly p d = 0
  · -- Case 1: h' - hilbertPoly p d = 0
    have h9 : h' = hilbertPoly p d := by simpa using sub_eq_zero.mp hq
    exact h9
  · -- Case 2: h' - hilbertPoly p d ≠ 0
    have h4 : ∀ k : ℕ, (h' - hilbertPoly p d).eval ((max N p.natDegree + k + 1 : ℕ) : F) = 0 := by
      intro k
      have h5 : (max N p.natDegree + k + 1 : ℕ) > max N p.natDegree := by
        linarith
      exact h3 (max N p.natDegree + k + 1) h5
    have h6 : ∀ k : ℕ, ((max N p.natDegree + k + 1 : ℕ) : F) ∈ (h' - hilbertPoly p d).rootSet F := by
      intro k
      simp only [Polynomial.mem_rootSet, h4 k, hq, ne_eq, not_false_eq_true]
      <;> aesop
    have h7 : Function.Injective (fun k : ℕ => ((max N p.natDegree + k + 1 : ℕ) : F)) := by
      intro k1 k2 h
      simp at h
      <;> norm_cast at h <;> linarith
    have h8 : Set.Infinite (Set.range (fun k : ℕ => ((max N p.natDegree + k + 1 : ℕ) : F))) := by
      apply Set.infinite_range_of_injective h7
    have h9 : Set.range (fun k : ℕ => ((max N p.natDegree + k + 1 : ℕ) : F)) ⊆ (h' - hilbertPoly p d).rootSet F := by
      intro x hx
      rcases hx with ⟨k, rfl⟩
      exact h6 k
    have h10 : Set.Infinite ((h' - hilbertPoly p d).rootSet F) := by
      apply Set.Infinite.mono h9 h8
    have h11 : Set.Finite ((h' - hilbertPoly p d).rootSet F) := by
      exact?
    contradiction

/--
The polynomial satisfying the key property of `Polynomial.hilbertPoly p d` is unique.
-/
theorem existsUnique_hilbertPoly (p : F[X]) (d : ℕ) :
    ∃! h : F[X], ∃ N : ℕ, ∀ n > N,
    PowerSeries.coeff F n (p * invOneSubPow F d) = h.eval (n : F)  := by

  use hilbertPoly p d
  constructor
  · -- We need to prove ∃ N : ℕ, ∀ n > N, PowerSeries.coeff F n (p * invOneSubPow F d) = (hilbertPoly p d).eval (n : F)
    use p.natDegree
    intro n hn
    exact coeff_mul_invOneSubPow_eq_hilbertPoly_eval d (by linarith)
  · -- We need to prove ∀ (h' : F[X]), (∃ N : ℕ, ∀ n > N, PowerSeries.coeff F n (p * invOneSubPow F d) = h'.eval (n : F)) → h' = hilbertPoly p d
    intro h' h'_property
    exact round1_hilbertPoly_unique F p d h' h'_property
