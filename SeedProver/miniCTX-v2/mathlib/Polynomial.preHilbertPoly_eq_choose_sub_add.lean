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

/- Start of proof attempt -/
lemma round1_preHilbertPoly_eq_choose_sub_add [CharZero F] (d : ℕ) {k n : ℕ} (hkn : k ≤ n):
    (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d := by
  have h1 : (preHilbertPoly F d k).eval (n : F) = (d.factorial : F)⁻¹ • ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).eval (n : F) := by
    simp [preHilbertPoly]
    <;> ring
  have h2 : ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).eval (n : F) = (ascPochhammer F d).eval ((Polynomial.X - (C (k : F)) + 1).eval (n : F)) := by
    rw [Polynomial.eval_comp]
  have h3 : (Polynomial.X - (C (k : F)) + 1).eval (n : F) = (n : F) - (k : F) + 1 := by
    simp [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    <;> ring
  have h4 : ∃ m : ℕ, n = k + m := by
    refine ⟨n - k,?_⟩
    omega
  obtain ⟨m, hm⟩ := h4
  have h51 : (n : F) = (k : F) + (m : F) := by
    have h511 : n = k + m := by omega
    norm_cast <;> simp [h511] <;> ring
  have h5 : (n : F) - (k : F) + 1 = ((m + 1 : ℕ) : F) := by
    have h51 : (n : F) = (k : F) + (m : F) := by
      exact_mod_cast hm
    rw [h51]
    simp [add_assoc]
    <;> ring
  have h6 : ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).eval (n : F) = (ascPochhammer F d).eval (((m + 1 : ℕ) : F)) := by
    rw [h2, h3]
    rw [h5]
    <;> simp
  have h7 : (ascPochhammer F d).eval (((m + 1 : ℕ) : F)) = (( (m + d).descFactorial d ) : F) := by
    have h73 : (ascPochhammer F d).eval (((m + 1 : ℕ) : F)) = ↑(( (m + 1) + d - 1).descFactorial d) := by
      have h731 := ascPochhammer_nat_eq_natCast_descFactorial F (m + 1) d
      simpa using h731
    have h71 : ( (m + 1) + d - 1 ) = m + d := by omega
    have h72 : (( (m + 1) + d - 1).descFactorial d) = ( (m + d).descFactorial d) := by rw [h71]
    rw [h73, h72]
    <;> simp
  have h8 : n - k + d = m + d := by omega
  have h9 : (n - k + d).descFactorial d = (m + d).descFactorial d := by
    rw [h8]
  have h10 : (( (m + d).descFactorial d ) : F) = (( (n - k + d).descFactorial d ) : F) := by
    rw [h9]
  have h6' : ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).eval (n : F) = (( (n - k + d).descFactorial d ) : F) := by
    have h61 : ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).eval (n : F) = (( (m + d).descFactorial d ) : F) := by
      rw [h6, h7]
    have h101 : (( (m + d).descFactorial d ) : F) = (( (n - k + d).descFactorial d ) : F) := by
      exact h10
    rw [h61, h101]
  have h13 : (d ! : F) ≠ 0 := by
    have h131 : d ! > 0 := Nat.factorial_pos d
    have h132 : (d ! : F) ≠ 0 := by
      exact_mod_cast Nat.not_eq_zero_of_lt h131
    exact h132
  have h11 : (n - k + d).descFactorial d = (n - k + d).choose d * d ! := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    <;> ring
  have h11' : (( (n - k + d).descFactorial d ) : F) = (( (n - k + d).choose d * d ! ) : F) := by
    rw [h11]
    <;> simp
  have h12 : (( (n - k + d).choose d * d ! ) : F) = (( (n - k + d).choose d ) : F) * ((d !) : F) := by
    simp [Nat.cast_mul]
    <;> ring
  have h6'' : ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).eval (n : F) = (( (n - k + d).choose d ) : F) * ((d !) : F) := by
    rw [h6', h11', h12]
  have h14 : (preHilbertPoly F d k).eval (n : F) = (( (n - k + d).choose d ) : F) := by
    rw [h1, h6'']
    field_simp [h13]
    <;> ring
  have h15 : (preHilbertPoly F d k).eval (n : F) = (( (n - k + d).choose d ) : F) := h14
  norm_cast at h15 ⊢
  <;> simpa using h15

theorem preHilbertPoly_eq_choose_sub_add [CharZero F] (d : ℕ) {k n : ℕ} (hkn : k ≤ n):
    (preHilbertPoly F d k).eval (n : F) = (n - k + d).choose d  := by

  exact round1_preHilbertPoly_eq_choose_sub_add F d hkn
