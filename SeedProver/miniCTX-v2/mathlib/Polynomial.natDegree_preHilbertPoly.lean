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

/- Start of proof attempt -/
lemma round1_h3 (F : Type*) [Field F] (d k : ℕ) [CharZero F] :
  ((preHilbertPoly F d k)).natDegree = ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).natDegree := by
  have h1 : (d.factorial : F) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero d
  have h2 : (d.factorial : F)⁻¹ ≠ 0 := by
    field_simp [h1]
  simp only [preHilbertPoly]
  rw [Polynomial.natDegree_smul]
  <;> simp [h2]

lemma round1_h4 (F : Type*) [Field F] (d k : ℕ) :
  ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).natDegree = (ascPochhammer F d).natDegree * (Polynomial.X - (C (k : F)) + 1).natDegree := by
  apply Polynomial.natDegree_comp

lemma round1_h5 (F : Type*) [Field F] (d k : ℕ) :
  (ascPochhammer F d).natDegree = d := by
  simp [ascPochhammer]
  <;>
  aesop

lemma round1_h6 (F : Type*) [Field F] (d k : ℕ) :
  (Polynomial.X - (C (k : F)) + 1 : F[X]).natDegree = 1 := by
  have h11 : (Polynomial.X - (C (k : F)) + 1 : F[X]) = Polynomial.X + (1 - C (k : F)) := by
    ring
  rw [h11]
  have h12 : (1 - C (k : F) : F[X]).natDegree ≤ 0 := by
    simpa using Polynomial.natDegree_C (1 - (k : F))
  have h13 : (Polynomial.X : F[X]).natDegree = 1 := Polynomial.natDegree_X
  have h14 : (Polynomial.X : F[X]).natDegree > (1 - C (k : F) : F[X]).natDegree := by
    linarith
  rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt h14]
  <;> simp

theorem natDegree_preHilbertPoly [CharZero F] (d k : ℕ) :
    (preHilbertPoly F d k).natDegree = d  := by

  have h3 : ((preHilbertPoly F d k)).natDegree = ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).natDegree := by
    exact round1_h3 F d k
  have h4 : ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).natDegree = (ascPochhammer F d).natDegree * (Polynomial.X - (C (k : F)) + 1).natDegree := by
    exact round1_h4 F d k
  have h5 : (ascPochhammer F d).natDegree = d := by
    exact round1_h5 F d k
  have h6 : (Polynomial.X - (C (k : F)) + 1 : F[X]).natDegree = 1 := by
    exact round1_h6 F d k
  calc
    (preHilbertPoly F d k).natDegree = ((ascPochhammer F d).comp (Polynomial.X - (C (k : F)) + 1)).natDegree := by rw [h3]
    _ = (ascPochhammer F d).natDegree * (Polynomial.X - (C (k : F)) + 1).natDegree := by rw [h4]
    _ = d * 1 := by rw [h5, h6]
    _ = d := by simp
