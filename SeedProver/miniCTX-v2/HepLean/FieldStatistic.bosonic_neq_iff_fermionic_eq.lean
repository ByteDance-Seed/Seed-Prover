-- In HepLean/HepLean/PerturbationTheory/FieldStatistics/Basic.lean

/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
import HepLean.Mathematics.List.InsertIdx
/-!

# Field statistics

Basic properties related to whether a field, or list of fields, is bosonic or fermionic.

-/

/-- The type `FieldStatistic` is the type containing two elements `bosonic` and `fermionic`.
  This type is used to specify if a field or operator obeys bosonic or fermionic statistics. -/
inductive FieldStatistic : Type where
  | bosonic : FieldStatistic
  | fermionic : FieldStatistic
deriving DecidableEq

namespace FieldStatistic

variable {𝓕 : Type}

/-- The type `FieldStatistic` carries an instance of a commutative group in which
- `bosonic * bosonic = bosonic`
- `bosonic * fermionic = fermionic`
- `fermionic * bosonic = fermionic`
- `fermionic * fermionic = bosonic`

This group is isomorphic to `ℤ₂`. -/
@[simp]
instance : CommGroup FieldStatistic where
  one := bosonic
  mul a b :=
    match a, b with
    | bosonic, bosonic => bosonic
    | bosonic, fermionic => fermionic
    | fermionic, bosonic => fermionic
    | fermionic, fermionic => bosonic
  inv a := a
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;>
    dsimp [HMul.hMul]
  one_mul a := by
    cases a <;> dsimp [HMul.hMul]
  mul_one a := by
    cases a <;> dsimp [HMul.hMul]
  inv_mul_cancel a := by
    cases a <;> dsimp only [HMul.hMul, Nat.succ_eq_add_one] <;> rfl
  mul_comm a b := by
    cases a <;> cases b <;> rfl

@[simp]
lemma bosonic_mul_bosonic : bosonic * bosonic = bosonic := rfl

@[simp]
lemma bosonic_mul_fermionic : bosonic * fermionic = fermionic := rfl

@[simp]
lemma fermionic_mul_bosonic : fermionic * bosonic = fermionic := rfl

@[simp]
lemma fermionic_mul_fermionic : fermionic * fermionic = bosonic := rfl

@[simp]
lemma mul_bosonic (a : FieldStatistic) : a * bosonic = a := by
  cases a <;> rfl

@[simp]
lemma mul_self (a : FieldStatistic) : a * a = 1 := by
  cases a <;> rfl

/-- Field statics form a finite type. -/
instance : Fintype FieldStatistic where
  elems := {bosonic, fermionic}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self bosonic {fermionic}
    · refine Finset.insert_eq_self.mp ?_
      exact rfl

@[simp]
lemma fermionic_not_eq_bonsic : ¬ fermionic = bosonic := by
  intro h
  exact FieldStatistic.noConfusion h

lemma bonsic_eq_fermionic_false : bosonic = fermionic ↔ false := by
  simp only [reduceCtorEq, Bool.false_eq_true]

@[simp]
lemma neq_fermionic_iff_eq_bosonic (a : FieldStatistic) : ¬ a = fermionic ↔ a = bosonic := by
  fin_cases a
  · simp
  · simp

@[simp]
lemma neq_bosonic_iff_eq_fermionic (a : FieldStatistic) : ¬ a = bosonic ↔ a = fermionic := by
  fin_cases a
  · simp
  · simp

/- Start of proof attempt -/
lemma round1_bosonic_neq_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a := by
  cases a <;> simp

theorem bosonic_neq_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a  := by

  exact round1_bosonic_neq_iff_fermionic_eq a
