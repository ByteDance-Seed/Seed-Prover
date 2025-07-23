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

/- Start of proof attempt -/
lemma round1_bosonic_mul_bosonic : FieldStatistic.bosonic * FieldStatistic.bosonic = FieldStatistic.bosonic := by
  rfl

theorem bosonic_mul_bosonic : bosonic * bosonic = bosonic  := by

  exact round1_bosonic_mul_bosonic
