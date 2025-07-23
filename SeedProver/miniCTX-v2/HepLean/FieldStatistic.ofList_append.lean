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

@[simp]
lemma bosonic_neq_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a := by
  fin_cases a
  · simp
  · simp

@[simp]
lemma fermionic_neq_iff_bosonic_eq (a : FieldStatistic) : ¬ fermionic = a ↔ bosonic = a := by
  fin_cases a
  · simp
  · simp

lemma eq_self_if_eq_bosonic {a : FieldStatistic} :
    (if a = bosonic then bosonic else fermionic) = a := by
  fin_cases a <;> rfl

lemma eq_self_if_bosonic_eq {a : FieldStatistic} :
    (if bosonic = a then bosonic else fermionic) = a := by
  fin_cases a <;> rfl

lemma mul_eq_one_iff (a b : FieldStatistic) : a * b = 1 ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp

lemma one_eq_mul_iff (a b : FieldStatistic) : 1 = a * b ↔ a = b := by
  fin_cases a <;> fin_cases b <;> simp

lemma mul_eq_iff_eq_mul (a b c : FieldStatistic) : a * b = c ↔ a = b * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [bosonic_mul_fermionic, fermionic_not_eq_bonsic, mul_self,
      reduceCtorEq, fermionic_mul_bosonic, true_iff, iff_true]
  all_goals rfl

lemma mul_eq_iff_eq_mul' (a b c : FieldStatistic) : a * b = c ↔ b = a * c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp only [bosonic_mul_fermionic, fermionic_not_eq_bonsic, mul_self,
      reduceCtorEq, fermionic_mul_bosonic, true_iff, iff_true]
  all_goals rfl

/-- The field statistics of a list of fields is fermionic if there is an odd number of fermions,
  otherwise it is bosonic. -/
def ofList (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) → FieldStatistic
  | [] => bosonic
  | φ :: φs => if s φ = ofList s φs then bosonic else fermionic

lemma ofList_cons_eq_mul (s : 𝓕 → FieldStatistic) (φ : 𝓕) (φs : List 𝓕) :
    ofList s (φ :: φs) = s φ * ofList s φs := by
  have ha (a b : FieldStatistic) : (if a = b then bosonic else fermionic) = a * b := by
    fin_cases a <;> fin_cases b <;> rfl
  exact ha (s φ) (ofList s φs)

lemma ofList_eq_prod (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) →
    ofList s φs = (List.map s φs).prod
  | [] => rfl
  | φ :: φs => by
    rw [ofList_cons_eq_mul, List.map_cons, List.prod_cons, ofList_eq_prod]

@[simp]
lemma ofList_singleton (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s [φ] = s φ := by
  simp only [ofList, Fin.isValue]
  rw [eq_self_if_eq_bosonic]

@[simp]
lemma ofList_freeMonoid (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s (FreeMonoid.of φ) = s φ :=
  ofList_singleton s φ

@[simp]
lemma ofList_empty (s : 𝓕 → FieldStatistic) : ofList s [] = bosonic := rfl

/- Start of proof attempt -/
lemma round1_h6 (s : 𝓕 → FieldStatistic)
  (φs φs' : List 𝓕):
  ofList s (φs ++ φs') = (ofList s φs) * (ofList s φs') := by
  have h1 : ofList s (φs ++ φs') = (List.map s (φs ++ φs')).prod := by
    exact ofList_eq_prod s (φs ++ φs')
  have h2 : List.map s (φs ++ φs') = List.map s φs ++ List.map s φs' := by
    simp [List.map_append]
  have h3 : (List.map s (φs ++ φs')).prod = (List.map s φs).prod * (List.map s φs').prod := by
    rw [h2]
    simp [List.prod_append]
  have h4 : (List.map s φs).prod = ofList s φs := by
    have h41 : ofList s φs = (List.map s φs).prod := by
      exact (ofList_eq_prod s φs)
    rw [h41]
    <;> rfl
  have h5 : (List.map s φs').prod = ofList s φs' := by
    have h51 : ofList s φs' = (List.map s φs').prod := by
      exact (ofList_eq_prod s φs')
    rw [h51]
    <;> rfl
  rw [h1, h3, h4, h5]
  <;> rfl

lemma round1_h7 :
  ∀ (a b : FieldStatistic), a * b = if a = b then bosonic else fermionic := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [bosonic_mul_bosonic, bosonic_mul_fermionic, fermionic_mul_bosonic, fermionic_mul_fermionic]
  <;> aesop

theorem ofList_append (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = if ofList s φs = ofList s φs' then bosonic else fermionic  := by

  have h6 : ofList s (φs ++ φs') = (ofList s φs) * (ofList s φs') := by
    exact round1_h6 s φs φs'
  have h7 : ∀ (a b : FieldStatistic), a * b = if a = b then bosonic else fermionic := by
    exact round1_h7
  have h9 : (ofList s φs) * (ofList s φs') = if ofList s φs = ofList s φs' then bosonic else fermionic := by
    exact h7 (ofList s φs) (ofList s φs')
  rw [h6, h9]
  <;> aesop
