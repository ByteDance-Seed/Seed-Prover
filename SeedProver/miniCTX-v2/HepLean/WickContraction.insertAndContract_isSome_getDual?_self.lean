-- In HepLean/HepLean/PerturbationTheory/WickContraction/InsertAndContract.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.UncontractedList
/-!

# Inserting an element into a contraction based on a list

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

/-!

## Inserting an element into a list

-/

/-- Given a Wick contraction `φsΛ` for a list `φs` of `𝓕.FieldOp`,
  an element `φ` of `𝓕.FieldOp`, an `i ≤ φs.length` and a `j` which is either `none` or
  some element of `φsΛ.uncontracted`, the new Wick contraction
  `φsΛ.insertAndContract φ i j` is defined by inserting `φ` into `φs` after
  the first `i`-elements and moving the values representing the contracted pairs in `φsΛ`
  accordingly.
  If `j` is not `none`, but rather `some j`, to this contraction is added the contraction
  of `φ` (at position `i`) with the new position of `j` after `φ` is added.

  In other words, `φsΛ.insertAndContract φ i j` is formed by adding `φ` to `φs` at position `i`,
  and contracting `φ` with the field originally at position `j` if `j` is not none.
  It is a Wick contraction of `φs.insertIdx φ i`, the list `φs` with `φ` inserted at
  position `i`.

  The notation `φsΛ ↩Λ φ i j` is used to denote `φsΛ.insertAndContract φ i j`. -/
def insertAndContract {φs : List 𝓕.FieldOp} (φ : 𝓕.FieldOp) (φsΛ : WickContraction φs.length)
    (i : Fin φs.length.succ) (j : Option φsΛ.uncontracted) :
    WickContraction (φs.insertIdx i φ).length :=
  congr (by simp) (φsΛ.insertAndContractNat i j)

@[inherit_doc insertAndContract]
scoped[WickContraction] notation φs "↩Λ" φ:max i:max j => insertAndContract φ φs i j

@[simp]
lemma insertAndContract_fstFieldOfContract (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Option φsΛ.uncontracted)
    (a : φsΛ.1) : (φsΛ ↩Λ φ i j).fstFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i j a)) =
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove (φsΛ.fstFieldOfContract a)) := by
  simp [insertAndContract]

@[simp]
lemma insertAndContract_sndFieldOfContract (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : Option (φsΛ.uncontracted))
    (a : φsΛ.1) : (φsΛ ↩Λ φ i j).sndFieldOfContract
    (congrLift (insertIdx_length_fin φ φs i).symm (insertLift i j a)) =
    finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove (φsΛ.sndFieldOfContract a)) := by
  simp [insertAndContract]

@[simp]
lemma insertAndContract_fstFieldOfContract_some_incl (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
      (insertAndContract φ φsΛ i (some j)).fstFieldOfContract
      (congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩) =
      if i < i.succAbove j.1 then
      finCongr (insertIdx_length_fin φ φs i).symm i else
      finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j.1) := by
  split
  · rename_i h
    refine (insertAndContract φ φsΛ i (some j)).eq_fstFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm i) (j :=
        finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j)) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all
  · rename_i h
    refine (insertAndContract φ φsΛ i (some j)).eq_fstFieldOfContract_of_mem
      (a := congrLift (insertIdx_length_fin φ φs i).symm ⟨{i, i.succAbove j}, by
        simp [insertAndContractNat]⟩)
      (i := finCongr (insertIdx_length_fin φ φs i).symm (i.succAbove j))
      (j := finCongr (insertIdx_length_fin φ φs i).symm i) ?_ ?_ ?_
    · simp [congrLift]
    · simp [congrLift]
    · rw [Fin.lt_def] at h ⊢
      simp_all only [Nat.succ_eq_add_one, Fin.val_fin_lt, not_lt, finCongr_apply, Fin.coe_cast]
      have hi : i.succAbove j ≠ i := Fin.succAbove_ne i j
      omega

/-!

## insertAndContract and getDual?

-/

@[simp]
lemma insertAndContract_none_getDual?_self (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).getDual? (Fin.cast (insertIdx_length_fin φ φs i).symm i) = none := by
  simp only [Nat.succ_eq_add_one, insertAndContract, getDual?_congr, finCongr_apply, Fin.cast_trans,
    Fin.cast_eq_self, Option.map_eq_none']
  simp

/- Start of proof attempt -/
lemma round1_insertAndContract_isSome_getDual?_self (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual?
    (Fin.cast (insertIdx_length_fin φ φs i).symm i)).isSome := by
  by_cases h : i < i.succAbove j.1
  · -- Case 1: i < i.succAbove j.1
    simp [insertAndContract, getDual?_congr]
    <;>
    aesop
  · -- Case 2: ¬(i < i.succAbove j.1)
    simp [insertAndContract, getDual?_congr]
    <;>
    aesop

theorem insertAndContract_isSome_getDual?_self (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    ((φsΛ ↩Λ φ i (some j)).getDual?
    (Fin.cast (insertIdx_length_fin φ φs i).symm i)).isSome  := by

  exact round1_insertAndContract_isSome_getDual?_self φ φs φsΛ i j
