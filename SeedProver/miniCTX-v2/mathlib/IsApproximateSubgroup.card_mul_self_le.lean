-- In mathlib/Mathlib/Combinatorics/Additive/ApproximateSubgroup.lean

/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Combinatorics.Additive.CovBySMul
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Additive.SmallTripling

/-!
# Approximate subgroups

This file defines approximate subgroups of a group, namely symmetric sets `A` such that `A * A` can
be covered by a small number of translates of `A`.

## Main results

Approximate subgroups are a central concept in additive combinatorics, as a natural weakening and
flexible substitute of genuine subgroups. As such, they share numerous properties with subgroups:
* `IsApproximateSubgroup.image`: Group homomorphisms send approximate subgroups to approximate
  subgroups
* `IsApproximateSubgroup.pow_inter_pow`: The intersection of (non-trivial powers of) two approximate
  subgroups is an approximate subgroup. Warning: The intersection of two approximate subgroups isn't
  an approximate subgroup in general.

Approximate subgroups are close qualitatively and quantitatively to other concepts in additive
combinatorics:
* `IsApproximateSubgroup.card_pow_le`: An approximate subgroup has small powers.
* `IsApproximateSubgroup.of_small_tripling`: A set of small tripling can be made an approximate
  subgroup by squaring.

It can be readily confirmed that approximate subgroups are a weakening of subgroups:
* `isApproximateSubgroup_one`: A 1-approximate subgroup is the same thing as a subgroup.
-/

open scoped Finset Pointwise

variable {G : Type*} [Group G] {A B : Set G} {K L : ℝ} {m n : ℕ}

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A + A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
structure IsApproximateAddSubgroup {G : Type*} [AddGroup G] (K : ℝ) (A : Set G) : Prop where
  zero_mem : 0 ∈ A
  neg_eq_self : -A = A
  two_nsmul_covByVAdd : CovByVAdd G K (2 • A) A

/--
An approximate subgroup in a group is a symmetric set `A` containing the identity and such that
`A * A` can be covered by a small number of translates of `A`.

In practice, we will take `K` fixed and `A` large but finite.
-/
@[to_additive]
structure IsApproximateSubgroup (K : ℝ) (A : Set G) : Prop where
  one_mem : 1 ∈ A
  inv_eq_self : A⁻¹ = A
  sq_covBySMul : CovBySMul G K (A ^ 2) A

namespace IsApproximateSubgroup

@[to_additive] lemma nonempty (hA : IsApproximateSubgroup K A) : A.Nonempty := ⟨1, hA.one_mem⟩

@[to_additive one_le]
lemma one_le (hA : IsApproximateSubgroup K A) : 1 ≤ K := by
  obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
  have hF₀ : F ≠ ∅ := by rintro rfl; simp [hA.nonempty.pow.ne_empty] at hSF
  exact hF.trans' <| by simpa [Finset.nonempty_iff_ne_empty]

@[to_additive]
lemma mono (hKL : K ≤ L) (hA : IsApproximateSubgroup K A) : IsApproximateSubgroup L A where
  one_mem := hA.one_mem
  inv_eq_self := hA.inv_eq_self
  sq_covBySMul := hA.sq_covBySMul.mono hKL

@[to_additive]
lemma card_pow_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    ∀ {n}, #(A ^ n) ≤ K ^ (n - 1) * #A
  | 0 => by simpa using hA.nonempty
  | 1 => by simp
  | n + 2 => by
    obtain ⟨F, hF, hSF⟩ := hA.sq_covBySMul
    calc
      (#(A ^ (n + 2)) : ℝ) ≤ #(F ^ (n + 1) * A) := by
        gcongr; exact mod_cast Set.pow_subset_pow_mul_of_sq_subset_mul hSF (by omega)
      _ ≤ #(F ^ (n + 1)) * #A := mod_cast Finset.card_mul_le
      _ ≤ #F ^ (n + 1) * #A := by gcongr; exact mod_cast Finset.card_pow_le
      _ ≤ K ^ (n + 1) * #A := by gcongr

/- Start of proof attempt -/
lemma round1_card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    (#(A * A) : ℝ) ≤ K * (#A : ℝ) := by
  obtain ⟨F, hF1, hF2⟩ := hA.sq_covBySMul
  have h113 : (F : Set G) • (A : Set G) = (F * A : Set G) := by
    ext x
    simp [Set.mem_smul_set, Set.mem_mul]
    <;> aesop
  have h114 : (A : Set G) ^ 2 ⊆ (F * A : Set G) := by
    rw [h113] at hF2
    exact hF2
  have h111 : (A : Set G) ^ 2 = (A : Set G) * (A : Set G) := by
    simp [pow_two]
  have h115 : (A : Set G) * (A : Set G) ⊆ (F * A : Set G) := by
    rw [h111] at h114
    exact h114
  have h12 : A * A ⊆ F * A := by
    intro x hx
    have h122 : (x : G) ∈ (A : Set G) * (A : Set G) := by exact_mod_cast hx
    have h123 : (x : G) ∈ (F * A : Set G) := h115 h122
    exact_mod_cast h123
  have h13 : #(A * A) ≤ #(F * A) := Finset.card_le_card h12
  have h14 : #(F * A) ≤ #F * #A := Finset.card_mul_le
  have h131 : #(A * A) ≤ #F * #A := by linarith
  have h17 : (#F : ℝ) ≤ K := by exact_mod_cast hF1
  have h18 : (#A : ℝ) ≥ 0 := by positivity
  have h19 : (#F : ℝ) * (#A : ℝ) ≤ K * (#A : ℝ) := by
    have h191 : (#F : ℝ) ≤ K := h17
    have h192 : (#A : ℝ) ≥ 0 := h18
    have h : (#F : ℝ) * (#A : ℝ) ≤ K * (#A : ℝ) := by
      nlinarith
    exact h
  have h20 : (#(A * A) : ℝ) ≤ (#F : ℝ) * (#A : ℝ) := by
    exact_mod_cast h131
  linarith

theorem card_mul_self_le [DecidableEq G] {A : Finset G} (hA : IsApproximateSubgroup K (A : Set G)) :
    #(A * A) ≤ K * #A  := by

  have h1 := round1_card_mul_self_le hA
  norm_cast at h1 ⊢
  <;> linarith
