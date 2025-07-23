-- In HepLean/HepLean/PerturbationTheory/WickContraction/TimeCond.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Join
/-!

# Time contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

/-- The condition on a Wick contraction which is true iff and only if every contraction
  is between two fields of equal time. -/
def EqTimeOnly {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : Prop :=
  ∀ (i j), {i, j} ∈ φsΛ.1 → timeOrderRel φs[i] φs[j]
noncomputable section

instance {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    Decidable (EqTimeOnly φsΛ) :=
    inferInstanceAs (Decidable (∀ (i j), {i, j} ∈ φsΛ.1 → timeOrderRel φs[i] φs[j]))

namespace EqTimeOnly
variable {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)

lemma timeOrderRel_of_eqTimeOnly_pair {i j : Fin φs.length} (h : {i, j} ∈ φsΛ.1)
    (hc : EqTimeOnly φsΛ) :
    timeOrderRel φs[i] φs[j] := by
  have h' := hc
  simp only [EqTimeOnly, ne_eq, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
    true_and] at h'
  exact h' i j h

lemma timeOrderRel_both_of_eqTimeOnly {i j : Fin φs.length} (h : {i, j} ∈ φsΛ.1)
    (hc : EqTimeOnly φsΛ) :
    timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i] := by
  apply And.intro
  · exact timeOrderRel_of_eqTimeOnly_pair φsΛ h hc
  · apply timeOrderRel_of_eqTimeOnly_pair φsΛ _ hc
    rw [@Finset.pair_comm]
    exact h

lemma eqTimeOnly_iff_forall_finset {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    φsΛ.EqTimeOnly ↔ ∀ (a : φsΛ.1),
      timeOrderRel (φs[φsΛ.fstFieldOfContract a]) (φs[φsΛ.sndFieldOfContract a])
      ∧ timeOrderRel (φs[φsΛ.sndFieldOfContract a]) (φs[φsΛ.fstFieldOfContract a]) := by
  apply Iff.intro
  · intro h a
    apply timeOrderRel_both_of_eqTimeOnly φsΛ _ h
    rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
    simp
  · intro h
    simp only [EqTimeOnly, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
      true_and]
    intro i j h1
    have h' := h ⟨{i, j}, h1⟩
    by_cases hij: i < j
    · have hi : φsΛ.fstFieldOfContract ⟨{i, j}, h1⟩ = i := by
        apply eq_fstFieldOfContract_of_mem _ _ i j
        · simp
        · simp
        · exact hij
      have hj : φsΛ.sndFieldOfContract ⟨{i, j}, h1⟩ = j := by
        apply eq_sndFieldOfContract_of_mem _ _ i j
        · simp
        · simp
        · exact hij
      simp_all
    · have hij : i ≠ j := by
        by_contra hij
        subst hij
        have h2 := φsΛ.2.1 {i, i} h1
        simp at h2
      have hj : φsΛ.fstFieldOfContract ⟨{i, j}, h1⟩ = j := by
        apply eq_fstFieldOfContract_of_mem _ _ j i
        · simp
        · simp
        · omega
      have hi : φsΛ.sndFieldOfContract ⟨{i, j}, h1⟩ = i := by
        apply eq_sndFieldOfContract_of_mem _ _ j i
        · simp
        · simp
        · omega
      simp_all

@[simp]
lemma empty_mem {φs : List 𝓕.FieldOp} : empty (n := φs.length).EqTimeOnly := by
  rw [eqTimeOnly_iff_forall_finset]
  simp [empty]

/-- Let `φs` be a list of `𝓕.FieldOp` and `φsΛ` a `WickContraction` of `φs` with
  in which every contraction involves two `𝓕FieldOp`s that have the same time, then
  `φsΛ.staticContract = φsΛ.timeContract`. -/
lemma staticContract_eq_timeContract_of_eqTimeOnly (h : φsΛ.EqTimeOnly) :
    φsΛ.staticContract = φsΛ.timeContract := by
  simp only [staticContract, timeContract]
  apply congrArg
  funext a
  ext
  simp only [List.get_eq_getElem]
  rw [timeContract_of_timeOrderRel]
  apply timeOrderRel_of_eqTimeOnly_pair φsΛ
  rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2
  exact h

lemma eqTimeOnly_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (φsΛ : WickContraction φs.length) :
    (congr (by simp [h]) φsΛ).EqTimeOnly (φs := φs') ↔ φsΛ.EqTimeOnly := by
  subst h
  simp

lemma quotContraction_eqTimeOnly {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (h : φsΛ.EqTimeOnly) (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    (φsΛ.quotContraction S ha).EqTimeOnly := by
  rw [eqTimeOnly_iff_forall_finset]
  intro a
  simp only [Fin.getElem_fin]
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp only [quotContraction_fstFieldOfContract_uncontractedListEmd, Fin.getElem_fin,
    quotContraction_sndFieldOfContract_uncontractedListEmd]
  rw [eqTimeOnly_iff_forall_finset] at h
  apply h

lemma exists_join_singleton_of_card_ge_zero {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) (h1 : φsΛ.EqTimeOnly) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i])
    ∧ φsucΛ.EqTimeOnly ∧ φsucΛ.1.card + 1 = φsΛ.1.card := by
  obtain ⟨a, ha⟩ := exists_contraction_pair_of_card_ge_zero φsΛ h
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
    WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
    congr (by simp [← subContraction_singleton_eq_singleton])
    (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp only [Fin.getElem_fin]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp only [id_eq, eq_mpr_eq_cast, h1, congr_trans_apply, congr_refl, φsucΛ]
    rw [join_sub_quot]
  · apply And.intro
    · apply timeOrderRel_both_of_eqTimeOnly φsΛ _ h1
      rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
      simp [ha]
    apply And.intro
    · simp only [id_eq, eq_mpr_eq_cast, φsucΛ]
      rw [eqTimeOnly_congr (φs := [(φsΛ.subContraction {a} (by simpa using ha))]ᵘᶜ)]
      simp only [id_eq, eq_mpr_eq_cast]
      exact quotContraction_eqTimeOnly h1 _ _
      rw [← subContraction_singleton_eq_singleton]
    · simp only [id_eq, eq_mpr_eq_cast, card_congr, φsucΛ]
      have h1 := subContraction_card_plus_quotContraction_card_eq _ {a} (by simpa using ha)
      simp only [subContraction, Finset.card_singleton, id_eq, eq_mpr_eq_cast] at h1
      omega

lemma timeOrder_timeContract_mul_of_eqTimeOnly_mid_induction {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : φsΛ.EqTimeOnly) (a b: 𝓕.FieldOpAlgebra) : (n : ℕ) → (hn : φsΛ.1.card = n) →
    𝓣(a * φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(a * b)
  | 0, hn => by
    rw [@card_zero_iff_empty] at hn
    subst hn
    simp
  | Nat.succ n, hn => by
    obtain ⟨i, j, hij, φsucΛ, rfl, h2, h3, h4⟩ :=
      exists_join_singleton_of_card_ge_zero φsΛ (by simp [hn]) hl
    rw [join_timeContract]
    rw [singleton_timeContract]
    simp only [Fin.getElem_fin, MulMemClass.coe_mul]
    trans timeOrder (a * FieldOpAlgebra.timeContract φs[↑i] φs[↑j] * (φsucΛ.timeContract.1 * b))
    simp only [mul_assoc, Fin.getElem_fin]
    rw [timeOrder_timeContract_eq_time_mid]
    have ih := timeOrder_timeContract_mul_of_eqTimeOnly_mid_induction φsucΛ h3 a b n (by omega)
    rw [← mul_assoc, ih]
    simp only [Fin.getElem_fin, mul_assoc]
    simp_all only [Nat.succ_eq_add_one, Fin.getElem_fin, add_left_inj]
    simp_all

lemma timeOrder_timeContract_mul_of_eqTimeOnly_mid {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : φsΛ.EqTimeOnly) (a b : 𝓕.FieldOpAlgebra) :
    𝓣(a * φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(a * b) := by
  exact timeOrder_timeContract_mul_of_eqTimeOnly_mid_induction φsΛ hl a b φsΛ.1.card rfl

/-- Let `φs` be a list of `𝓕.FieldOp`, `φsΛ` a `WickContraction` of `φs` with
  in which every contraction involves two `𝓕.FieldOp`s that have the same time and
  `b` a general element in `𝓕.FieldOpAlgebra`. Then
  `𝓣(φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(b)`.

  This follows from properties of orderings and the ideal defining `𝓕.FieldOpAlgebra`. -/
lemma timeOrder_timeContract_mul_of_eqTimeOnly_left {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : φsΛ.EqTimeOnly) (b : 𝓕.FieldOpAlgebra) :
    𝓣(φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(b) := by
  trans 𝓣(1 * φsΛ.timeContract.1 * b)
  simp only [one_mul]
  rw [timeOrder_timeContract_mul_of_eqTimeOnly_mid φsΛ hl]
  simp

lemma exists_join_singleton_of_not_eqTimeOnly {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (h1 : ¬ φsΛ.EqTimeOnly) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (¬ timeOrderRel φs[i] φs[j] ∨ ¬ timeOrderRel φs[j] φs[i]) := by
  rw [eqTimeOnly_iff_forall_finset] at h1
  simp only [Fin.getElem_fin, Subtype.forall, not_forall, not_and] at h1
  obtain ⟨a, ha, hr⟩ := h1
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
    WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
    congr (by simp [← subContraction_singleton_eq_singleton])
      (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp only [Fin.getElem_fin]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp only [id_eq, eq_mpr_eq_cast, h1, congr_trans_apply, congr_refl, φsucΛ]
    rw [join_sub_quot]
  · by_cases h1 : timeOrderRel φs[↑(φsΛ.fstFieldOfContract ⟨a, ha⟩)]
      φs[↑(φsΛ.sndFieldOfContract ⟨a, ha⟩)]
    · simp_all [h1]
    · simp_all [h1]

lemma timeOrder_timeContract_of_not_eqTimeOnly {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length)
    (hl : ¬ φsΛ.EqTimeOnly) : 𝓣(φsΛ.timeContract.1) = 0 := by
  obtain ⟨i, j, hij, φsucΛ, rfl, hr⟩ := exists_join_singleton_of_not_eqTimeOnly φsΛ hl
  rw [join_timeContract]
  rw [singleton_timeContract]
  simp only [Fin.getElem_fin, MulMemClass.coe_mul]
  rw [timeOrder_timeOrder_left]
  rw [timeOrder_timeContract_neq_time]
  simp only [zero_mul, map_zero]
  simp_all only [Fin.getElem_fin, not_and]
  intro h
  simp_all

/-- Let `φs` be a list of `𝓕.FieldOp` and `φsΛ` a `WickContraction` with
  at least one contraction between `𝓕.FieldOp` that do not have the same time. Then
  `𝓣(φsΛ.staticContract.1) = 0`. -/
lemma timeOrder_staticContract_of_not_mem {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (hl : ¬ φsΛ.EqTimeOnly) : 𝓣(φsΛ.staticContract.1) = 0 := by
  obtain ⟨i, j, hij, φsucΛ, rfl, hr⟩ := exists_join_singleton_of_not_eqTimeOnly φsΛ hl
  rw [join_staticContract]
  simp only [MulMemClass.coe_mul]
  rw [singleton_staticContract]
  rw [timeOrder_timeOrder_left]
  rw [timeOrder_superCommute_anPart_ofFieldOp_neq_time]
  simp only [zero_mul, map_zero]
  intro h
  simp_all

end EqTimeOnly

/-- The condition on a Wick contraction which is true if it has at least one contraction
  which is between two equal time fields. -/
def HaveEqTime {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : Prop :=
  ∃ (i j : Fin φs.length) (h : {i, j} ∈ φsΛ.1),
  timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]

noncomputable instance {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    Decidable (HaveEqTime φsΛ) :=
  inferInstanceAs (Decidable (∃ (i j : Fin φs.length)
    (h : ({i, j} : Finset (Fin φs.length)) ∈ φsΛ.1),
    timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]))

lemma haveEqTime_iff_finset {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    HaveEqTime φsΛ ↔ ∃ (a : Finset (Fin φs.length)) (h : a ∈ φsΛ.1),
      timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩]
    ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := by
  simp only [HaveEqTime, Fin.getElem_fin, exists_and_left, exists_prop]
  apply Iff.intro
  · intro h
    obtain ⟨i, j, hij, h1, h2⟩ := h
    use {i, j}, h1
    by_cases hij : i < j
    · have h1n := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ i j (by simp) (by simp) hij
      have h2n := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ i j (by simp) (by simp) hij
      simp only [h1n, h2n]
      simp_all only [forall_true_left, true_and]
    · have hineqj : i ≠ j := by
        by_contra hineqj
        subst hineqj
        have h2 := φsΛ.2.1 {i, i} h1
        simp_all
      have hji : j < i := by omega
      have h1n := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ j i (by simp) (by simp) hji
      have h2n := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ j i (by simp) (by simp) hji
      simp only [h1n, h2n]
      simp_all
  · intro h
    obtain ⟨a, h1, h2, h3⟩ := h
    use φsΛ.fstFieldOfContract ⟨a, h1⟩
    use φsΛ.sndFieldOfContract ⟨a, h1⟩
    simp_all only [and_true, true_and]
    rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
    exact h1

@[simp]
lemma empty_not_haveEqTime {φs : List 𝓕.FieldOp} :
    ¬ HaveEqTime (empty : WickContraction φs.length) := by
  rw [haveEqTime_iff_finset]
  simp [empty]

/-- Given a Wick contraction the subset of contracted pairs between equal time fields. -/
def eqTimeContractSet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    Finset (Finset (Fin φs.length)) :=
  Finset.univ.filter (fun a =>
    a ∈ φsΛ.1 ∧ ∀ (h : a ∈ φsΛ.1),
    timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩]
    ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩])

lemma eqTimeContractSet_subset {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    eqTimeContractSet φsΛ ⊆ φsΛ.1 := by
  simp only [eqTimeContractSet, Fin.getElem_fin]
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp]
  intro h _
  exact h

lemma mem_of_mem_eqTimeContractSet{φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {a : Finset (Fin φs.length)} (h : a ∈ eqTimeContractSet φsΛ) : a ∈ φsΛ.1 := by
  simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.1

lemma join_eqTimeContractSet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    eqTimeContractSet (join φsΛ φsucΛ) = φsΛ.eqTimeContractSet ∪
    φsucΛ.eqTimeContractSet.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding := by
  ext a
  apply Iff.intro
  · intro h
    have hmem := mem_of_mem_eqTimeContractSet h
    have ht := joinLiftLeft_or_joinLiftRight_of_mem_join (φsucΛ := φsucΛ) _ hmem
    rcases ht with ht | ht
    · obtain ⟨b, rfl⟩ := ht
      simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
        RelEmbedding.coe_toEmbedding]
      left
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
      apply And.intro (by simp [joinLiftLeft])
      intro h'
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
        Finset.coe_mem, Subtype.coe_eta, join_fstFieldOfContract_joinLiftLeft,
        join_sndFieldOfContract_joinLift, forall_true_left, true_and] at h
      exact h
    · obtain ⟨b, rfl⟩ := ht
      simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
        RelEmbedding.coe_toEmbedding]
      right
      use b
      rw [Finset.mapEmbedding_apply]
      simp only [joinLiftRight, and_true]
      simpa [eqTimeContractSet] using h
  · intro h
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at h
    rcases h with h | h
    · simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      apply And.intro
      · simp [join, h.1]
      · intro h'
        have h2 := h.2 h.1
        exact h2
    · simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [eqTimeContractSet, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      obtain ⟨b, h1, h2, rfl⟩ := h
      apply And.intro
      · simp [join, h1]
      · intro h'
        have h2 := h1.2 h1.1
        have hj : ⟨(Finset.mapEmbedding uncontractedListEmd) b, h'⟩
          = joinLiftRight ⟨b, h1.1⟩ := by rfl
        simp only [hj, join_fstFieldOfContract_joinLiftRight, getElem_uncontractedListEmd,
          join_sndFieldOfContract_joinLiftRight]
        simpa using h2

/- Start of proof attempt -/
lemma round1_h1 (φs : List 𝓕.FieldOp)
  (φsΛ : WickContraction φs.length)
  (h : ¬ HaveEqTime φsΛ):
  ∀ (a : Finset (Fin φs.length)), a ∈ eqTimeContractSet φsΛ → False := by
  intro a ha
  have h5 : a ∈ φsΛ.1 ∧ ∀ (h : a ∈ φsΛ.1), timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩] ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := by
    simp only [eqTimeContractSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    tauto
  have h51 : a ∈ φsΛ.1 := h5.1
  have h52 : ∀ (h : a ∈ φsΛ.1), timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩] ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := h5.2
  have h4 : timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h51⟩] φs[φsΛ.sndFieldOfContract ⟨a, h51⟩] ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h51⟩] φs[φsΛ.fstFieldOfContract ⟨a, h51⟩] := h52 h51
  have h6 : HaveEqTime φsΛ ↔ ∃ (a : Finset (Fin φs.length)) (h : a ∈ φsΛ.1), timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩] ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := by
    exact haveEqTime_iff_finset φsΛ
  have h7 : ∀ (a : Finset (Fin φs.length)) (h : a ∈ φsΛ.1), ¬ (timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩] ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩]) := by
    by_contra h7
    push_neg at h7
    have h71 : ∃ (a : Finset (Fin φs.length)) (h : a ∈ φsΛ.1), timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩] ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := by
      exact h7
    have h61 : HaveEqTime φsΛ := by
      rw [h6]
      exact h71
    tauto
  have h8 := h7 a h51
  tauto

lemma round1_h9 (φs : List 𝓕.FieldOp)
  (φsΛ : WickContraction φs.length)
  (h1 : ∀ (a : Finset (Fin φs.length)), a ∈ eqTimeContractSet φsΛ → False):
  ∀ (a : Finset (Fin φs.length)), a ∉ eqTimeContractSet φsΛ := by
  intro a
  intro h10
  have h11 := h1 a h10
  contradiction

theorem eqTimeContractSet_of_not_haveEqTime {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (h : ¬ HaveEqTime φsΛ) : eqTimeContractSet φsΛ = ∅  := by

  have h1 : ∀ (a : Finset (Fin φs.length)), a ∈ eqTimeContractSet φsΛ → False := by
    exact round1_h1 φs φsΛ h
  have h9 : ∀ (a : Finset (Fin φs.length)), a ∉ eqTimeContractSet φsΛ := by
    exact round1_h9 φs φsΛ h1
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  exact h9
