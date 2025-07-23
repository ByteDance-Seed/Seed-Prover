-- In HepLean/HepLean/PerturbationTheory/WickContraction/Sign/Join.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Join
/-!

# Sign associated with joining two Wick contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

open FieldStatistic

lemma stat_signFinset_right {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i j : Fin [φsΛ]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨[φsΛ]ᵘᶜ.get, φsucΛ.signFinset i j⟩) =
    (𝓕 |>ₛ ⟨φs.get, (φsucΛ.signFinset i j).map uncontractedListEmd⟩) := by
  simp only [ofFinset]
  congr 1
  rw [← fin_finset_sort_map_monotone]
  simp only [List.map_map, List.map_inj_left, Finset.mem_sort, List.get_eq_getElem,
    Function.comp_apply, getElem_uncontractedListEmd, implies_true]
  intro i j h
  exact uncontractedListEmd_strictMono h

lemma signFinset_right_map_uncontractedListEmd_eq_filter {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (i j : Fin [φsΛ]ᵘᶜ.length) : (φsucΛ.signFinset i j).map uncontractedListEmd =
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd i) (uncontractedListEmd j)).filter
    (fun c => c ∈ φsΛ.uncontracted) := by
  ext a
  simp only [Finset.mem_map, Finset.mem_filter]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    apply And.intro
    · simp_all only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      join_getDual?_apply_uncontractedListEmb, Option.map_eq_none', Option.isSome_map']
      apply And.intro
      · exact uncontractedListEmd_strictMono ha.1
      · apply And.intro
        · exact uncontractedListEmd_strictMono ha.2.1
        · have ha2 := ha.2.2
          simp_all only [and_true]
          rcases ha2 with ha2 | ha2
          · simp [ha2]
          · right
            intro h
            apply lt_of_lt_of_eq (uncontractedListEmd_strictMono (ha2 h))
            rw [Option.get_map]
    · exact uncontractedListEmd_mem_uncontracted a
  · intro h
    have h2 := h.2
    have h2' := uncontractedListEmd_surjective_mem_uncontracted a h.2
    obtain ⟨a, rfl⟩ := h2'
    use a
    simp_all only [signFinset, Finset.mem_filter, Finset.mem_univ,
      join_getDual?_apply_uncontractedListEmb, Option.map_eq_none', Option.isSome_map', true_and,
      and_true, and_self]
    apply And.intro
    · have h1 := h.1
      rw [StrictMono.lt_iff_lt] at h1
      exact h1
      exact fun _ _ h => uncontractedListEmd_strictMono h
    · apply And.intro
      · have h1 := h.2.1
        rw [StrictMono.lt_iff_lt] at h1
        exact h1
        exact fun _ _ h => uncontractedListEmd_strictMono h
      · have h1 := h.2.2
        simp_all only [and_true]
        rcases h1 with h1 | h1
        · simp [h1]
        · right
          intro h
          have h1' := h1 h
          have hl : uncontractedListEmd i < uncontractedListEmd ((φsucΛ.getDual? a).get h) := by
            apply lt_of_lt_of_eq h1'
            simp [Option.get_map]
          rw [StrictMono.lt_iff_lt] at hl
          exact hl
          exact fun _ _ h => uncontractedListEmd_strictMono h

lemma sign_right_eq_prod_mul_prod {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    φsucΛ.sign = (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
      (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
      (fun c => ¬ c ∈ φsΛ.uncontracted)⟩)) *
    (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  rw [← Finset.prod_mul_distrib, sign]
  congr
  funext a
  rw [← map_mul]
  congr
  rw [stat_signFinset_right, signFinset_right_map_uncontractedListEmd_eq_filter]
  rw [ofFinset_filter]

lemma join_singleton_signFinset_eq_filter {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).signFinset i j =
    ((singleton h).signFinset i j).filter (fun c => ¬
    (((join (singleton h) φsucΛ).getDual? c).isSome ∧
    ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
    (((join (singleton h) φsucΛ).getDual? c).get h1) < i))) := by
  ext a
  simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_lt,
    and_assoc, and_congr_right_iff]
  intro h1 h2
  have h1 : (singleton h).getDual? a = none := by
    rw [singleton_getDual?_eq_none_iff_neq]
    omega
  simp only [h1, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, true_and]
  apply Iff.intro
  · intro h1 h2
    rcases h1 with h1 | h1
    · simp only [h1, Option.isSome_none, Bool.false_eq_true, IsEmpty.exists_iff]
      have h2' : ¬ (((singleton h).join φsucΛ).getDual? a).isSome := by
        exact Option.not_isSome_iff_eq_none.mpr h1
      exact h2' h2
    use h2
    have h1 := h1 h2
    omega
  · intro h2
    by_cases h2' : (((singleton h).join φsucΛ).getDual? a).isSome = true
    · have h2 := h2 h2'
      obtain ⟨hb, h2⟩ := h2
      right
      intro hl
      apply lt_of_le_of_ne h2
      by_contra hn
      have hij : ((singleton h).join φsucΛ).getDual? i = j := by
        rw [@getDual?_eq_some_iff_mem]
        simp [join, singleton]
      simp only [hn, getDual?_getDual?_get_get, Option.some.injEq] at hij
      omega
    · simp only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at h2'
      simp [h2']

lemma join_singleton_left_signFinset_eq_filter {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨φs.get, (singleton h).signFinset i j⟩)
    = (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩) *
      (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩) := by
  conv_rhs =>
    left
    rw [join_singleton_signFinset_eq_filter]
  rw [mul_comm]
  exact (ofFinset_filter_mul_neg 𝓕.fieldOpStatistic _ _ _).symm

/-- The difference in sign between `φsucΛ.sign` and the direct contribution of `φsucΛ` to
  `(join (singleton h) φsucΛ)`. -/
def joinSignRightExtra {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) : ℂ :=
    ∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
    ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
    (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
    (fun c => ¬ c ∈ (singleton h).uncontracted)⟩)

/-- The difference in sign between `(singleton h).sign` and the direct contribution of
  `(singleton h)` to `(join (singleton h) φsucΛ)`. -/
def joinSignLeftExtra {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) : ℂ :=
    𝓢(𝓕 |>ₛ φs[j], (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩))

lemma join_singleton_sign_left {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (singleton h).sign = 𝓢(𝓕 |>ₛ φs[j],
    (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩)) * (joinSignLeftExtra h φsucΛ) := by
  rw [singleton_sign_expand]
  rw [join_singleton_left_signFinset_eq_filter h φsucΛ]
  rw [map_mul]
  rfl

/- Start of proof attempt -/
lemma round1_join_singleton_sign_right {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    φsucΛ.sign =
    (joinSignRightExtra h φsucΛ) *
    (∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  have h1 := sign_right_eq_prod_mul_prod (singleton h) φsucΛ
  simpa using h1

theorem join_singleton_sign_right {φs : List 𝓕.FieldOp}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    φsucΛ.sign =
    (joinSignRightExtra h φsucΛ) *
    (∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩))  := by

  exact round1_join_singleton_sign_right h φsucΛ
