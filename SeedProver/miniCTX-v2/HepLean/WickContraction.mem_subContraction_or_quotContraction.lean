-- In HepLean/HepLean/PerturbationTheory/WickContraction/SubContraction.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.FieldOpAlgebra.TimeContraction
/-!

# Sub contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
open HepLean.List
open FieldOpAlgebra

/-- Given a Wick contraction `φsΛ`, and a subset of `φsΛ.1`, the Wick contraction
  consisting of contracted pairs within that subset. -/
def subContraction (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    WickContraction φs.length :=
  ⟨S, by
    intro i hi
    exact φsΛ.2.1 i (ha hi),
    by
    intro i hi j hj
    exact φsΛ.2.2 i (ha hi) j (ha hj)⟩

lemma mem_of_mem_subContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin φs.length)} (ha : a ∈ (φsΛ.subContraction S hs).1) : a ∈ φsΛ.1 := by
  exact hs ha

/-- Given a Wick contraction `φsΛ`, and a subset `S` of `φsΛ.1`, the Wick contraction
  on the uncontracted list `[φsΛ.subContraction S ha]ᵘᶜ`
  consisting of the remaining contracted pairs of `φsΛ` not in `S`. -/
def quotContraction (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    WickContraction [φsΛ.subContraction S ha]ᵘᶜ.length :=
  ⟨Finset.filter (fun a => Finset.map uncontractedListEmd a ∈ φsΛ.1) Finset.univ,
  by
    intro a ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    simpa using φsΛ.2.1 (Finset.map uncontractedListEmd a) ha', by
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases hab : a = b
  · simp [hab]
  · simp only [hab, false_or]
    have hx := φsΛ.2.2 (Finset.map uncontractedListEmd a) ha (Finset.map uncontractedListEmd b) hb
    simp_all⟩

lemma mem_of_mem_quotContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin [φsΛ.subContraction S hs]ᵘᶜ.length)}
    (ha : a ∈ (quotContraction S hs).1) : Finset.map uncontractedListEmd a ∈ φsΛ.1 := by
  simp only [quotContraction, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  exact ha

/- Start of proof attempt -/
lemma round1_mem_subContraction_or_quotContraction (S : Finset (Finset (Fin φs.length))) (hs : S ⊆ φsΛ.1)
    (a : Finset (Fin φs.length)) (ha : a ∈ φsΛ.1) :
    a ∈ (φsΛ.subContraction S hs).1 ∨
    ∃ a', Finset.map uncontractedListEmd a' = a ∧ a' ∈ (quotContraction S hs).1 := by
  by_cases h1 : a ∈ S
  · -- Case 1: a ∈ S
    have h2 : a ∈ (φsΛ.subContraction S hs).1 := by
      simp only [subContraction, Finset.mem_filter, Finset.mem_univ, true_and] at *
      <;> tauto
    exact Or.inl h2
  · -- Case 2: a ∉ S
    have h2 : a ∉ S := h1
    have h_i_in_uncontracted : ∀ i ∈ a, i ∈ (φsΛ.subContraction S hs).uncontracted := by
      intro i hi
      have h6 : ∀ p ∈ (φsΛ.subContraction S hs).1, i ∉ p := by
        intro p hp
        intro h_ip
        have hp_in_S : p ∈ S := by
          simp only [subContraction, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          tauto
        have hp1 : p ∈ φsΛ.1 := hs hp_in_S
        have h51 : p = a ∨ Disjoint p a := φsΛ.2.2 p hp1 a ha
        cases h51 with
        | inl h511 =>
          -- Case p = a
          have h5111 : a ∈ S := by
            rw [h511] at hp_in_S
            exact hp_in_S
          contradiction
        | inr h512 =>
          -- Case Disjoint p a
          have h_disj : Disjoint p a := h512
          have h141 : i ∈ p ∩ a := Finset.mem_inter.mpr ⟨h_ip, hi⟩
          have h142 : p ∩ a = ∅ := by
            rw [Finset.disjoint_iff_inter_eq_empty] at h_disj
            exact h_disj
          rw [h142] at h141
          contradiction
      have h8 : i ∈ (φsΛ.subContraction S hs).uncontracted := by
        rw [WickContraction.mem_uncontracted_iff_not_contracted]
        exact h6
      exact h8
    have h9 : ∀ i ∈ a, ∃ j : Fin [φsΛ.subContraction S hs]ᵘᶜ.length, uncontractedListEmd j = i := by
      intro i hi
      have h10 : i ∈ (φsΛ.subContraction S hs).uncontracted := h_i_in_uncontracted i hi
      exact WickContraction.uncontractedListEmd_surjective_mem_uncontracted i h10
    set a' : Finset (Fin [φsΛ.subContraction S hs]ᵘᶜ.length) := Finset.filter (fun j => uncontractedListEmd j ∈ a) Finset.univ with ha'
    have h101 : Finset.map uncontractedListEmd a' ⊆ a := by
      intro x hx
      rcases Finset.mem_map.mp hx with ⟨j, hj, rfl⟩
      have h1013 : uncontractedListEmd j ∈ a := by
        have h1014 : j ∈ a' := hj
        simp only [ha', Finset.mem_filter, Finset.mem_univ, true_and] at h1014
        tauto
      simpa using h1013
    have h102 : a ⊆ Finset.map uncontractedListEmd a' := by
      intro x hx
      rcases h9 x hx with ⟨j, hj1⟩
      have h1021 : uncontractedListEmd j ∈ a := by
        rw [hj1]
        exact hx
      have h1022 : j ∈ a' := by
        simp only [ha', Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1021
      have h1024 : x ∈ Finset.map uncontractedListEmd a' := by
        refine' Finset.mem_map.mpr ⟨j, h1022, by simp [hj1]⟩
      exact h1024
    have h10 : Finset.map uncontractedListEmd a' = a := by
      apply Finset.Subset.antisymm h101 h102
    have h16 : Finset.map uncontractedListEmd a' ∈ φsΛ.1 := by
      rw [h10]
      exact ha
    have h17 : a' ∈ (quotContraction S hs).1 := by
      simp only [quotContraction, Finset.mem_filter, Finset.mem_univ, true_and] at *
      <;> tauto
    refine' Or.inr ⟨a', ⟨h10, h17⟩⟩

theorem mem_subContraction_or_quotContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin φs.length)} (ha : a ∈ φsΛ.1) :
    a ∈ (φsΛ.subContraction S hs).1 ∨
    ∃ a', Finset.map uncontractedListEmd a' = a ∧ a' ∈ (quotContraction S hs).1  := by

  exact round1_mem_subContraction_or_quotContraction S hs a ha
