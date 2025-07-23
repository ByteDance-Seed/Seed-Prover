-- In HepLean/HepLean/PerturbationTheory/WickContraction/InsertAndContractNat.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Erase
/-!

# Inserting an element into a contraction

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

/-!

## Inserting an element into a contraction

-/

/-- Given a Wick contraction `c` for `n`, a position `i : Fin n.succ` and
  an optional uncontracted element `j : Option (c.uncontracted)` of `c`.
  The Wick contraction for `n.succ` formed by 'inserting' `i` into `Fin n`
  and contracting it optionally with `j`. -/
def insertAndContractNat (c : WickContraction n) (i : Fin n.succ) (j : Option (c.uncontracted)) :
    WickContraction n.succ := by
  let f := Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1
  let f' := match j with | none => f | some j => Insert.insert {i, i.succAbove j} f
  refine ⟨f', ?_, ?_⟩
  · simp only [Nat.succ_eq_add_one, f']
    match j with
    | none =>
      simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
      intro a ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact c.2.1 a ha
    | some j =>
      simp only [Finset.mem_insert, forall_eq_or_imp]
      apply And.intro
      · rw [@Finset.card_eq_two]
        use i
        use (i.succAbove j)
        simp only [ne_eq, and_true]
        exact Fin.ne_succAbove i j
      · simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
        intro a ha
        rw [Finset.mapEmbedding_apply]
        simp only [Finset.card_map]
        exact c.2.1 a ha
  · intro a ha b hb
    simp only [Nat.succ_eq_add_one, f'] at ha hb
    match j with
    | none =>
      simp_all only [f, Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        Nat.succ_eq_add_one]
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      subst ha''
      subst hb''
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
      exact c.2.2 a' ha' b' hb'
    | some j =>
      simp_all only [Finset.mem_insert, Nat.succ_eq_add_one]
      match ha, hb with
      | Or.inl ha, Or.inl hb =>
        rw [ha, hb]
        simp
      | Or.inl ha, Or.inr hb =>
        apply Or.inr
        subst ha
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
        simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding, f] at hb
        obtain ⟨a', hb', hb''⟩ := hb
        subst hb''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          exact fun x _ => Fin.succAbove_ne i x
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' hb' ha)
      | Or.inr ha, Or.inl hb =>
        apply Or.inr
        subst hb
        simp only [Finset.disjoint_insert_right, Nat.succ_eq_add_one,
          Finset.disjoint_singleton_right]
        simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding, f] at ha
        obtain ⟨a', ha', ha''⟩ := ha
        subst ha''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          exact fun x _ => Fin.succAbove_ne i x
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' ha' ha)
      | Or.inr ha, Or.inr hb =>
        simp_all only [f, Finset.le_eq_subset,
          or_true, Finset.mem_map, RelEmbedding.coe_toEmbedding]
        obtain ⟨a', ha', ha''⟩ := ha
        obtain ⟨b', hb', hb''⟩ := hb
        subst ha''
        subst hb''
        simp only [EmbeddingLike.apply_eq_iff_eq]
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
        exact c.2.2 a' ha' b' hb'

lemma insertAndContractNat_of_isSome (c : WickContraction n) (i : Fin n.succ)
    (j : Option c.uncontracted) (hj : j.isSome) :
    (insertAndContractNat c i j).1 = Insert.insert {i, i.succAbove (j.get hj)}
    (Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1) := by
  simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.le_eq_subset]
  rw [@Option.isSome_iff_exists] at hj
  obtain ⟨j, hj⟩ := hj
  subst hj
  simp

@[simp]
lemma self_mem_uncontracted_of_insertAndContractNat_none (c : WickContraction n) (i : Fin n.succ) :
    i ∈ (insertAndContractNat c i none).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.le_eq_subset, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at hp
  obtain ⟨a, ha, ha'⟩ := hp
  have hc := c.2.1 a ha
  rw [@Finset.card_eq_two] at hc
  obtain ⟨x, y, hxy, ha⟩ := hc
  subst ha
  subst ha'
  rw [Finset.mapEmbedding_apply]
  simp only [Nat.succ_eq_add_one, Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  apply And.intro
  · exact Fin.ne_succAbove i x
  · exact Fin.ne_succAbove i y

@[simp]
lemma self_not_mem_uncontracted_of_insertAndContractNat_some (c : WickContraction n)
    (i : Fin n.succ) (j : c.uncontracted) :
    i ∉ (insertAndContractNat c i (some j)).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  simp [insertAndContractNat]

lemma insertAndContractNat_succAbove_mem_uncontracted_iff (c : WickContraction n) (i : Fin n.succ)
    (j : Fin n) :
    (i.succAbove j) ∈ (insertAndContractNat c i none).uncontracted ↔ j ∈ c.uncontracted := by
  rw [mem_uncontracted_iff_not_contracted, mem_uncontracted_iff_not_contracted]
  simp only [Nat.succ_eq_add_one, insertAndContractNat, Finset.le_eq_subset, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply Iff.intro
  · intro h p hp
    have hp' := h p hp
    have hc := c.2.1 p hp
    rw [Finset.card_eq_two] at hc
    obtain ⟨x, y, hxy, hp⟩ := hc
    subst hp
    rw [Finset.mapEmbedding_apply] at hp'
    simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hp'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact And.intro (fun a => hp'.1 (congrArg i.succAbove a))
      (fun a => hp'.2 (congrArg i.succAbove a))
  · intro h p hp
    have hc := c.2.1 p hp
    rw [Finset.card_eq_two] at hc
    obtain ⟨x, y, hxy, hp⟩ := hc
    subst hp
    rw [Finset.mapEmbedding_apply]
    simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    have hp' := h {x, y} hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
    apply And.intro
      (fun a => hp'.1 (i.succAbove_right_injective a))
      (fun a => hp'.2 (i.succAbove_right_injective a))

@[simp]
lemma mem_uncontracted_insertAndContractNat_none_iff (c : WickContraction n) (i : Fin n.succ)
    (k : Fin n.succ) : k ∈ (insertAndContractNat c i none).uncontracted ↔
    k = i ∨ ∃ j, k = i.succAbove j ∧ j ∈ c.uncontracted := by
  by_cases hi : k = i
  · subst hi
    simp
  · simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hi
    obtain ⟨z, hk⟩ := hi
    subst hk
    have hn : ¬ i.succAbove z = i := Fin.succAbove_ne i z
    simp only [Nat.succ_eq_add_one, insertAndContractNat_succAbove_mem_uncontracted_iff, hn,
      false_or]
    apply Iff.intro
    · intro h
      exact ⟨z, rfl, h⟩
    · intro h
      obtain ⟨j, hk⟩ := h
      have hjk : z = j := Fin.succAbove_right_inj.mp hk.1
      subst hjk
      exact hk.2

lemma insertAndContractNat_none_uncontracted (c : WickContraction n) (i : Fin n.succ) :
    (insertAndContractNat c i none).uncontracted =
    Insert.insert i (c.uncontracted.map i.succAboveEmb) := by
  ext a
  simp only [Nat.succ_eq_add_one, mem_uncontracted_insertAndContractNat_none_iff, Finset.mem_insert,
    Finset.mem_map, Fin.succAboveEmb_apply]
  apply Iff.intro
  · intro a_1
    cases a_1 with
    | inl h =>
      subst h
      simp_all only [true_or]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨left, right⟩ := h
      subst left
      apply Or.inr
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
  · intro a_1
    cases a_1 with
    | inl h =>
      subst h
      simp_all only [true_or]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨left, right⟩ := h
      subst right
      apply Or.inr
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {exact left
        }
        · simp_all only

/- Start of proof attempt -/
lemma round1_forward_direction (c : WickContraction n) (i : Fin n.succ)
    (k : Fin n.succ) (j : c.uncontracted) (h1 : k ∈ (insertAndContractNat c i (some j)).uncontracted) :
    ∃ z, k = i.succAbove z ∧ z ∈ c.uncontracted ∧ z ≠ j := by
  have h1' : ∀ p ∈ (insertAndContractNat c i (some j)).1, k ∉ p := by
    rw [mem_uncontracted_iff_not_contracted] at h1
    exact h1
  have h12 : k ∉ ({i, i.succAbove j} : Finset (Fin n.succ)) := by
    have h121 : ({i, i.succAbove j} : Finset (Fin n.succ)) ∈ (insertAndContractNat c i (some j)).1 := by
      simp [insertAndContractNat]
      <;> aesop
    have h122 := h1' ({i, i.succAbove j}) h121
    exact h122
  have h121 : k ≠ i := by
    intro h1211
    have h1212 : k ∈ ({i, i.succAbove j} : Finset (Fin n.succ)) := by
      simp [h1211]
    contradiction
  have h122 : k ≠ i.succAbove j := by
    intro h1221
    have h1222 : k ∈ ({i, i.succAbove j} : Finset (Fin n.succ)) := by
      simp [h1221]
    contradiction
  have h13 : ∀ p ∈ (insertAndContractNat c i none).1, k ∉ p := by
    intro p hp
    have h131 : p ∈ (insertAndContractNat c i (some j)).1 := by
      simp [insertAndContractNat] at hp ⊢ <;> aesop
    exact h1' p h131
  have h14 : k ∈ (insertAndContractNat c i none).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    exact h13
  have h15 : k = i ∨ ∃ j', k = i.succAbove j' ∧ j' ∈ c.uncontracted := by
    have h151 := mem_uncontracted_insertAndContractNat_none_iff c i k
    have h152 : k ∈ (insertAndContractNat c i none).uncontracted := h14
    have h153 : k = i ∨ ∃ j', k = i.succAbove j' ∧ j' ∈ c.uncontracted := by tauto
    tauto
  have h16 : ∃ j', k = i.succAbove j' ∧ j' ∈ c.uncontracted := by
    cases h15 with
    | inl h15 =>
      -- Case k = i
      contradiction
    | inr h15 =>
      -- Case ∃ j', k = i.succAbove j' ∧ j' ∈ c.uncontracted
      tauto
  rcases h16 with ⟨j', h161, h162⟩
  have h17 : i.succAbove j' ≠ i.succAbove j := by
    intro h171
    have h172 : k = i.succAbove j := by
      rw [h161] at *
      tauto
    contradiction
  have h18 : j' ≠ j := by
    intro h181
    rw [h181] at h17
    contradiction
  refine ⟨j', ⟨h161, ⟨h162, h18⟩⟩⟩

lemma round1_backward_direction (c : WickContraction n) (i : Fin n.succ)
    (k : Fin n.succ) (j : c.uncontracted) (h2 : ∃ z, k = i.succAbove z ∧ z ∈ c.uncontracted ∧ z ≠ j) :
    k ∈ (insertAndContractNat c i (some j)).uncontracted := by
  rcases h2 with ⟨z, h21, h22, h23⟩
  have h3 : k ∈ (insertAndContractNat c i none).uncontracted := by
    have h31 : k ∈ (insertAndContractNat c i none).uncontracted := by
      have h311 : k = i ∨ ∃ j', k = i.succAbove j' ∧ j' ∈ c.uncontracted := by
        right
        refine ⟨z, ⟨h21, h22⟩⟩
      have h312 : k ∈ (insertAndContractNat c i none).uncontracted := by
        have h313 : k ∈ (insertAndContractNat c i none).uncontracted ↔ k = i ∨ ∃ j', k = i.succAbove j' ∧ j' ∈ c.uncontracted := mem_uncontracted_insertAndContractNat_none_iff c i k
        exact h313.mpr h311
      exact h312
    exact h31
  have h3' : ∀ p ∈ (insertAndContractNat c i none).1, k ∉ p := by
    rw [mem_uncontracted_iff_not_contracted] at h3
    exact h3
  have h4 : k ∉ ({i, i.succAbove j} : Finset (Fin n.succ)) := by
    have h41 : k ≠ i := by
      intro h411
      have h412 : i.succAbove z = i := by
        rw [h21] at h411
        tauto
      have h413 : i.succAbove z ≠ i := Fin.succAbove_ne i z
      contradiction
    have h42 : k ≠ i.succAbove j := by
      intro h421
      have h422 : i.succAbove z = i.succAbove j := by
        rw [h21] at h421
        tauto
      have h423 : z = j := by
        exact Fin.succAbove_right_injective h422
      have h424 : z ≠ j := h23
      contradiction
    simp [h41, h42]
    <;> aesop
  have h5 : ∀ p ∈ (insertAndContractNat c i (some j)).1, k ∉ p := by
    intro p hp
    by_cases h51 : p = ({i, i.succAbove j} : Finset (Fin n.succ))
    · -- Case 1: p = {i, i.succAbove j}
      rw [h51]
      exact h4
    · -- Case 2: p ≠ {i, i.succAbove j}
      have h52 : p ∈ (insertAndContractNat c i none).1 := by
        simp [insertAndContractNat] at hp ⊢ <;> aesop
      exact h3' p h52
  have h6 : k ∈ (insertAndContractNat c i (some j)).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    exact h5
  exact h6

theorem mem_uncontracted_insertAndContractNat_some_iff (c : WickContraction n) (i : Fin n.succ)
    (k : Fin n.succ) (j : c.uncontracted) :
    k ∈ (insertAndContractNat c i (some j)).uncontracted ↔
    ∃ z, k = i.succAbove z ∧ z ∈ c.uncontracted ∧ z ≠ j  := by

  constructor
  · exact round1_forward_direction c i k j
  · exact round1_backward_direction c i k j
