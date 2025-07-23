-- In Seymour/Seymour/ForMathlib/SetTheory.lean

import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.SymmDiff
import Mathlib.Tactic

import Seymour.Basic

/-!
This provides lemmas about sets (mostly dealing with disjointness) that are missing in Mathlib.
-/

variable {α : Type}

section Other

lemma set_union_union_eq_rev (X Y Z : Set α) : X ∪ Y ∪ Z = Z ∪ Y ∪ X := by
  rw [Set.union_assoc, Set.union_comm, Set.union_comm Y Z]

lemma setminus_inter_union_eq_union {X Y : Set α} : X \ (X ∩ Y) ∪ Y = X ∪ Y := by
  tauto_set

lemma nonempty_inter_not_ssubset_empty_inter {A B E : Set α} (hA : (A ∩ E).Nonempty) (hB : B ∩ E = ∅) :
    ¬(A ⊂ B) := by
  intro ⟨hAB, _⟩
  obtain ⟨x, hxAE⟩ := hA
  have hxBE : x ∈ B ∩ E := (Set.inter_subset_inter hAB fun _ => id) hxAE
  rw [hB] at hxBE
  tauto

lemma ssubset_self_union_other_elem {a : α} {X : Set α} (ha : a ∉ X) :
    X ⊂ X ∪ {a} := by
  constructor
  · exact Set.subset_union_left
  · by_contra hX
    rw [Set.union_subset_iff] at hX
    obtain ⟨_, haa⟩ := hX
    tauto

lemma singleton_union_ssubset_union_iff {a : α} {A B : Set α} (haA : a ∉ A) (haB : a ∉ B) :
    A ∪ {a} ⊂ B ∪ {a} ↔ A ⊂ B := by
  constructor
  · intro hAB
    obtain ⟨hABl, hABr⟩ := hAB
    constructor
    · intro x hx
      apply ne_of_mem_of_not_mem hx at haA
      cases hABl (Set.mem_union_left {a} hx) <;> tauto
    · by_contra hBA
      apply Set.union_subset_union_left {a} at hBA
      tauto
  · intro hAB
    obtain ⟨hABl, hABr⟩ := hAB
    constructor
    · exact Set.union_subset_union_left {a} hABl
    · by_contra hBA
      rw [Set.union_singleton, Set.union_singleton] at hBA
      apply (Set.insert_subset_insert_iff haB).→ at hBA
      tauto

lemma ssub_parts_ssub {A B E₁ E₂ : Set α}
    (hA : A ⊆ E₁ ∪ E₂) (hB : B ⊆ E₁ ∪ E₂) (hAB₁ : A ∩ E₁ ⊂ B ∩ E₁) (hAB₂ : A ∩ E₂ ⊂ B ∩ E₂) :
    A ⊂ B := by
  constructor
  · obtain ⟨hE₁, _⟩ := hAB₁
    obtain ⟨hE₂, _⟩ := hAB₂
    rw [Set.left_eq_inter.← hA, Set.left_eq_inter.← hB, Set.inter_union_distrib_left, Set.inter_union_distrib_left]
    exact Set.union_subset_union hE₁ hE₂
  · intro hBA
    obtain ⟨_, hE₁⟩ := hAB₁
    obtain ⟨x, hxBE₁, hxnAE₁⟩ := Set.not_subset.→ hE₁
    have hxB : x ∈ B := Set.mem_of_mem_inter_left hxBE₁
    have hxE₁ : x ∈ E₁ := Set.mem_of_mem_inter_right hxBE₁
    tauto

lemma HasSubset.Subset.parts_eq {A E₁ E₂ : Set α} (hA : A ⊆ E₁ ∪ E₂) : (A ∩ E₁) ∪ (A ∩ E₂) = A :=
  ((subset_of_subset_of_eq
    (Set.subset_inter (fun _ => id) hA)
    (Set.inter_union_distrib_left A E₁ E₂)).antisymm
  (Set.union_subset Set.inter_subset_left Set.inter_subset_left)).symm

lemma elem_notin_set_minus_singleton (a : α) (X : Set α) : a ∉ X \ {a} := Set.not_mem_diff_of_mem rfl

lemma sub_union_diff_sub_union {A B C : Set α} (hA : A ⊆ B \ C) : A ⊆ B :=
  fun _ hA' => Set.diff_subset (hA hA')

lemma singleton_inter_in_left {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : a ∈ X :=
  Set.mem_of_mem_inter_left (ha.symm.subset rfl)

lemma singleton_inter_in_right {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : a ∈ Y :=
  Set.mem_of_mem_inter_right (ha.symm.subset rfl)

lemma singleton_inter_subset_left {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ X := by
  rw [Set.singleton_subset_iff]
  exact singleton_inter_in_left ha

lemma singleton_inter_subset_right {X Y : Set α} {a : α} (ha : X ∩ Y = {a}) : {a} ⊆ Y := by
  rw [Set.singleton_subset_iff]
  exact singleton_inter_in_right ha

/- Start of proof attempt -/
lemma round1_diff_subset_parent {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ \ X₂ ⊆ E := by
  intro x hx
  have hx1 : x ∈ X₁ := hx.1
  exact hX₁E hx1

/-- Being a subset is preserved under subtracting sets. -/
theorem diff_subset_parent {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ \ X₂ ⊆ E  := by

  exact round1_diff_subset_parent hX₁E
