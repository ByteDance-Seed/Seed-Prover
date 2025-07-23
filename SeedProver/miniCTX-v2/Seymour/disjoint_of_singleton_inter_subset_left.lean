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

/-- Being a subset is preserved under subtracting sets. -/
lemma diff_subset_parent {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ \ X₂ ⊆ E :=
  Set.diff_subset_iff.← (Set.subset_union_of_subset_right hX₁E X₂)

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_left {X₁ X₂ E : Set α} (hX₁E : X₁ ⊆ E) :
    X₁ ∩ X₂ ⊆ E :=
  (Set.inter_subset_inter_left X₂ hX₁E).trans Set.inter_subset_left

/-- Being a subset is preserved under taking intersections. -/
lemma inter_subset_parent_right {X₁ X₂ E : Set α} (hX₂E : X₂ ⊆ E) :
    X₁ ∩ X₂ ⊆ E := by
  rw [Set.inter_comm]
  exact inter_subset_parent_left hX₂E

/-- Intersection of two sets is subset of their union. -/
lemma inter_subset_union {X₁ X₂ : Set α} :
    X₁ ∩ X₂ ⊆ X₁ ∪ X₂ :=
  inter_subset_parent_left Set.subset_union_left

lemma subset_diff_empty_eq {A B : Set α} (hAB : A ⊆ B) (hBA : B \ A = ∅) : A = B :=
  A.union_empty ▸ hBA ▸ Set.union_diff_cancel hAB

end Other

section Disjoint

lemma Disjoint.ni_of_in {X Y : Set α} {a : α} (hXY : X ⫗ Y) (ha : a ∈ X) :
    a ∉ Y := by
  intro ha'
  simpa [hXY.inter_eq] using Set.mem_inter ha ha'

lemma disjoint_of_singleton_inter_left_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    X \ {a} ⫗ Y := by
  tauto_set

lemma disjoint_of_singleton_inter_right_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    X ⫗ Y \ {a} := by
  rw [disjoint_comm]
  rw [Set.inter_comm] at hXY
  exact disjoint_of_singleton_inter_left_wo hXY

lemma disjoint_of_singleton_inter_both_wo {X Y : Set α} {a : α} (hXY : X ∩ Y = {a}) :
    X \ {a} ⫗ Y \ {a} :=
  Disjoint.disjoint_sdiff_left (disjoint_of_singleton_inter_right_wo hXY)

/- Start of proof attempt -/
lemma round1_h1 (X Y Z : Set α) (a : α) (hXY : X ∩ Y = {a}) (hZ : Z ⊆ X) (haZ : a ∉ Z) :
    Z ∩ Y = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro z hz
  have hz_in_Z : z ∈ Z := hz.1
  have hz_in_Y : z ∈ Y := hz.2
  have hz_in_X : z ∈ X := hZ hz_in_Z
  have hz_in_X_inter_Y : z ∈ X ∩ Y := ⟨hz_in_X, hz_in_Y⟩
  have hz_in_singleton_a : z ∈ ({a} : Set α) := by
    rw [hXY] at hz_in_X_inter_Y
    exact hz_in_X_inter_Y
  have hz_eq_a : z = a := by simpa using hz_in_singleton_a
  have ha_in_Z : a ∈ Z := by
    rw [hz_eq_a] at hz_in_Z
    exact hz_in_Z
  contradiction

theorem disjoint_of_singleton_inter_subset_left {X Y Z : Set α} {a : α} (hXY : X ∩ Y = {a}) (hZ : Z ⊆ X) (haZ : a ∉ Z) :
    Z ⫗ Y  := by

  have h1 : Z ∩ Y = ∅ := round1_h1 X Y Z a hXY hZ haZ
  have h2 : Z ⫗ Y := by
    have h3 : Z ∩ Y = ∅ := h1
    have h4 : Z ⫗ Y := by
      rw [Set.disjoint_iff_inter_eq_empty]
      exact h3
    exact h4
  exact h2
