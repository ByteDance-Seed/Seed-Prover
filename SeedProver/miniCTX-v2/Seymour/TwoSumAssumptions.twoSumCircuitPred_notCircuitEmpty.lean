-- In Seymour/Seymour/Matroid/Operations/Sum2/Basic.lean

import Mathlib.Data.Set.Card
import Mathlib.Data.Matroid.Dual

import Seymour.ForMathlib.SetTheory
import Seymour.Matroid.Notions.Circuit
import Seymour.Matroid.Notions.CircuitAxioms
import Seymour.Matroid.Notions.Connectivity
import Seymour.Matroid.Constructors.CircuitMatroid

/-!
This file defines 2-sum of two (general) matroids `M₁` and `M₂`, denoted as `M₁ ⊕₂ M₂`.
-/

variable {α : Type}

section MainDefinitions

/-- `M₁ ⊕₂ M₂` is defined if `M₁` and `M₂` satisfy the following assumptions -/
structure TwoSumAssumptions (M₁ M₂ : Matroid α) : Prop where
  /-- `M₁` is finite -/
  M₁fin : M₁.Finite
  /-- `M₂` is finite -/
  M₂fin : M₂.Finite
  /-- `M₁` contains at least 2 elements -/
  M₁card : M₁.E.encard ≥ 2
  /-- `M₂` contains at least 2 elements -/
  M₂card : M₂.E.encard ≥ 2
  /-- `M₁` and `M₂` have exactly one element in common -/
  interSingleton : (M₁.E ∩ M₂.E).encard = 1
  /-- the common element of `M₁` and `M₂` is not a separator in `M₁` -/
  M₁sep : ¬M₁.Separator (M₁.E ∩ M₂.E)
  /-- the common element of `M₁` and `M₂` is not a separator in `M₂` -/
  M₂sep : ¬M₂.Separator (M₁.E ∩ M₂.E)

-- question: can avoid this assumption? -- which assumption? the finiteness?

/-- Ground set of `M₁ ⊕₂ M₂` -/
def twoSumGround (M₁ M₂ : Matroid α) : Set α :=
  (M₁.E ∪ M₂.E) \ (M₁.E ∩ M₂.E)

/-- Type 1 of circuits in `M₁ ⊕₂ M₂`: circuits of `M₁` that are disjoint with `M₁.E ∩ M₂.E` -/
def TwoSumCircuitType1 (M₁ M₂ : Matroid α) (C : Set α) : Prop :=
  M₁.Circuit C ∧ C ⫗ M₁.E ∩ M₂.E

/-- Type 2 of circuits in `M₁ ⊕₂ M₂`: circuits of `M₂` that are disjoint with `M₁.E ∩ M₂.E` -/
def TwoSumCircuitType2 (M₁ M₂ : Matroid α) (C : Set α) : Prop :=
  M₂.Circuit C ∧ C ⫗ M₁.E ∩ M₂.E

/-- Type 3 of circuits in `M₁ ⊕₂ M₂`:
    sets `(C₁ ∪ C₂) \ (M₁.E ∩ M₂.E)` where `C₁` and `C₂` are circuits in `M₁` and `M₂`, respectively,
    and `M₁.E ∩ M₂.E ⊆ C₁` and `M₁.E ∩ M₂.E ⊆ C₂` -/
def TwoSumCircuitType3 (M₁ M₂ : Matroid α) (C : Set α) : Prop :=
  M₁.Circuit ((C ∩ M₁.E) ∪ (M₁.E ∩ M₂.E)) ∧ M₂.Circuit ((C ∩ M₂.E) ∪ (M₁.E ∩ M₂.E)) ∧ C ⊆ twoSumGround M₁ M₂

/-- Circuit predicate of `M₁ ⊕₂ M₂`, which defines 2-sum as `CircuitMatroid` -/
def TwoSumCircuitPred (M₁ M₂ : Matroid α) : CircuitPredicate α :=
  fun C : Set α =>
    TwoSumCircuitType1 M₁ M₂ C ∨
    TwoSumCircuitType2 M₁ M₂ C ∨
    TwoSumCircuitType3 M₁ M₂ C

end MainDefinitions

section PropertiesAssumptions

variable {M₁ M₂ : Matroid α}

/-- 2-sum assumptions are symmetric -/
lemma TwoSumAssumptions.symm (assumptions : TwoSumAssumptions M₁ M₂) :
    TwoSumAssumptions M₂ M₁ :=
  ⟨
    assumptions.M₂fin,
    assumptions.M₁fin,
    assumptions.M₂card,
    assumptions.M₁card,
    Set.inter_comm M₁.E M₂.E ▸ assumptions.interSingleton,
    Set.inter_comm M₁.E M₂.E ▸ assumptions.M₂sep,
    Set.inter_comm M₁.E M₂.E ▸ assumptions.M₁sep,
  ⟩

/-- Intersection of ground sets is nonempty -/
lemma TwoSumAssumptions.inter_nonempty (assumptions : TwoSumAssumptions M₁ M₂) :
    (M₁.E ∩ M₂.E).Nonempty :=
  Set.one_le_encard_iff_nonempty.→ assumptions.interSingleton.symm.le

/-- Intersection of ground sets is a singleton set -/
lemma TwoSumAssumptions.inter_singleton (assumptions : TwoSumAssumptions M₁ M₂) :
    ∃ p : α, M₁.E ∩ M₂.E = {p} :=
  Set.encard_eq_one.→ assumptions.interSingleton

variable {p : α}

/-- Singleton element in intersection of ground sets in not a loop in `M₁` -/
lemma TwoSumAssumptions.inter_singleton_not_loop_M₁ (assumptions : TwoSumAssumptions M₁ M₂)
    (hp : M₁.E ∩ M₂.E = {p}) :
    ¬(M₁.Loop p) :=
  (hp ▸ assumptions.M₁sep <| Matroid.separator_loop ·)

/-- Singleton element in intersection of ground sets in not a coloop in `M₁` -/
lemma TwoSumAssumptions.inter_singleton_not_coloop_M₁ (assumptions : TwoSumAssumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) :
    ¬(M₁.Coloop p) :=
  (hp ▸ assumptions.M₁sep <| Matroid.separator_coloop ·)

/-- Singleton element in intersection of ground sets in not a loop in `M₂` -/
lemma TwoSumAssumptions.inter_singleton_not_loop_M₂ (assumptions : TwoSumAssumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) :
    ¬(M₂.Loop p) :=
  (hp ▸ assumptions.M₂sep <| Matroid.separator_loop ·)

/-- Singleton element in intersection of ground sets in not a coloop in `M₂` -/
lemma TwoSumAssumptions.inter_singleton_not_coloop_M₂ (assumptions : TwoSumAssumptions M₁ M₂) (hp : M₁.E ∩ M₂.E = {p}) :
    ¬(M₂.Coloop p) :=
  (hp ▸ assumptions.M₂sep <| Matroid.separator_coloop ·)

end PropertiesAssumptions

section PropertiesGroundSet

/-- Ground set of 2-sum is disjoint with `M₁.E ∩ M₂.E` -/
lemma twoSumGround_disjoint_inter (M₁ M₂ : Matroid α) :
    twoSumGround M₁ M₂ ⫗ M₁.E ∩ M₂.E :=
  Set.disjoint_sdiff_left

/-- Ground sets minus their intersection are disjoint sets -/
lemma twoSum_disjoint_grounds_diff_inter (M₁ M₂ : Matroid α) :
    M₁.E \ (M₁.E ∩ M₂.E) ⫗ M₂.E \ (M₁.E ∩ M₂.E) := by
  rw [Set.diff_self_inter, Set.diff_inter_self_eq_diff]
  exact disjoint_sdiff_sdiff

end PropertiesGroundSet

section PropertiesCircuitType1

variable {M₁ M₂ : Matroid α} {C : Set α}

/-- Circuit of type 1 is a circuit in `M₁` -/
lemma TwoSumCircuitType1.circuit_M₁ (hC : TwoSumCircuitType1 M₁ M₂ C) : M₁.Circuit C :=
  hC.left

/-- Circuit of type 1 is disjoint with `M₁.E ∩ M₂.E` -/
lemma TwoSumCircuitType1.disjoint_inter (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⫗ M₁.E ∩ M₂.E :=
  hC.right

/-- Circuit of type 1 lies in `M₁.E ∪ M₂.E` -/
lemma TwoSumCircuitType1.subset_union (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_left hC.circuit_M₁.subset_ground M₂.E

/-- Circuit of type 1 lies in ground set of `M₁ ⊕₂ M₂` -/
lemma TwoSumCircuitType1.subset_ground (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⊆ twoSumGround M₁ M₂ :=
  Set.subset_diff.← ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of type 1 lies in `M₁.E \ (M₁.E ∩ M₂.E)` -/
lemma TwoSumCircuitType1.subset_M₁_diff_inter (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⊆ M₁.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.← ⟨hC.circuit_M₁.subset_ground, hC.disjoint_inter⟩

/-- Circuit of type 1 is disjoint with `M₂.E` -/
lemma TwoSumCircuitType1.disjoint_M₂ (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⫗ M₂.E := by
  have hMM := twoSum_disjoint_grounds_diff_inter M₁ M₂
  have hCM₂ := Set.disjoint_of_subset_left hC.subset_M₁_diff_inter hMM
  have hCM₂ := Set.disjoint_union_right.← ⟨hCM₂, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_right] at hCM₂
  exact hCM₂

end PropertiesCircuitType1

section PropertiesCircuitType2

variable {M₁ M₂ : Matroid α} {C : Set α}

/-- Circuit of type 2 is a circuit in `M₂` -/
lemma TwoSumCircuitType2.circuit_M₂ (hC : TwoSumCircuitType2 M₁ M₂ C) : M₂.Circuit C :=
  hC.left

/-- Circuit of type 2 is disjoint with `M₁.E ∩ M₂.E` -/
lemma TwoSumCircuitType2.disjoint_inter (hC : TwoSumCircuitType2 M₁ M₂ C) : C ⫗ M₁.E ∩ M₂.E :=
  hC.right

/-- Circuit of type 2 lies in `M₁.E ∪ M₂.E` -/
lemma TwoSumCircuitType2.subset_union (hC : TwoSumCircuitType2 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  Set.subset_union_of_subset_right hC.circuit_M₂.subset_ground M₁.E

/-- Circuit of type 2 lies in ground set of `M₁ ⊕₂ M₂` -/
lemma TwoSumCircuitType2.subset_ground (hC : TwoSumCircuitType2 M₁ M₂ C) : C ⊆ twoSumGround M₁ M₂ :=
  Set.subset_diff.← ⟨hC.subset_union, hC.disjoint_inter⟩

/-- Circuit of type 2 lies in `M₂.E \ (M₁.E ∩ M₂.E)` -/
lemma TwoSumCircuitType2.subset_M₂_diff_inter (hC : TwoSumCircuitType2 M₁ M₂ C) : C ⊆ M₂.E \ (M₁.E ∩ M₂.E) :=
  Set.subset_diff.← ⟨hC.circuit_M₂.subset_ground, hC.disjoint_inter⟩

/-- Circuit of type 2 is disjoint with `M₁.E` -/
lemma TwoSumCircuitType2.disjoint_M₁ (hC : TwoSumCircuitType2 M₁ M₂ C) : C ⫗ M₁.E := by
  have hMM := twoSum_disjoint_grounds_diff_inter M₁ M₂
  have hCM₁ := (Set.disjoint_of_subset_right hC.subset_M₂_diff_inter hMM).symm
  have hCM₁ := Set.disjoint_union_right.← ⟨hCM₁, hC.disjoint_inter⟩
  rw [Set.diff_union_of_subset Set.inter_subset_left] at hCM₁
  exact hCM₁

end PropertiesCircuitType2

section PropertiesCircuitType3

variable {M₁ M₂ : Matroid α} {C : Set α}

/-- Circuit of type 3 yields a circuit in `M₁` after intersecting it with `M₁.E` and adding `M₁.E ∩ M₂.E` -/
def TwoSumCircuitType3.to_circuit_M₁ (hC : TwoSumCircuitType3 M₁ M₂ C) : M₁.Circuit ((C ∩ M₁.E) ∪ (M₁.E ∩ M₂.E)) :=
  hC.left

/-- Circuit of type 3 yields a circuit in `M₂` after intersecting it with `M₁.E` and adding `M₁.E ∩ M₂.E` -/
def TwoSumCircuitType3.to_circuit_M₂ (hC : TwoSumCircuitType3 M₁ M₂ C) : M₂.Circuit ((C ∩ M₂.E) ∪ (M₁.E ∩ M₂.E)) :=
  hC.right.left

/-- Circuit of type 3 is subset of ground set of `M₁ ⊕₂ M₂` -/
def TwoSumCircuitType3.subset_ground (hC : TwoSumCircuitType3 M₁ M₂ C) : C ⊆ twoSumGround M₁ M₂ :=
  hC.right.right

/-- Circuit of type 3 lies in `M₁.E ∪ M₂.E` -/
lemma TwoSumCircuitType3.subset_union (hC : TwoSumCircuitType3 M₁ M₂ C) : C ⊆ M₁.E ∪ M₂.E :=
  sub_union_diff_sub_union hC.subset_ground

/-- Circuit of type 3 is disjoint with `M₁.E ∩ M₂.E` -/
lemma TwoSumCircuitType3.disjoint_inter (hC : TwoSumCircuitType3 M₁ M₂ C) : C ⫗ M₁.E ∩ M₂.E :=
  Set.disjoint_of_subset_left hC.subset_ground (twoSumGround_disjoint_inter M₁ M₂)

/-- Circuit of type 3 intersected with `M₁.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma TwoSumCircuitType3.disjoint_inter_M₁_inter (hC : TwoSumCircuitType3 M₁ M₂ C) : C ∩ M₁.E ⫗ M₁.E ∩ M₂.E :=
  hC.disjoint_inter.inter_left M₁.E

/-- Circuit of type 3 intersected with `M₂.E` is disjoint with `M₁.E ∩ M₂.E` -/
lemma TwoSumCircuitType3.disjoint_inter_M₂_inter (hC : TwoSumCircuitType3 M₁ M₂ C) : C ∩ M₂.E ⫗ M₁.E ∩ M₂.E :=
  hC.disjoint_inter.inter_left M₂.E

/-- Circuit of type 3 has nonempty intersection with `M₁.E` -/
lemma TwoSumCircuitType3.inter_M₁_nonempty (hC : TwoSumCircuitType3 M₁ M₂ C) (assumptions : TwoSumAssumptions M₁ M₂) :
    (C ∩ M₁.E).Nonempty := by
  by_contra! hCM₁
  have hM₁ := hC.to_circuit_M₁
  have ⟨p, hp⟩ := assumptions.inter_singleton
  rw [hCM₁, Set.empty_union, hp, ←Matroid.loop_iff_circuit M₁] at hM₁
  have hpM₁ := assumptions.inter_singleton_not_loop_M₁ hp
  exact hpM₁ hM₁

/-- Circuit of type 3 has nonempty intersection with `M₂.E` -/
lemma TwoSumCircuitType3.inter_M₂_nonempty (hC : TwoSumCircuitType3 M₁ M₂ C) (assumptions : TwoSumAssumptions M₁ M₂) :
    (C ∩ M₂.E).Nonempty := by
  by_contra! hCM₂empty
  have hCM₂ := hC.to_circuit_M₂
  have ⟨p, hp⟩ := assumptions.inter_singleton
  rw [hCM₂empty, Set.empty_union, hp, ←Matroid.loop_iff_circuit M₂] at hCM₂
  exact assumptions.inter_singleton_not_loop_M₂ hp hCM₂

end PropertiesCircuitType3

section PropertiesCircuitTypePairs1

/-- Circuit of type 1 is not a strict subset of any circuit of type 1 -/
lemma TwoSumCircuitType1.not_ssubset_circuit_type_1 {M₁ M₂ : Matroid α} {C C' : Set α}
    (hC : TwoSumCircuitType1 M₁ M₂ C) (hC' : TwoSumCircuitType1 M₁ M₂ C') :
    ¬(C ⊂ C') :=
  hC.circuit_M₁.not_ssubset_circuit hC'.circuit_M₁

/-- Circuit of type 1 is disjoint with any circuit of type 2 -/
lemma TwoSumCircuitType1.disjoint_circuit_type_2 {M₁ M₂ : Matroid α} {C₁ C₂ : Set α}
    (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) :
    C₁ ⫗ C₂ := by
  have hC₁M₁ := hC₁.subset_M₁_diff_inter
  have hC₂M₂ := hC₂.subset_M₂_diff_inter
  have hMM := twoSum_disjoint_grounds_diff_inter M₁ M₂
  exact Set.disjoint_of_subset hC₁M₁ hC₂M₂ hMM

/-- Circuit of type 1 is not a strict subset of any circuit of type 2 -/
lemma TwoSumCircuitType1.not_ssubset_circuit_type_2 {M₁ M₂ : Matroid α} {C₁ C₂ : Set α}
    (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) :
    ¬(C₁ ⊂ C₂) :=
  disjoint_nonempty_not_ssubset (hC₁.disjoint_circuit_type_2 hC₂) hC₁.circuit_M₁.nonempty

/-- Circuit of type 1 is not a strict subset of any circuit of type 3 -/
lemma TwoSumCircuitType1.not_ssubset_circuit_type_3 {M₁ M₂ : Matroid α} {C₁ C₃ : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) (hC₃ : TwoSumCircuitType3 M₁ M₂ C₃) :
    ¬(C₁ ⊂ C₃) :=
  fun hCC =>
    hC₁.circuit_M₁.not_ssubset_circuit hC₃.to_circuit_M₁
      (Set.ssubset_of_ssubset_of_subset (ssubset_union_disjoint_nonempty hC₁.disjoint_inter assumptions.inter_nonempty)
        (Set.union_subset_union_left (M₁.E ∩ M₂.E) (Set.subset_inter hCC.left hC₁.circuit_M₁.subset_ground)))

/-- Circuit of type 1 is not a strict subset of any other circuit -/
lemma TwoSumCircuitType1.not_ssubset_circuit {M₁ M₂ : Matroid α} {C₁ C : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) (hC : TwoSumCircuitPred M₁ M₂ C) :
    ¬(C₁ ⊂ C) := by
  cases hC with
  | inl hC => exact hC₁.not_ssubset_circuit_type_1 hC
  | inr hC => cases hC with
    | inl hC => exact hC₁.not_ssubset_circuit_type_2 hC
    | inr hC => exact hC₁.not_ssubset_circuit_type_3 assumptions hC

end PropertiesCircuitTypePairs1

section PropertiesCircuitTypePairs2

variable {M₁ M₂ : Matroid α}

/-- Circuits of type 2 are disjoint with circuits of type 1 -/
lemma TwoSumCircuitType2.disjoint_circuitType1 {C₁ C₂ : Set α}
    (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) :
    C₂ ⫗ C₁ :=
  (hC₁.disjoint_circuit_type_2 hC₂).symm

/-- Circuit of type 2 is not a strict subset of any circuit of type 1 -/
lemma TwoSumCircuitType2.not_ssubset_circuitType1 {C₁ C₂ : Set α}
    (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) :
    ¬(C₂ ⊂ C₁) :=
  disjoint_nonempty_not_ssubset (hC₂.disjoint_circuitType1 hC₁) hC₂.circuit_M₂.nonempty

/-- Circuit of type 2 is not a strict subset of any circuit of type 2 -/
lemma TwoSumCircuitType2.not_ssubset_circuitType2 {C C' : Set α}
    (hC : TwoSumCircuitType2 M₁ M₂ C) (hC' : TwoSumCircuitType2 M₁ M₂ C') :
    ¬(C ⊂ C') :=
  hC.circuit_M₂.not_ssubset_circuit hC'.circuit_M₂

/-- Circuit of type 2 is not a strict subset of any circuit of type 3 -/
lemma TwoSumAssumptions.circuitType2_not_ssubset_circuitType3 {C₂ C₃ : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) (hC₃ : TwoSumCircuitType3 M₁ M₂ C₃) :
    ¬(C₂ ⊂ C₃) :=
  fun hCC =>
    hC₂.circuit_M₂.not_ssubset_circuit hC₃.to_circuit_M₂
      (Set.ssubset_of_ssubset_of_subset (ssubset_union_disjoint_nonempty hC₂.disjoint_inter assumptions.inter_nonempty)
        (Set.union_subset_union_left (M₁.E ∩ M₂.E) (Set.subset_inter hCC.left hC₂.circuit_M₂.subset_ground)))

/-- Circuit of type 2 is not a strict subset of any other circuit -/
lemma TwoSumAssumptions.circuitType2_not_ssubset {C₂ C : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) (hC : TwoSumCircuitPred M₁ M₂ C) :
    ¬(C₂ ⊂ C) := by
  cases hC with
  | inl hC => exact hC₂.not_ssubset_circuitType1 hC
  | inr hC => cases hC with
    | inl hC => exact hC₂.not_ssubset_circuitType2 hC
    | inr hC => exact assumptions.circuitType2_not_ssubset_circuitType3 hC₂ hC

end PropertiesCircuitTypePairs2

section PropertiesCircuitTypePairs3

variable {M₁ M₂ : Matroid α}

/-- Circuit of type 3 is not a strict subset of any circuit of type 1 -/
lemma TwoSumAssumptions.circuitType3_not_ssubset_circuitType1 {C₁ C₃ : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₃ : TwoSumCircuitType3 M₁ M₂ C₃) (hC₁ : TwoSumCircuitType1 M₁ M₂ C₁) :
    ¬(C₃ ⊂ C₁) :=
  nonempty_inter_not_ssubset_empty_inter (hC₃.inter_M₂_nonempty assumptions) hC₁.disjoint_M₂.inter_eq

/-- Circuit of type 3 is not a strict subset of any circuit of type 2 -/
lemma TwoSumAssumptions.circuitType3_not_ssubset_circuitType2 {C₂ C₃ : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₃ : TwoSumCircuitType3 M₁ M₂ C₃) (hC₂ : TwoSumCircuitType2 M₁ M₂ C₂) :
    ¬(C₃ ⊂ C₂) :=
  nonempty_inter_not_ssubset_empty_inter (hC₃.inter_M₁_nonempty assumptions) hC₂.disjoint_M₁.inter_eq

/-- Circuit of type 3 is not a strict subset of any circuit of type 3 -/
lemma TwoSumCircuitType3.not_ssubset_circuitType3 {C C' : Set α}
    (hC : TwoSumCircuitType3 M₁ M₂ C) (hC' : TwoSumCircuitType3 M₁ M₂ C') :
    ¬(C ⊂ C') := by
  intro ⟨hCC', hnCC'⟩
  have M₁_circ_nssub := Set.ssubset_def ▸ hC.to_circuit_M₁.not_ssubset_circuit hC'.to_circuit_M₁
  have M₂_circ_nssub := Set.ssubset_def ▸ hC.to_circuit_M₂.not_ssubset_circuit hC'.to_circuit_M₂
  push_neg at M₁_circ_nssub
  push_neg at M₂_circ_nssub
  have M₁_circ_sub := (union_subset_union_iff hC'.disjoint_inter_M₁_inter hC.disjoint_inter_M₁_inter).→
    (M₁_circ_nssub (Set.union_subset_union_left (M₁.E ∩ M₂.E) (Set.inter_subset_inter_left M₁.E hCC')))
  have M₂_circ_sub := (union_subset_union_iff hC'.disjoint_inter_M₂_inter hC.disjoint_inter_M₂_inter).→
    (M₂_circ_nssub (Set.union_subset_union_left (M₁.E ∩ M₂.E) (Set.inter_subset_inter_left M₂.E hCC')))
  exact hnCC' (hC.subset_union.parts_eq ▸ hC'.subset_union.parts_eq ▸ Set.union_subset_union M₁_circ_sub M₂_circ_sub)

/-- Circuit of type 3 is not a strict subset of any other circuit -/
lemma TwoSumAssumptions.circuitType3_not_ssubset_circuit {C₃ C : Set α}
    (assumptions : TwoSumAssumptions M₁ M₂) (hC₃ : TwoSumCircuitType3 M₁ M₂ C₃) (hC : TwoSumCircuitPred M₁ M₂ C) :
    ¬(C₃ ⊂ C) := by
  cases hC with
  | inl hC => exact assumptions.circuitType3_not_ssubset_circuitType1 hC₃ hC
  | inr hC => cases hC with
    | inl hC => exact assumptions.circuitType3_not_ssubset_circuitType2 hC₃ hC
    | inr hC => exact hC₃.not_ssubset_circuitType3 hC

end PropertiesCircuitTypePairs3

section PropertiesCircuitPred

/- Start of proof attempt -/
lemma round1_h3 (M₁ M₂ : Matroid α)
  (assumptions : TwoSumAssumptions M₁ M₂):
  ¬ (TwoSumCircuitType3 M₁ M₂ ∅) := by
  intro h
  have h5 := TwoSumCircuitType3.inter_M₁_nonempty h assumptions
  simp at h5

/-- In definition of 2-sum, empty set is not a circuit -/
theorem TwoSumAssumptions.twoSumCircuitPred_notCircuitEmpty {M₁ M₂ : Matroid α} (assumptions : TwoSumAssumptions M₁ M₂) :
    (TwoSumCircuitPred M₁ M₂).NotCircuitEmpty  := by

  have h1 : ¬ (TwoSumCircuitType1 M₁ M₂ ∅) := by
    intro h
    rcases h with ⟨h11, _⟩
    exfalso
    exact?
  have h2 : ¬ (TwoSumCircuitType2 M₁ M₂ ∅) := by
    intro h
    rcases h with ⟨h21, _⟩
    exfalso
    exact?
  have h3 : ¬ (TwoSumCircuitType3 M₁ M₂ ∅) := by
    exact round1_h3 M₁ M₂ assumptions
  intro h4
  rcases h4 with (h4 | h4 | h4)
  · exact h1 h4
  · exact h2 h4
  · exact h3 h4
