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

/- Start of proof attempt -/
lemma round1_TwoSumCircuitType1_disjoint_inter (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⫗ M₁.E ∩ M₂.E := by
  exact hC.right

/-- Circuit of type 1 is disjoint with `M₁.E ∩ M₂.E` -/
theorem TwoSumCircuitType1.disjoint_inter (hC : TwoSumCircuitType1 M₁ M₂ C) : C ⫗ M₁.E ∩ M₂.E  := by

  exact round1_TwoSumCircuitType1_disjoint_inter hC
