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

/- Start of proof attempt -/
lemma round1_symm_M2fin (assumptions : TwoSumAssumptions M₁ M₂) : M₂.Finite := by
  exact assumptions.M₂fin

lemma round1_symm_M1fin (assumptions : TwoSumAssumptions M₁ M₂) : M₁.Finite := by
  exact assumptions.M₁fin

lemma round1_symm_M2card (assumptions : TwoSumAssumptions M₁ M₂) : M₂.E.encard ≥ 2 := by
  exact assumptions.M₂card

lemma round1_symm_M1card (assumptions : TwoSumAssumptions M₁ M₂) : M₁.E.encard ≥ 2 := by
  exact assumptions.M₁card

lemma round1_symm_interSingleton (assumptions : TwoSumAssumptions M₁ M₂) : (M₂.E ∩ M₁.E).encard = 1 := by
  have h1 : M₂.E ∩ M₁.E = M₁.E ∩ M₂.E := by
    ext x
    simp [and_comm]
  rw [h1]
  exact assumptions.interSingleton

lemma round1_symm_M2sep (assumptions : TwoSumAssumptions M₁ M₂) : ¬M₂.Separator (M₂.E ∩ M₁.E) := by
  have h2 : M₂.E ∩ M₁.E = M₁.E ∩ M₂.E := by
    ext x
    simp [and_comm]
  rw [h2]
  exact assumptions.M₂sep

lemma round1_symm_M1sep (assumptions : TwoSumAssumptions M₁ M₂) : ¬M₁.Separator (M₂.E ∩ M₁.E) := by
  have h3 : M₂.E ∩ M₁.E = M₁.E ∩ M₂.E := by
    ext x
    simp [and_comm]
  rw [h3]
  exact assumptions.M₁sep

/-- 2-sum assumptions are symmetric -/
theorem TwoSumAssumptions.symm (assumptions : TwoSumAssumptions M₁ M₂) :
    TwoSumAssumptions M₂ M₁  := by

  constructor
  · exact round1_symm_M2fin assumptions
  · exact round1_symm_M1fin assumptions
  · exact round1_symm_M2card assumptions
  · exact round1_symm_M1card assumptions
  · exact round1_symm_interSingleton assumptions
  · exact round1_symm_M2sep assumptions
  · exact round1_symm_M1sep assumptions
