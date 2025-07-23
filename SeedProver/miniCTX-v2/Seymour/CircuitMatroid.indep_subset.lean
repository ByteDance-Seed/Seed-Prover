-- In Seymour/Seymour/Matroid/Constructors/CircuitMatroid.lean

import Mathlib.Order.RelClasses
import Mathlib.Data.Matroid.IndepAxioms

import Seymour.Basic
import Seymour.Matroid.Notions.IndepAxioms
import Seymour.Matroid.Notions.CircuitAxioms
import Seymour.Matroid.Notions.Circuit

/-- Matroid defined by circuit axioms. -/
structure CircuitMatroid (α : Type) where
  /-- The ground set -/
  E : Set α
  /-- The circuit predicate -/
  CircuitPred : CircuitPredicate α
  /-- Empty set is not a circuit -/
  not_circuit_empty : CircuitPred.NotCircuitEmpty
  /-- No circuit is a subset of another circuit -/
  circuit_not_ssubset : CircuitPred.CircuitNotSsubset
  /-- Condition (C3) from Bruhn et al. -/
  circuit_c3 : CircuitPred.BruhnC3
  /-- Corresponding family of independent sets satisfies the maximal subset property -/
  circuit_maximal : CircuitPred.CircuitMaximal E
  /-- Every circuit is a subset of the ground set -/
  subset_ground : CircuitPred.SubsetGround E -- question: unused?

variable {α : Type}

/-- Corresponding independence predicate of circuit matroid. -/
def CircuitMatroid.IndepPred (M : CircuitMatroid α) :
    IndepPredicate α :=
  M.CircuitPred.toIndepPredicate M.E

/-- Corresponding independence predicate of circuit matroid satisfies (I1): empty set is independent. -/
lemma CircuitMatroid.indep_empty (M : CircuitMatroid α) :
    M.IndepPred.IndepEmpty :=
  CircuitPredicate.toIndepPredicate_indepEmpty M.not_circuit_empty M.E

/- Start of proof attempt -/
lemma round1_indep_subset (M : CircuitMatroid α) :
    M.IndepPred.IndepSubset := by
  intro I J h1 h2
  have h11 : J ⊆ M.E := h1.1
  have h12 : ∀ C ⊆ J, ¬M.CircuitPred C := h1.2
  have h13 : I ⊆ M.E := by
    exact Set.Subset.trans h2 h11
  have h14 : ∀ C ⊆ I, ¬M.CircuitPred C := by
    intro C hC
    have hC1 : C ⊆ J := by
      exact Set.Subset.trans hC h2
    exact h12 C hC1
  exact ⟨h13, h14⟩

/-- Corresponding independence predicate of circuit matroid satisfies (I2): subsets of independent sets are independent. -/
theorem CircuitMatroid.indep_subset (M : CircuitMatroid α) :
    M.IndepPred.IndepSubset  := by

  exact round1_indep_subset M
