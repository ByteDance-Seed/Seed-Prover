-- In Seymour/Seymour/Matroid/Notions/CircuitAxioms.lean

import Mathlib.Order.RelClasses
import Mathlib.Data.Matroid.Basic

import Seymour.Basic
import Seymour.Matroid.Notions.IndepAxioms

/-- Circuit predicate, defines which sets are circuits. -/
abbrev CircuitPredicate (α : Type) := Set α → Prop

variable {α : Type}

section ValidFamily

/-- Family of circuits satisfying assumptions of circuit axiom (C3) from Bruhn et al. -/
structure ValidFamily (P : CircuitPredicate α) (X : Set α) where
  F : X.Elem → Set α
  hPF : ∀ x : X.Elem, P (F x)
  hF : ∀ x y : X.Elem, x.val ∈ F y ↔ x = y -- `F y` may nevertheless contain multiple elements of `Xᶜ`

/-- Shorthand for union of sets in `ValidFamily` -/
abbrev ValidFamily.union {P : CircuitPredicate α} {X : Set α} (F : ValidFamily P X) : Set α :=
  Set.iUnion F.F

-- question: unused API?
lemma ValidFamily.mem_of_elem {P : CircuitPredicate α} {X : Set α} (F : ValidFamily P X) (x : X.Elem) :
    x.val ∈ F.F x := by
  rw [F.hF]

-- question: unused API?
lemma ValidFamily.outside {P : CircuitPredicate α} {C X : Set α} {F : ValidFamily P X} {z : α} (hzCF : z ∈ C \ F.union) :
    z ∉ X := by
  intro hz
  have := F.hF ⟨z, hz⟩ ⟨z, hz⟩
  simp_all

end ValidFamily

section CircuitAxioms

/-- Circuit predicate `P` defines independence predicate: independent sets are all non-circuits. -/
def CircuitPredicate.toIndepPredicate (P : CircuitPredicate α) (E : Set α) : IndepPredicate α :=
  fun I : Set α => I ⊆ E ∧ ∀ C : Set α, C ⊆ I → ¬(P C)

/-- Axiom (C1): empty set is not a circuit. -/
def CircuitPredicate.NotCircuitEmpty (P : CircuitPredicate α) : Prop :=
  ¬(P ∅)
alias CircuitPredicate.BruhnC1 := CircuitPredicate.NotCircuitEmpty

/-- Axiom (C2): no circuit is a subset of another circuit. -/
def CircuitPredicate.CircuitNotSsubset (P : CircuitPredicate α) : Prop :=
  ∀ C C' : Set α, P C → P C' → ¬(C' ⊂ C)  -- todo: swap to ¬C ⊂ C'
alias CircuitPredicate.BruhnC2 := CircuitPredicate.CircuitNotSsubset

/-- Axiom (C3) from Bruhn et al. -/
def CircuitPredicate.BruhnC3 (P : CircuitPredicate α) : Prop :=
  ∀ X C : Set α, ∀ F : ValidFamily P X, ∀ z ∈ C \ F.union, ∃ C' : Set α, P C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ F.union) \ X

/-- Axiom (CM) from Bruhn et al.: set of all independent sets has the maximal subset property. -/
def CircuitPredicate.CircuitMaximal (P : CircuitPredicate α) (E : Set α) : Prop :=
  ∀ X : Set α, X ⊆ E → Matroid.ExistsMaximalSubsetProperty (P.toIndepPredicate E) X
alias CircuitPredicate.BruhnCM := CircuitPredicate.CircuitMaximal

/-- Every circuit is a subset of the ground set. -/
def CircuitPredicate.SubsetGround (P : CircuitPredicate α) (E : Set α) : Prop :=
  ∀ C : Set α, P C → C ⊆ E
alias CircuitPredicate.BruhnCE := CircuitPredicate.SubsetGround

/-- Strong circuit elimination axiom: if `C₁` and `C₂` are circuits with `e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`,
    then there is circuit `C₃` such that `f ∈ C₃ ⊆ C₁ ∪ C₂ \ {e}`. -/
def CircuitPredicate.StrongCircuitElim (P : CircuitPredicate α) : Prop :=
  ∀ C₁ C₂ : Set α, ∀ e f, P C₁ ∧ P C₂ ∧ e ∈ C₁ ∩ C₂ ∧ f ∈ C₁ \ C₂ → ∃ C₃, P C₃ ∧ f ∈ C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e}

/-- Weak circuit elimination axiom: if `C₁` and `C₂` are distinct circuits and `e ∈ C₁ ∩ C₂`,
    then there is circuit `C₃` such that `C₃ ⊆ C₁ ∪ C₂ \ {e}`. -/
def CircuitPredicate.WeakCircuitElim (P : CircuitPredicate α) : Prop :=
  ∀ C₁ C₂ : Set α, C₁ ≠ C₂ → P C₁ → P C₂ → ∀ e ∈ C₁ ∩ C₂, ∃ C₃, P C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e}

end CircuitAxioms

section CircuitAxiomRelations

/-- Alternative formulation of axiom (C2). -/
lemma CircuitPredicate.circuit_not_ssubset_iff (P : CircuitPredicate α) :
    P.CircuitNotSsubset ↔ ∀ C C' : Set α, P C → P C' → C' ⊆ C → C ⊆ C' := by
  constructor
  · intro hP C C' hC hC' hCC'
    apply hP C C' hC at hC'
    rw [ssubset_iff_subset_ne] at hC'
    push_neg at hC'
    exact (hC' hCC').symm.subset
  · intro hP C C' hC hC' hCC'
    apply hP C C' hC at hC'
    rw [ssubset_iff_subset_ne] at hCC'
    exact hCC'.right.symm (Set.Subset.antisymm (hC' hCC'.left) hCC'.left)

/- Start of proof attempt -/
lemma round1_main (P : CircuitPredicate α) (h : P.BruhnC3) :
    P.StrongCircuitElim := by
  intro C₁ C₂ e f h1
  rcases h1 with ⟨h11, h12, h13, h14⟩
  have h131 : e ∈ C₁ := h13.1
  have h132 : e ∈ C₂ := h13.2
  have h141 : f ∈ C₁ := h14.1
  have h142 : f ∉ C₂ := h14.2
  have hF2 : ∀ (x y : ({e} : Set α).Elem), x.val ∈ C₂ ↔ x = y := by
    intro x y
    have hx : x.val = e := x.property
    have hy : y.val = e := y.property
    have h5 : x.val = y.val := by
      rw [hx, hy]
    have h6 : x = y := by
      apply Subtype.ext
      exact h5
    have h7 : x.val ∈ C₂ := by
      rw [hx]
      exact h132
    constructor
    · -- Assume `x.val ∈ C₂`, we need to show `x = y`
      intro _
      exact h6
    · -- Assume `x = y`, we need to show `x.val ∈ C₂`
      intro _
      exact h7
  have hF1 : ∀ (x : ({e} : Set α).Elem), P (C₂) := by
    intro x
    exact h12
  set F : ValidFamily P {e} := {
    F := fun _ => C₂,
    hPF := by
      intro x
      exact h12,
    hF := by
      intro x y
      exact hF2 x y
  }
  have hF_union : F.union = C₂ := by
    simp [ValidFamily.union]
    <;> aesop
  have hz : f ∈ C₁ \ F.union := by
    rw [hF_union]
    exact ⟨h141, h142⟩
  have h7 := h {e} C₁ F f hz
  obtain ⟨C', hC1, hC2, hC3⟩ := h7
  have h9 : C' ⊆ (C₁ ∪ C₂) \ {e} := by
    rw [hF_union] at hC3
    simpa using hC3
  refine ⟨C', hC1, hC2, h9⟩

/-- Axiom (C3) implies strong circuit elimination. -/
theorem CircuitPredicate.C3_strong_circuit_elim (P : CircuitPredicate α) :
    P.BruhnC3 → P.StrongCircuitElim  := by

  intro h
  exact round1_main P h
