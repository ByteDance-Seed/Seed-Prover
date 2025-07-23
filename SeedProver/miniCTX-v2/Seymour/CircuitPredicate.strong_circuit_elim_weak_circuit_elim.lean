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

/-- Axiom (C3) implies strong circuit elimination. -/
lemma CircuitPredicate.C3_strong_circuit_elim (P : CircuitPredicate α) :
    P.BruhnC3 → P.StrongCircuitElim := by
  intro hPC3 C₁ C₂ x z hxz
  obtain ⟨_hC₁, hC₂, hx, hz⟩ := hxz
  let F : ValidFamily P {x} :=
  ⟨
    (fun _ => C₂),
    (fun _ => hC₂),
    (by simpa using Set.mem_of_mem_inter_right hx)
  ⟩
  specialize hPC3 {x} C₁ F
  simp only [ValidFamily.union, Set.iUnion_coe_set, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left] at hPC3
  specialize hPC3 z hz
  exact hPC3

/- Start of proof attempt -/
lemma round1_h1 (P : CircuitPredicate α)
  (h : P.StrongCircuitElim)
  (C₁ C₂ : Set α)
  (hne : C₁ ≠ C₂)
  (hC₁ : P C₁)
  (hC₂ : P C₂)
  (e : α)
  (he : e ∈ C₁ ∩ C₂):
  ¬(C₁ ⊆ C₂) ∨ ¬(C₂ ⊆ C₁) := by
  by_contra h1
  push_neg at h1
  have h11 : C₁ ⊆ C₂ := h1.1
  have h12 : C₂ ⊆ C₁ := h1.2
  have h13 : C₁ = C₂ := Set.Subset.antisymm h11 h12
  contradiction

lemma round1_case1 (P : CircuitPredicate α)
  (h : P.StrongCircuitElim)
  (C₁ C₂ : Set α)
  (hC₁ : P C₁)
  (hC₂ : P C₂)
  (e : α)
  (he : e ∈ C₁ ∩ C₂)
  (h11 : ∃ f, f ∈ C₁ ∧ f ∉ C₂):
  ∃ C₃, P C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e} := by
  rcases h11 with ⟨f, hf1, hf2⟩
  have h111 : f ∈ C₁ \ C₂ := ⟨hf1, hf2⟩
  have h6 := h C₁ C₂ e f ⟨hC₁, hC₂, he, h111⟩
  rcases h6 with ⟨C₃, hC₃1, _hf_in_C₃, hC₃2⟩
  refine ⟨C₃, ⟨hC₃1, hC₃2⟩⟩

lemma round1_case2 (P : CircuitPredicate α)
  (h : P.StrongCircuitElim)
  (C₁ C₂ : Set α)
  (hC₁ : P C₁)
  (hC₂ : P C₂)
  (e : α)
  (he : e ∈ C₁ ∩ C₂)
  (h12 : ∃ f, f ∈ C₂ ∧ f ∉ C₁):
  ∃ C₃, P C₃ ∧ C₃ ⊆ (C₁ ∪ C₂) \ {e} := by
  rcases h12 with ⟨f, hf1, hf2⟩
  have h121 : f ∈ C₂ \ C₁ := ⟨hf1, hf2⟩
  have he1 : e ∈ C₂ ∩ C₁ := by
    have he2 : e ∈ C₁ ∩ C₂ := he
    simp only [Set.mem_inter_iff] at *
    <;> tauto
  have h6 := h C₂ C₁ e f ⟨hC₂, hC₁, he1, h121⟩
  rcases h6 with ⟨C₃, hC₃1, _hf_in_C₃, hC₃2⟩
  have h4 : C₃ ⊆ (C₁ ∪ C₂) \ {e} := by
    have h5 : C₂ ∪ C₁ = C₁ ∪ C₂ := by
      ext x
      simp [Set.mem_union]
      <;> tauto
    have hC₃2' : C₃ ⊆ (C₂ ∪ C₁) \ {e} := hC₃2
    have h6 : (C₂ ∪ C₁) \ {e} = (C₁ ∪ C₂) \ {e} := by
      rw [h5]
    rw [h6] at hC₃2'
    exact hC₃2'
  refine ⟨C₃, ⟨hC₃1, h4⟩⟩

/-- Strong circuit elimination implies weak circuit elimination. -/
theorem CircuitPredicate.strong_circuit_elim_weak_circuit_elim (P : CircuitPredicate α) :
    P.StrongCircuitElim → P.WeakCircuitElim  := by

  intro h
  intro C₁ C₂ hne hC₁ hC₂ e he
  have h1 : ¬(C₁ ⊆ C₂) ∨ ¬(C₂ ⊆ C₁) := by
    exact round1_h1 P h C₁ C₂ hne hC₁ hC₂ e he
  cases h1 with
  | inl h11 =>
    have h11' : ∃ f, f ∈ C₁ ∧ f ∉ C₂ := by
      by_contra h11'
      push_neg at h11'
      have h112 : C₁ ⊆ C₂ := by
        intro x hx
        exact h11' x hx
      contradiction
    exact round1_case1 P h C₁ C₂ hC₁ hC₂ e he h11'
  | inr h12 =>
    have h12' : ∃ f, f ∈ C₂ ∧ f ∉ C₁ := by
      by_contra h12'
      push_neg at h12'
      have h122 : C₂ ⊆ C₁ := by
        intro x hx
        exact h12' x hx
      contradiction
    exact round1_case2 P h C₁ C₂ hC₁ hC₂ e he h12'
