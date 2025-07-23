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

/- Start of proof attempt -/
lemma round1_validFamily.outside {P : CircuitPredicate α} {C X : Set α} {F : ValidFamily P X} {z : α} (hzCF : z ∈ C \ F.union) :
    z ∉ X := by
  by_contra hzX
  have h1 : ∃ (x : X.Elem), x.val = z := by
    refine ⟨⟨z, hzX⟩, rfl⟩
  obtain ⟨x, hxz⟩ := h1
  have h2 : x.val ∈ F.F x := ValidFamily.mem_of_elem F x
  have h3 : z ∈ F.F x := by
    rw [hxz] at h2
    exact h2
  have h4 : z ∈ Set.iUnion F.F := by
    refine Set.mem_iUnion.mpr ⟨x, h3⟩
  have h7 : z ∈ F.union := by simpa [ValidFamily.union] using h4
  have h5 : z ∉ F.union := hzCF.2
  contradiction

theorem ValidFamily.outside {P : CircuitPredicate α} {C X : Set α} {F : ValidFamily P X} {z : α} (hzCF : z ∈ C \ F.union) :
    z ∉ X  := by

  exact round1_validFamily.outside hzCF
