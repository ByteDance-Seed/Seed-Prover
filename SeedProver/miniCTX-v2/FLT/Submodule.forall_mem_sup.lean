-- In FLT/FLT/Mathlib/LinearAlgebra/Span/Defs.lean

import Mathlib.LinearAlgebra.Span.Defs

open Pointwise

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {p p' : Submodule R M}

variable {P : M → Prop}

namespace Submodule

/- Start of proof attempt -/
lemma round1_forward_direction (h : ∀ x ∈ p ⊔ p', P x) : ∀ x₁ ∈ p, ∀ x₂ ∈ p', P (x₁ + x₂) := by
  intro x₁ hx₁ x₂ hx₂
  have h1 : x₁ ∈ p ⊔ p' := by
    exact Submodule.mem_sup_left hx₁
  have h2 : x₂ ∈ p ⊔ p' := by
    exact Submodule.mem_sup_right hx₂
  have h3 : x₁ + x₂ ∈ p ⊔ p' := by
    exact Submodule.add_mem (p ⊔ p') h1 h2
  exact h (x₁ + x₂) h3

lemma round1_backward_direction (h : ∀ x₁ ∈ p, ∀ x₂ ∈ p', P (x₁ + x₂)) : ∀ x ∈ p ⊔ p', P x := by
  intro x hx
  rcases Submodule.mem_sup.mp hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  have h5 := h x₁ hx₁ x₂ hx₂
  simpa using h5

theorem forall_mem_sup : (∀ x ∈ p ⊔ p', P x) ↔ (∀ x₁ ∈ p, ∀ x₂ ∈ p', P (x₁ + x₂))  := by

  constructor
  · exact round1_forward_direction
  · exact round1_backward_direction
