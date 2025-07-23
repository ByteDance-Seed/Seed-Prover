-- In FLT/FLT/Mathlib/LinearAlgebra/Span/Defs.lean

import Mathlib.LinearAlgebra.Span.Defs

open Pointwise

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {p p' : Submodule R M}

variable {P : M → Prop}

namespace Submodule

@[simp high]
lemma forall_mem_sup : (∀ x ∈ p ⊔ p', P x) ↔ (∀ x₁ ∈ p, ∀ x₂ ∈ p', P (x₁ + x₂)) := by
  simp [mem_sup]
  aesop

/- Start of proof attempt -/
lemma round1_exists_mem_sup_forward (h : ∃ x ∈ p ⊔ p', P x) : ∃ x₁ ∈ p, ∃ x₂ ∈ p', P (x₁ + x₂) := by
  rcases h with ⟨x, hx, hPx⟩
  rcases Submodule.mem_sup.mp hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  refine ⟨x₁, hx₁, x₂, hx₂, ?_⟩
  simpa using hPx

lemma round1_exists_mem_sup_backward (h : ∃ x₁ ∈ p, ∃ x₂ ∈ p', P (x₁ + x₂)) : ∃ x ∈ p ⊔ p', P x := by
  rcases h with ⟨x₁, hx₁, x₂, hx₂, hPx⟩
  refine ⟨x₁ + x₂, ?_, hPx⟩
  exact Submodule.add_mem_sup hx₁ hx₂

theorem exists_mem_sup : (∃ x ∈ p ⊔ p', P x) ↔ (∃ x₁ ∈ p, ∃ x₂ ∈ p', P (x₁ + x₂))  := by

  constructor
  · exact round1_exists_mem_sup_forward
  · exact round1_exists_mem_sup_backward
