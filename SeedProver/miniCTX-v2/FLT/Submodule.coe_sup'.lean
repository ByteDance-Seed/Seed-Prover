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

@[simp high]
lemma exists_mem_sup : (∃ x ∈ p ⊔ p', P x) ↔ (∃ x₁ ∈ p, ∃ x₂ ∈ p', P (x₁ + x₂)) := by
  simp [mem_sup]

/- Start of proof attempt -/
lemma round1_coe_sup' : ↑(p ⊔ p') = (p : Set M) + (p' : Set M)  := by
  ext x
  simp [Set.mem_add, Submodule.mem_sup]
  <;> aesop

theorem coe_sup' : ↑(p ⊔ p') = (p : Set M) + (p' : Set M)  := by

  exact round1_coe_sup'
