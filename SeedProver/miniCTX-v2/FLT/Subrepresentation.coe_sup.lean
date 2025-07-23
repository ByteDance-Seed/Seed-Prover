-- In FLT/FLT/Deformations/RepresentationTheory/Subrepresentation.lean

import Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.LinearAlgebra.Span.Defs

open Pointwise

universe u

variable {A : Type*} [CommRing A]

variable {G : Type*} [Group G]

variable {W : Type*} [AddCommMonoid W] [Module A W]

variable {ρ : Representation A G W}

variable (ρ) in
structure Subrepresentation where
  toSubmodule : Submodule A W
  apply_mem_toSubmodule (g : G) ⦃v : W⦄ : v ∈ toSubmodule → ρ g v ∈ toSubmodule

namespace Subrepresentation

lemma toSubmodule_injective : Function.Injective (toSubmodule : Subrepresentation ρ → Submodule A W) := by
  rintro ⟨_,_⟩
  congr!

instance : SetLike (Subrepresentation ρ) W where
  coe ρ' := ρ'.toSubmodule
  coe_injective' := SetLike.coe_injective.comp toSubmodule_injective

def toRepresentation (ρ' : Subrepresentation ρ): Representation A G ρ'.toSubmodule where
  toFun g := (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

instance : Max (Subrepresentation ρ) where
  max ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊔ ρ₂.toSubmodule) <| by
      simp only [Submodule.forall_mem_sup, map_add]
      intro g x₁ hx₁ x₂ hx₂
      exact Submodule.mem_sup.mpr
        ⟨ρ g x₁, ρ₁.apply_mem_toSubmodule g hx₁, ρ g x₂, ρ₂.apply_mem_toSubmodule g hx₂, rfl⟩

instance : Min (Subrepresentation ρ) where
  min ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊓ ρ₂.toSubmodule) <| by
      simp only [Submodule.mem_inf, and_imp]
      rintro g x hx₁ hx₂
      exact ⟨ρ₁.apply_mem_toSubmodule g hx₁, ρ₂.apply_mem_toSubmodule g hx₂⟩

/- Start of proof attempt -/
lemma round1_coe_sup (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : Set W) := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_add]
  constructor
  · -- Assume x ∈ (ρ₁ ⊔ ρ₂).toSubmodule
    intro h1
    have h2 : x ∈ (ρ₁ ⊔ ρ₂).toSubmodule := h1
    have h4 : (ρ₁ ⊔ ρ₂).toSubmodule = ρ₁.toSubmodule ⊔ ρ₂.toSubmodule := rfl
    rw [h4] at h2
    rcases Submodule.mem_sup.mp h2 with ⟨y, hy, z, hz, h_eq⟩
    refine ⟨y, hy, z, hz, h_eq⟩
  · -- Assume ∃ (y : W), y ∈ ρ₁.toSubmodule ∧ ∃ (z : W), z ∈ ρ₂.toSubmodule ∧ y + z = x
    rintro ⟨y, hy, z, hz, h_eq⟩
    have h2 : y ∈ ρ₁.toSubmodule := hy
    have h3 : z ∈ ρ₂.toSubmodule := hz
    have h4 : y + z ∈ ρ₁.toSubmodule ⊔ ρ₂.toSubmodule := by
      exact Submodule.mem_sup.mpr ⟨y, h2, z, h3, rfl⟩
    have h5 : (ρ₁ ⊔ ρ₂).toSubmodule = ρ₁.toSubmodule ⊔ ρ₂.toSubmodule := rfl
    have h6 : y + z ∈ (ρ₁ ⊔ ρ₂).toSubmodule := by
      rw [h5]
      exact h4
    have h7 : x = y + z := by
      rw [h_eq]
      <;> simp
    rw [h7]
    exact h6

theorem coe_sup (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : Set W)  := by

  exact round1_coe_sup ρ₁ ρ₂
