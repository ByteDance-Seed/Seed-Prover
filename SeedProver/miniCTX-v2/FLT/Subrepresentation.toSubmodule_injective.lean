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

/- Start of proof attempt -/
lemma round1_toSubmodule_injective (ρ : Representation A G W) : 
  Function.Injective (toSubmodule : Subrepresentation ρ → Submodule A W) := by
  intro x y h
  have h1 : x.toSubmodule = y.toSubmodule := h
  have h2 : x = y := by
    cases x
    cases y
    simp_all
    <;> aesop
  exact h2

theorem toSubmodule_injective : Function.Injective (toSubmodule : Subrepresentation ρ → Submodule A W)  := by

  exact round1_toSubmodule_injective ρ
