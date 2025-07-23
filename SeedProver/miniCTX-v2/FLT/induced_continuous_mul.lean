-- In FLT/FLT/Mathlib/Topology/Algebra/Monoid.lean

import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.Monoid

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [ContinuousMul G]
-- TODO: `ContinuousMulConst` would be enough but it doesn't exist, and `ContinuousConstSMul Gᵐᵒᵖ G`
-- should work but doesn't

section induced

variable {R : Type*} [τR : TopologicalSpace R]
variable {A : Type*} [SMul R A]
variable {S : Type*} [τS : TopologicalSpace S] {f : S → R} (hf : Continuous f)
variable {B : Type*} [SMul S B]

open Topology

-- note: use convert not exact to ensure typeclass inference doesn't try to find topology on B
@[to_additive]
theorem induced_continuous_smul [τA : TopologicalSpace A] [ContinuousSMul R A] (g : B →ₑ[f] A)
    (hf : Continuous f) : @ContinuousSMul S B _ _ (TopologicalSpace.induced g τA) := by
  convert IsInducing.continuousSMul (IsInducing.induced g) hf (fun {c} {x} ↦ map_smulₛₗ g c x)

/- Start of proof attempt -/
lemma round1_induced_continuous_mul [CommMonoid A] [τA : TopologicalSpace A] [ContinuousMul A]
    [CommMonoid B] (h : B →* A) :
    @ContinuousMul B (TopologicalSpace.induced h τA) _  := by
  letI : TopologicalSpace B := TopologicalSpace.induced h τA
  have h1 : Continuous h := continuous_induced_dom
  have h2 : Continuous (fun p : B × B => h p.1) := by
    have h21 : Continuous (fun p : B × B => p.1) := continuous_fst
    exact Continuous.comp h1 h21
  have h3 : Continuous (fun p : B × B => h p.2) := by
    have h31 : Continuous (fun p : B × B => p.2) := continuous_snd
    exact Continuous.comp h1 h31
  have h4 : Continuous (fun p : B × B => (h p.1, h p.2)) := Continuous.prod_mk h2 h3
  have h5 : Continuous (fun p : B × B => h p.1 * h p.2) := by
    have h51 : Continuous (fun p : A × A => p.1 * p.2) := continuous_mul
    have h52 : Continuous (fun p : B × B => (h p.1, h p.2)) := h4
    exact Continuous.comp h51 h52
  have h6 : ∀ p : B × B, h (p.1 * p.2) = h p.1 * h p.2 := by
    intro p
    exact h.map_mul p.1 p.2
  have h7 : Continuous (fun p : B × B => h (p.1 * p.2)) := by
    have h_eq : (fun p : B × B => h (p.1 * p.2)) = (fun p : B × B => h p.1 * h p.2) := by
      funext p
      exact h6 p
    rw [h_eq]
    exact h5
  have h9 : Continuous (h ∘ (fun p : B × B => p.1 * p.2)) := by
    have h91 : (h ∘ (fun p : B × B => p.1 * p.2)) = (fun p : B × B => h (p.1 * p.2)) := by
      funext p
      simp
    rw [h91]
    exact h7
  have h10 : Continuous (fun p : B × B => p.1 * p.2) := by
    have h101 : Continuous (h ∘ (fun p : B × B => p.1 * p.2)) := h9
    have h102 : Continuous (fun p : B × B => p.1 * p.2) ↔ Continuous (h ∘ (fun p : B × B => p.1 * p.2)) := by
      exact?
    exact h102.mpr h101
  exact { continuous_mul := h10 }

theorem induced_continuous_mul [CommMonoid A] [τA : TopologicalSpace A] [ContinuousMul A]
    [CommMonoid B] (h : B →* A) :
    @ContinuousMul B (TopologicalSpace.induced h τA) _  := by

  exact round1_induced_continuous_mul h
