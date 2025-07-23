-- In foundation/Foundation/Modal/Hilbert/WeakerThan/K4_K45.lean

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

/- Start of proof attempt -/
lemma round1_h1 (α : Type u_1):
  ∀ (φ : Formula α), φ ∈ axioms (Hilbert.K4 α) → φ ∈ axioms (Hilbert.K45 α) := by
  intro φ h11
  simp [Hilbert.K4, Hilbert.K45] at h11 ⊢ <;> aesop

theorem K4_weakerThan_K45 : (Hilbert.K4 α) ≤ₛ (Hilbert.K45 α)  := by

  have h1 : ∀ (φ : Formula α), φ ∈ axioms (Hilbert.K4 α) → φ ∈ axioms (Hilbert.K45 α) := by
    exact round1_h1 α
  exact?
