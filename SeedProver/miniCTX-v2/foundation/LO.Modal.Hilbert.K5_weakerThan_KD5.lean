-- In foundation/Foundation/Modal/Hilbert/WeakerThan/K5_KD5.lean

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

/- Start of proof attempt -/
lemma round1_h1 (α : Type u) :
  ∀ (A : Formula α), A ∈ (Hilbert.K5 α).axioms → A ∈ (Hilbert.KD5 α).axioms := by
  intro A hA
  cases hA <;> aesop

lemma round1_h2 (α : Type u) (h1 : ∀ (A : Formula α), A ∈ (Hilbert.K5 α).axioms → A ∈ (Hilbert.KD5 α).axioms) :
  (Hilbert.K5 α).axioms ⊆ (Hilbert.KD5 α).axioms := by
  intro A hA
  exact h1 A hA

theorem K5_weakerThan_KD5 : (Hilbert.K5 α) ≤ₛ (Hilbert.KD5 α)  := by

  have h1 : ∀ (A : Formula α), A ∈ (Hilbert.K5 α).axioms → A ∈ (Hilbert.KD5 α).axioms := by
    exact round1_h1 α
  have h2 : (Hilbert.K5 α).axioms ⊆ (Hilbert.KD5 α).axioms := by
    exact round1_h2 α h1
  exact?
