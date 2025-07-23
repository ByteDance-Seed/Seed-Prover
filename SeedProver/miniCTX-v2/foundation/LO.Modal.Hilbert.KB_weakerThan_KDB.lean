-- In foundation/Foundation/Modal/Hilbert/WeakerThan/KB_KDB.lean

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

/- Start of proof attempt -/
lemma round1_h1 (α : Type u_1):
  ∀ (φ : Formula α), φ ∈ (Hilbert.KB α).axioms → φ ∈ (Hilbert.KDB α).axioms := by
  intro φ h111
  simp [Hilbert.KB, Hilbert.KDB] at h111 ⊢
  <;> aesop

theorem KB_weakerThan_KDB : (Hilbert.KB α) ≤ₛ (Hilbert.KDB α)  := by

  have h11 : (Hilbert.KB α).axioms ⊆ (Hilbert.KDB α).axioms := by
    intro φ h12
    have h13 : ∀ (φ : Formula α), φ ∈ (Hilbert.KB α).axioms → φ ∈ (Hilbert.KDB α).axioms := round1_h1 α
    exact h13 φ h12
  exact?
