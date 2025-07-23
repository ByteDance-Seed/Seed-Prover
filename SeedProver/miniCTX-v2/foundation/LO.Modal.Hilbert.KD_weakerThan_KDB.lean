-- In foundation/Foundation/Modal/Hilbert/WeakerThan/KD_KDB.lean

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke

/- Start of proof attempt -/
lemma KD_axioms_subset_KDB_axioms (α : Type u_1):
  ∀ (a : Formula α), a ∈ (LO.Modal.Hilbert.KD α).axioms → a ∈ (LO.Modal.Hilbert.KDB α).axioms := by
  intro a ha
  simp [LO.Modal.Hilbert.KD, LO.Modal.Hilbert.KDB, LO.Modal.Hilbert.ExtK] at ha ⊢
  <;> aesop

theorem KD_weakerThan_KDB : (Hilbert.KD α) ≤ₛ (Hilbert.KDB α)  := by

  have h : ∀ (a : Formula α), a ∈ (LO.Modal.Hilbert.KD α).axioms → a ∈ (LO.Modal.Hilbert.KDB α).axioms := by
    exact KD_axioms_subset_KDB_axioms α
  have h2 : (LO.Modal.Hilbert.KD α).axioms ⊆ (LO.Modal.Hilbert.KDB α).axioms := by
    intro a ha
    exact h a ha
  exact?
