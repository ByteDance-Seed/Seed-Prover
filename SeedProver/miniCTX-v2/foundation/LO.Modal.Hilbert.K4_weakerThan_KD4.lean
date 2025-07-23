-- In foundation/Foundation/Modal/Hilbert/WeakerThan/K4_KD4.lean

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke


/- Start of proof attempt -/
lemma round1_h1 (α : Type u) : ∀ (A : Formula α), A ∈ (Hilbert.K4 α).axioms → A ∈ (Hilbert.KD4 α).axioms := by
  intro A hA
  rcases hA with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _) <;> aesop

theorem K4_weakerThan_KD4 : (Hilbert.K4 α) ≤ₛ (Hilbert.KD4 α)  := by

  have h1 : ∀ (A : Formula α), A ∈ (Hilbert.K4 α).axioms → A ∈ (Hilbert.KD4 α).axioms := by
    exact round1_h1 α
  exact?
