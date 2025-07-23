-- In foundation/Foundation/Modal/Hilbert/WeakerThan/K5_K45.lean

import Foundation.Modal.Kripke.Geach.Systems

namespace LO.Modal.Hilbert

open System
open Modal.Kripke
open Formula
open Formula.Kripke


/- Start of proof attempt -/
lemma round1_h1 (α : Type u)
  (p : Formula α)
  (hp : p ∈ (Hilbert.K5 α).axioms) :
  p ∈ (Hilbert.K45 α).axioms := by
  simp [Hilbert.K5, Hilbert.K45] at hp ⊢ <;>
  (try tauto) <;>
  (try aesop) <;>
  (try {
    cases hp <;> aesop
  }) <;>
  (try {
    tauto
  }) <;>
  (try {
    aesop
  })

theorem K5_weakerThan_K45 : (Hilbert.K5 α) ≤ₛ (Hilbert.K45 α)  := by

  have h1 : (Hilbert.K5 α).axioms ⊆ (Hilbert.K45 α).axioms := by
    intro p hp
    exact round1_h1 α p hp
  have h2 : (Hilbert.K5 α) ≤ₛ (Hilbert.K45 α) := by
    exact?
  exact h2
