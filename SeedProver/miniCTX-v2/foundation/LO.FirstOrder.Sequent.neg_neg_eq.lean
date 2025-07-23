-- In foundation/Foundation/IntFO/Translation.lean

import Foundation.IntFO.Basic

namespace LO.FirstOrder

namespace Sequent

instance : Tilde (List (Semiformula L ξ n)) := ⟨fun Γ ↦ Γ.map (∼·)⟩

@[simp] lemma neg_def (Γ : List (Semiformula L ξ n)) : ∼Γ = Γ.map (∼·) := rfl

@[simp] lemma neg_nil : ∼([] : List (Semiformula L ξ n)) = [] := rfl

@[simp] lemma neg_cons (Γ : List (Semiformula L ξ n)) (φ) : ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl

/- Start of proof attempt -/
lemma round1_neg_neg_eq (Γ : List (Semiformula L ξ n)) : ∼∼Γ = Γ := by
  induction Γ with
  | nil =>
    simp
  | cons φ Γ ih =>
    simp_all [neg_cons]
    <;> aesop

theorem neg_neg_eq (Γ : List (Semiformula L ξ n)) : ∼∼Γ = Γ  := by

  exact round1_neg_neg_eq Γ
