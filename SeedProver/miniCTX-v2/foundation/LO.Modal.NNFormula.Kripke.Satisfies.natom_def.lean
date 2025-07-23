-- In foundation/Foundation/Modal/Kripke/NNFormula.lean

import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Basic

namespace LO.Modal

open System

variable {φ ψ : NNFormula ℕ}

namespace NNFormula.Kripke

def Satisfies (M : Kripke.Model) (x : M.World) : NNFormula ℕ → Prop
  | atom a  =>  M x a
  | natom a => ¬M x a
  | ⊤       => True
  | ⊥       => False
  | φ ⋎ ψ   => Satisfies M x φ ∨ Satisfies M x ψ
  | φ ⋏ ψ   => Satisfies M x φ ∧ Satisfies M x ψ
  | □φ      => ∀ y, x ≺ y → Satisfies M y φ
  | ◇φ      => ∃ y, x ≺ y ∧ (Satisfies M y φ)

namespace Satisfies

variable {M : Kripke.Model} {x : M.World}

protected instance semantics : Semantics (NNFormula ℕ) (M.World) := ⟨λ x ↦ Satisfies M x⟩

protected lemma iff_models : x ⊧ φ ↔ Satisfies M x φ := iff_of_eq rfl

@[simp]
protected lemma atom_def (a : ℕ) : x ⊧ (atom a) ↔ M x a := by simp [Satisfies.iff_models, Satisfies];

/- Start of proof attempt -/
lemma round1_natom_def (a : ℕ) : x ⊧ (natom a) ↔ ¬M x a := by
  simp [Satisfies.iff_models]
  <;> aesop

theorem natom_def (a : ℕ) : x ⊧ (natom a) ↔ ¬M x a  := by

  exact round1_natom_def a
