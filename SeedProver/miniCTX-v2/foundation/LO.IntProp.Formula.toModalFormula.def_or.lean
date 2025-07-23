-- In foundation/Foundation/Modal/IntProp.lean

import Foundation.IntProp.Formula
import Foundation.Modal.Formula

namespace LO.IntProp

def Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ∼φ => ∼(toModalFormula φ)
  | φ ➝ ψ => (toModalFormula φ) ➝ (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)
postfix:75 "ᴹ" => Formula.toModalFormula

namespace Formula.toModalFormula

@[simp] lemma def_top : (⊤ : Formula α)ᴹ = ⊤ := by rfl

@[simp] lemma def_bot : (⊥ : Formula α)ᴹ = ⊥ := by rfl

@[simp] lemma def_atom (a : α) : (atom a)ᴹ = .atom a := by rfl

@[simp] lemma def_not (φ : Formula α) : (∼φ)ᴹ = ∼(φᴹ) := by rfl

@[simp] lemma def_imp (φ ψ : Formula α) : (φ ➝ ψ)ᴹ = (φᴹ) ➝ (ψᴹ) := by rfl

@[simp] lemma def_and (φ ψ : Formula α) : (φ ⋏ ψ)ᴹ = (φᴹ) ⋏ (ψᴹ) := by rfl

/- Start of proof attempt -/
lemma round1_def_or (φ ψ : Formula α) : (φ ⋎ ψ)ᴹ = (φᴹ) ⋎ (ψᴹ) := by
  simp [Formula.toModalFormula]

theorem def_or (φ ψ : Formula α) : (φ ⋎ ψ)ᴹ = (φᴹ) ⋎ (ψᴹ)  := by

  exact round1_def_or φ ψ
