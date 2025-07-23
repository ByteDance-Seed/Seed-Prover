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

/- Start of proof attempt -/
lemma round1_def_top (α : Type u) : (⊤ : Formula α)ᴹ = ⊤ := by
  rfl

theorem def_top : (⊤ : Formula α)ᴹ = ⊤  := by

  exact round1_def_top α
