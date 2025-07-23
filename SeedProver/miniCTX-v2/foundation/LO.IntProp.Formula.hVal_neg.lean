-- In foundation/Foundation/IntProp/Heyting/Semantics.lean

import Foundation.IntProp.Hilbert.Basic
import Foundation.Vorspiel.Order
import Foundation.Logic.LindenbaumAlgebra

namespace LO.IntProp

variable {α : Type u}

namespace Formula

def hVal {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ) : Formula α → ℍ
  | atom a => v a
  | ⊤      => ⊤
  | ⊥      => ⊥
  | φ ⋏ ψ  => φ.hVal v ⊓ ψ.hVal v
  | φ ⋎ ψ  => φ.hVal v ⊔ ψ.hVal v
  | φ ➝ ψ  => φ.hVal v ⇨ ψ.hVal v
  | ∼φ     => (φ.hVal v)ᶜ

variable {ℍ : Type*} [HeytingAlgebra ℍ] (v : α → ℍ)

@[simp] lemma hVal_atom (a : α) : (atom a).hVal v = v a := rfl

@[simp] lemma hVal_verum : (⊤ : Formula α).hVal v = ⊤ := rfl

@[simp] lemma hVal_falsum : (⊥ : Formula α).hVal v = ⊥ := rfl

@[simp] lemma hVal_and (φ ψ : Formula α) : (φ ⋏ ψ).hVal v = φ.hVal v ⊓ ψ.hVal v := rfl

@[simp] lemma hVal_or (φ ψ : Formula α) : (φ ⋎ ψ).hVal v = φ.hVal v ⊔ ψ.hVal v := rfl

@[simp] lemma hVal_imp (φ ψ : Formula α) : (φ ➝ ψ).hVal v = φ.hVal v ⇨ ψ.hVal v := rfl

/- Start of proof attempt -/
lemma round1_hVal_neg {ℍ : Type*} [HeytingAlgebra ℍ] {α : Type u} (v : α → ℍ) (φ : Formula α) : 
  (∼φ).hVal v = (φ.hVal v)ᶜ := by
  rfl

theorem hVal_neg (φ : Formula α) : (∼φ).hVal v = (φ.hVal v)ᶜ  := by

  exact round1_hVal_neg v φ
