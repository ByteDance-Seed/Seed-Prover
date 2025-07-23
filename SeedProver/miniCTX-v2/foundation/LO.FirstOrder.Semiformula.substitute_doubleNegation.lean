-- In foundation/Foundation/IntFO/Translation.lean

import Foundation.IntFO.Basic

namespace LO.FirstOrder

namespace Sequent

instance : Tilde (List (Semiformula L ξ n)) := ⟨fun Γ ↦ Γ.map (∼·)⟩

@[simp] lemma neg_def (Γ : List (Semiformula L ξ n)) : ∼Γ = Γ.map (∼·) := rfl

@[simp] lemma neg_nil : ∼([] : List (Semiformula L ξ n)) = [] := rfl

@[simp] lemma neg_cons (Γ : List (Semiformula L ξ n)) (φ) : ∼(φ :: Γ) = ∼φ :: ∼Γ := rfl

@[simp] lemma neg_neg_eq (Γ : List (Semiformula L ξ n)) : ∼∼Γ = Γ := by simp [Function.comp_def]

end Sequent

namespace Semiformula

def doubleNegation {n} : Semiformula L ξ n → Semiformulaᵢ L ξ n
  | rel r v  => ∼∼(.rel r v)
  | nrel r v => ∼(.rel r v)
  | ⊤        => ∼⊥
  | ⊥        => ⊥
  | φ ⋏ ψ    => φ.doubleNegation ⋏ ψ.doubleNegation
  | φ ⋎ ψ    => ∼(∼φ.doubleNegation ⋏ ∼ψ.doubleNegation)
  | ∀' φ     => ∀' φ.doubleNegation
  | ∃' φ     => ∼(∀' ∼φ.doubleNegation)

scoped[LO.FirstOrder] postfix:max "ᴺ" => Semiformula.doubleNegation

@[simp] lemma doubleNegation_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v)ᴺ = ∼∼(.rel r v) := rfl

@[simp] lemma doubleNegation_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v)ᴺ = ∼(.rel r v) := rfl

@[simp] lemma doubleNegation_verum : (⊤ : Semiformula L ξ n)ᴺ = ∼⊥ := rfl

@[simp] lemma doubleNegation_falsum : (⊥ : Semiformula L ξ n)ᴺ = ⊥ := rfl

@[simp] lemma doubleNegation_and (φ ψ : Semiformula L ξ n) : (φ ⋏ ψ)ᴺ = φᴺ ⋏ ψᴺ := rfl

@[simp] lemma doubleNegation_or (φ ψ : Semiformula L ξ n) : (φ ⋎ ψ)ᴺ = ∼(∼φᴺ ⋏ ∼ψᴺ) := rfl

@[simp] lemma doubleNegation_all (φ : Semiformula L ξ (n + 1)) : (∀' φ)ᴺ = ∀' φᴺ := rfl

@[simp] lemma doubleNegation_ex (φ : Semiformula L ξ (n + 1)) : (∃' φ)ᴺ = ∼(∀' ∼φᴺ) := rfl

@[simp] lemma doubleNegation_isNegative (φ : Semiformula L ξ n) : φᴺ.IsNegative := by
  induction φ using rec' <;> simp [*]

lemma rew_doubleNegation (ω : Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L ξ₁ n₁) : ω ▹ φᴺ = (ω ▹ φ)ᴺ := by
  induction φ using rec' generalizing n₂ <;> simp [rew_rel, rew_nrel, Semiformulaᵢ.rew_rel, *]

/- Start of proof attempt -/
lemma round1_substitute_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) : 
  φᴺ ⇜ v = (φ ⇜ v)ᴺ := by
  exact?

theorem substitute_doubleNegation (φ : Semiformula L ξ n₁) (v : Fin n₁ → Semiterm L ξ n₂) : φᴺ ⇜ v = (φ ⇜ v)ᴺ  := by

  exact round1_substitute_doubleNegation φ v
