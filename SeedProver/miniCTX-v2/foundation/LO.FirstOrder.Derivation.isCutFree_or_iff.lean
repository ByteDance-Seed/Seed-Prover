-- In foundation/Foundation/FirstOrder/Hauptsatz.lean

import Foundation.IntFO.Translation

/-!
#Algebraic Proofs of Cut Elimination

Main reference: Jeremy Avigad, Algebraic proofs of cut elimination, The Journal of Logic and Algebraic Programming, Volume 49, Issues 1–2, 2001, Pages 15-30
 -/

namespace LO.FirstOrder

variable {L : Language.{u}}

namespace Derivation

inductive IsCutFree : {Γ : Sequent L} → ⊢ᵀ Γ → Prop
| axL (Γ) {k} (r : L.Rel k) (v)                 : IsCutFree (axL Γ r v)
| verum (Γ)                                     : IsCutFree (verum Γ)
| or {Γ φ ψ} {d : ⊢ᵀ φ :: ψ :: Γ}               : IsCutFree d → IsCutFree d.or
| and {Γ φ ψ} {dφ : ⊢ᵀ φ :: Γ} {dψ : ⊢ᵀ ψ :: Γ} : IsCutFree dφ → IsCutFree dψ → IsCutFree (dφ.and dψ)
| all {Γ φ} {d : ⊢ᵀ Rewriting.free φ :: Γ⁺}     : IsCutFree d → IsCutFree d.all
| ex {Γ φ} (t) {d : ⊢ᵀ φ/[t] :: Γ}              : IsCutFree d → IsCutFree d.ex
| wk {Δ Γ} {d : ⊢ᵀ Δ} (ss : Δ ⊆ Γ)              : IsCutFree d → IsCutFree (d.wk ss)

attribute [simp] IsCutFree.axL IsCutFree.verum

variable {Γ Δ : Sequent L}

/- Start of proof attempt -/
lemma round1_isCutFree_or_iff {d : ⊢ᵀ φ :: ψ :: Γ} :
    IsCutFree d.or ↔ IsCutFree d := by
  constructor
  · -- Assume `IsCutFree d.or`, we need to prove `IsCutFree d`
    intro h
    cases h with
    | or h1 =>
      exact h1
  · -- Assume `IsCutFree d`, we need to prove `IsCutFree d.or`
    intro h
    exact IsCutFree.or h

theorem isCutFree_or_iff {d : ⊢ᵀ φ :: ψ :: Γ} :
    IsCutFree d.or ↔ IsCutFree d  := by

  exact round1_isCutFree_or_iff
