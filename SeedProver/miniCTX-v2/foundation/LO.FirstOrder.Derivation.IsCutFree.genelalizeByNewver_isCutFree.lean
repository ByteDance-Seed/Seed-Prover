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

@[simp] lemma isCutFree_or_iff {d : ⊢ᵀ φ :: ψ :: Γ} :
    IsCutFree d.or ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .or⟩

@[simp] lemma isCutFree_and_iff {dφ : ⊢ᵀ φ :: Γ} {dψ : ⊢ᵀ ψ :: Γ} :
    IsCutFree (dφ.and dψ) ↔ IsCutFree dφ ∧ IsCutFree dψ :=
  ⟨by rintro ⟨⟩; constructor <;> assumption, by intro ⟨hφ, hψ⟩; exact hφ.and hψ⟩

@[simp] lemma isCutFree_all_iff {d : ⊢ᵀ Rewriting.free φ :: Γ⁺} :
    IsCutFree d.all ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .all⟩

@[simp] lemma isCutFree_ex_iff {d : ⊢ᵀ φ/[t] :: Γ} :
    IsCutFree d.ex ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .ex t⟩

@[simp] lemma isCutFree_wk_iff {d : ⊢ᵀ Δ} {ss : Δ ⊆ Γ} :
    IsCutFree (d.wk ss) ↔ IsCutFree d := ⟨by rintro ⟨⟩; assumption, .wk _⟩

@[simp] lemma IsCutFree.cast {d : ⊢ᵀ Γ} {e : Γ = Δ} :
    IsCutFree (.cast d e) ↔ IsCutFree d := by rcases e; rfl

@[simp] lemma IsCutFree.not_cut (dp : ⊢ᵀ φ :: Γ) (dn : ⊢ᵀ ∼φ :: Γ) : ¬IsCutFree (dp.cut dn) := by rintro ⟨⟩

@[simp] lemma isCutFree_rewrite_iff_isCutFree {f : ℕ → SyntacticTerm L} {d : ⊢ᵀ Γ} :
    IsCutFree (rewrite d f) ↔ IsCutFree d := by
  induction d generalizing f <;> simp [rewrite, *]
  case root => contradiction

@[simp] lemma isCutFree_map_iff_isCutFree {f : ℕ → ℕ} {d : ⊢ᵀ Γ} :
    IsCutFree (Derivation.map d f) ↔ IsCutFree d := isCutFree_rewrite_iff_isCutFree

/- Start of proof attempt -/
lemma round1_h {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᵀ φ/[&m] :: Δ) : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d := by
  simp [genelalizeByNewver, IsCutFree.cast, isCutFree_rewrite_iff_isCutFree, isCutFree_map_iff_isCutFree]
  <;> aesop

theorem IsCutFree.genelalizeByNewver_isCutFree {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᵀ φ/[&m] :: Δ) : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d  := by

  have h : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d := by
    exact round1_h hp hΔ d
  exact h
