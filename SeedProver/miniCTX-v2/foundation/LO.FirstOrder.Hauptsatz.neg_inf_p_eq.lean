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

@[simp] lemma IsCutFree.genelalizeByNewver_isCutFree {φ : SyntacticSemiformula L 1} (hp : ¬φ.FVar? m) (hΔ : ∀ ψ ∈ Δ, ¬ψ.FVar? m)
    (d : ⊢ᵀ φ/[&m] :: Δ) : IsCutFree (genelalizeByNewver hp hΔ d) ↔ IsCutFree d := by simp [genelalizeByNewver]

end Derivation

inductive PositiveDerivationFrom (Ξ : Sequent L) : Sequent L → Type _
| verum (Γ)    : PositiveDerivationFrom Ξ (⊤ :: Γ)
| or {Γ φ ψ}   : PositiveDerivationFrom Ξ (φ :: ψ :: Γ) → PositiveDerivationFrom Ξ (φ ⋎ ψ :: Γ)
| ex {Γ φ} (t) : PositiveDerivationFrom Ξ (φ/[t] :: Γ) → PositiveDerivationFrom Ξ ((∃' φ) :: Γ)
| wk {Γ Δ}     : PositiveDerivationFrom Ξ Δ → Δ ⊆ Γ → PositiveDerivationFrom Ξ Γ
| protected id : PositiveDerivationFrom Ξ Ξ

infix:45 " ⟶⁺ " => PositiveDerivationFrom

namespace PositiveDerivationFrom

variable {Ξ Γ Δ : Sequent L}

def ofSubset (ss : Ξ ⊆ Γ) : Ξ ⟶⁺ Γ := wk .id ss

def trans {Ξ Γ Δ : Sequent L} : Ξ ⟶⁺ Γ → Γ ⟶⁺ Δ → Ξ ⟶⁺ Δ
  | _, verum Γ => verum Γ
  | b, or d    => or (b.trans d)
  | b, ex t d  => ex t (b.trans d)
  | b, wk d h  => wk (b.trans d) h
  | b, .id     => b

def cons {Ξ Γ : Sequent L} (φ) : Ξ ⟶⁺ Γ → φ :: Ξ ⟶⁺ φ :: Γ
  | verum Γ         => wk (verum Γ) (List.subset_cons_self _ _)
  | @or _ _ Γ ψ χ d =>
    have : φ :: Ξ ⟶⁺ ψ :: χ :: φ :: Γ := wk (cons φ d) (by simp; tauto)
    wk (or this) (by simp)
  | @ex _ Ξ Γ ψ t d =>
    have : φ :: Ξ ⟶⁺ ψ/[t] :: φ :: Γ := wk (cons φ d) (by simp)
    wk this.ex (by simp)
  | wk d h          => wk (d.cons φ) (by simp [h])
  | .id             => .id

def append {Ξ Γ : Sequent L} : (Δ : Sequent L) → Ξ ⟶⁺ Γ → Δ ++ Ξ ⟶⁺ Δ ++ Γ
  | [],     d => d
  | φ :: Δ, d => (d.append Δ).cons φ

def add {Γ Δ Ξ Θ : Sequent L} : Γ ⟶⁺ Δ → Ξ ⟶⁺ Θ → Γ ++ Ξ ⟶⁺ Δ ++ Θ
  | verum Δ, d => verum _
  | or d,    b => or (d.add b)
  | ex t d,  b => ex t (d.add b)
  | wk d h,  b => wk (d.add b) (by simp [h])
  | .id,     b => b.append Γ

def graft {Ξ Γ : Sequent L} (b : ⊢ᵀ Ξ) : Ξ ⟶⁺ Γ → ⊢ᵀ Γ
  | verum Γ => .verum Γ
  | or d    => .or (d.graft b)
  | ex t d  => .ex t (d.graft b)
  | wk d h  => .wk (d.graft b) h
  | .id     => b

lemma graft_isCutFree_of_isCutFree {b : ⊢ᵀ Ξ} {d : Ξ ⟶⁺ Γ} (hb : Derivation.IsCutFree b) : Derivation.IsCutFree (d.graft b) := by
  induction d <;> simp [graft, *]

end PositiveDerivationFrom

namespace Hauptsatz

open Semiformulaᵢ

local notation "ℙ" => Sequent L

structure StrongerThan (q p : ℙ) where
  val : ∼p ⟶⁺ ∼q

scoped infix:60 " ≼ " => StrongerThan

scoped instance : Min ℙ := ⟨fun p q ↦ p ++ q⟩

lemma inf_def (p q : ℙ) : p ⊓ q = p ++ q := rfl

/- Start of proof attempt -/
lemma round1_neg_inf_p_eq (p q : ℙ) : ∼(p ⊓ q) = ∼p ⊓ ∼q := by
  simp [inf_def]
  <;> aesop

theorem neg_inf_p_eq (p q : ℙ) : ∼(p ⊓ q) = ∼p ⊓ ∼q  := by

  exact round1_neg_inf_p_eq p q
