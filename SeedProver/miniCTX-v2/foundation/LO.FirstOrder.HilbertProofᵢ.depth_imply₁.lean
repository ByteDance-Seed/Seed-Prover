-- In foundation/Foundation/IntFO/Basic/Deduction.lean

import Foundation.IntFO.Basic.Rew

namespace LO.FirstOrder

abbrev Sequentᵢ (L : Language) := List (SyntacticFormulaᵢ L)

open Semiformulaᵢ

variable {L : Language} {T : Theory L}

structure Hilbertᵢ (L : Language) where
  axiomSet : Set (SyntacticFormulaᵢ L)
  rewrite_closed {φ : SyntacticFormulaᵢ L} : φ ∈ axiomSet → ∀ f : ℕ → SyntacticTerm L, Rew.rewrite f ▹ φ ∈ axiomSet

instance : SetLike (Hilbertᵢ L) (SyntacticFormulaᵢ L) where
  coe := Hilbertᵢ.axiomSet
  coe_injective' := by rintro ⟨T, _⟩ ⟨U, _⟩; simp

namespace Hilbertᵢ

def Minimal : Hilbertᵢ L := ⟨∅, by simp⟩

notation "𝐌𝐢𝐧¹" => Minimal

def Intuitionistic : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ}, by rintro _ ⟨φ, rfl⟩ f; exact ⟨Rew.rewrite f ▹ φ, by simp⟩⟩

notation "𝐈𝐧𝐭¹" => Intuitionistic

def Classical : Hilbertᵢ L := ⟨{⊥ ➝ φ | φ} ∪ {φ ⋎ ∼φ | φ}, by
  rintro _ (⟨φ, rfl⟩ | ⟨φ, rfl⟩) f
  · exact Or.inl ⟨Rew.rewrite f ▹ φ, by simp⟩
  · exact Or.inr ⟨Rew.rewrite f ▹ φ, by simp⟩⟩

notation "𝐂𝐥¹" => Classical

lemma minimal_le (Λ : Hilbertᵢ L) : (Minimal : Hilbertᵢ L) ≤ Λ := by rintro _ ⟨⟩

lemma intuitionistic_le_classical : (Intuitionistic : Hilbertᵢ L) ≤ Classical := by rintro _ ⟨φ, rfl⟩; exact .inl ⟨φ, rfl⟩

end Hilbertᵢ

inductive HilbertProofᵢ (Λ : Hilbertᵢ L) : SyntacticFormulaᵢ L → Type _
  | eaxm {φ}     : φ ∈ Λ → HilbertProofᵢ Λ φ
  | mdp {φ ψ}    : HilbertProofᵢ Λ (φ ➝ ψ) → HilbertProofᵢ Λ φ → HilbertProofᵢ Λ ψ
  | gen {φ}      : HilbertProofᵢ Λ (Rewriting.free φ) → HilbertProofᵢ Λ (∀' φ)
  | verum        : HilbertProofᵢ Λ ⊤
  | imply₁ φ ψ   : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ
  | imply₂ φ ψ χ : HilbertProofᵢ Λ <| (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
  | and₁ φ ψ     : HilbertProofᵢ Λ <| φ ⋏ ψ ➝ φ
  | and₂ φ ψ     : HilbertProofᵢ Λ <| φ ⋏ ψ ➝ ψ
  | and₃ φ ψ     : HilbertProofᵢ Λ <| φ ➝ ψ ➝ φ ⋏ ψ
  | or₁ φ ψ      : HilbertProofᵢ Λ <| φ ➝ φ ⋎ ψ
  | or₂ φ ψ      : HilbertProofᵢ Λ <| ψ ➝ φ ⋎ ψ
  | or₃ φ ψ χ    : HilbertProofᵢ Λ <| (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)
  | all₁ φ t     : HilbertProofᵢ Λ <| ∀' φ ➝ φ/[t]
  | all₂ φ ψ     : HilbertProofᵢ Λ <| ∀' (φ/[] ➝ ψ) ➝ φ ➝ ∀' ψ
  | ex₁ t φ      : HilbertProofᵢ Λ <| φ/[t] ➝ ∃' φ
  | ex₂ φ ψ      : HilbertProofᵢ Λ <| ∀' (φ ➝ ψ/[]) ➝ ∃' φ ➝ ψ

instance : System (SyntacticFormulaᵢ L) (Hilbertᵢ L) := ⟨HilbertProofᵢ⟩

namespace HilbertProofᵢ

open System.FiniteContext Rewriting LawfulSyntacticRewriting

variable (Λ : Hilbertᵢ L)

instance : System.ModusPonens Λ := ⟨mdp⟩

instance : System.HasAxiomAndInst Λ := ⟨and₃⟩

instance : System.HasAxiomImply₁ Λ := ⟨imply₁⟩

instance : System.HasAxiomImply₂ Λ := ⟨imply₂⟩

instance : System.Minimal Λ where
  mdp := mdp
  verum := verum
  imply₁ := imply₁
  imply₂ := imply₂
  and₁ := and₁
  and₂ := and₂
  and₃ := and₃
  or₁ := or₁
  or₂ := or₂
  or₃ := or₃
  neg_equiv _ := System.iffId _

variable {Λ}

protected def cast {φ ψ} (b : Λ ⊢ φ) (e : φ = ψ) : Λ ⊢ ψ := e ▸ b

def depth {φ} : Λ ⊢ φ → ℕ
  | mdp b d => max (depth b) (depth d) + 1
  | gen b   => depth b + 1
  | _       => 0

scoped notation "‖" d "‖" => depth d

@[simp] lemma depth_eaxm (h : φ ∈ Λ) : ‖eaxm h‖ = 0 := rfl
@[simp] lemma depth_mdp (b : Λ ⊢ φ ➝ ψ) (d : Λ ⊢ φ) : ‖mdp b d‖ = max ‖b‖ ‖d‖ + 1 := rfl
@[simp] lemma depth_gen (b : Λ ⊢ Rewriting.free φ) : ‖gen b‖ = ‖b‖ + 1 := rfl
@[simp] lemma depth_verum : ‖(verum : Λ ⊢ ⊤)‖ = 0 := rfl

/- Start of proof attempt -/
lemma round1_depth_imply₁ (φ ψ : SyntacticFormulaᵢ L) :
  ‖imply₁ (Λ := Λ) φ ψ‖ = 0 := by
  rfl

theorem depth_imply₁ (φ ψ) : ‖imply₁ (Λ := Λ) φ ψ‖ = 0  := by

  exact round1_depth_imply₁ φ ψ
