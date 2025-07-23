-- In foundation/Foundation/Modal/Hilbert/GL_Independency.lean

import Foundation.Modal.Hilbert.Maximal.Unprovability
import Foundation.Modal.Kripke.GL.MDP

namespace LO.Modal

open System
open IntProp

variable [DecidableEq α]

def independency (φ : Formula α) := ∼□φ ⋏ ∼□(∼φ)

def higherIndependency (φ : Formula α) : ℕ → Formula α
  | 0 => φ
  | n + 1 => independency (higherIndependency φ n)

namespace Hilbert.GL

variable {φ : Formula ℕ}

lemma unprovable_notbox : (Hilbert.GL _) ⊬ ∼□φ := by
  by_contra hC;
  have : (Hilbert.GL _) ⊢! ∼□φ ➝ ∼□⊥ := contra₀'! (imply_box_distribute'! efq!)
  have : Hilbert.GL _ ⊢! ∼□⊥ := this ⨀ hC;
  have : Hilbert.Cl ℕ ⊢! (⊥ ➝ ⊥) ➝ ⊥ := by simpa using provable_CL_verTranslated this;
  simpa using Hilbert.Cl.classical_sound this;

lemma unprovable_independency : (Hilbert.GL _) ⊬ independency φ := by
  by_contra hC;
  exact unprovable_notbox $ and₁'! hC;

lemma unprovable_not_independency_of_consistency : (Hilbert.GL ℕ) ⊬ ∼(independency (∼□⊥)) := by
  by_contra hC;
  rcases modal_disjunctive (dne_or! $ demorgan₄'! hC) with (h | h);
  . exact unprovable_notbox h;
  . exact Consistent.not_bot (inferInstance) $ unnec! $ dne'! h

/- Start of proof attempt -/
lemma round1_h1 : (Hilbert.GL ℕ) ⊬ (independency (∼□⊥)) := by
  exact unprovable_independency (φ := (∼□⊥))

lemma round1_h2 : (Hilbert.GL ℕ) ⊬ ∼(independency (∼□⊥)) := by
  exact unprovable_not_independency_of_consistency

theorem undecidable_independency_of_consistency : Undecidable (Hilbert.GL ℕ) (independency (∼□⊥))  := by

  have h1 : (Hilbert.GL ℕ) ⊬ (independency (∼□⊥)) := by
    exact round1_h1
  have h2 : (Hilbert.GL ℕ) ⊬ ∼(independency (∼□⊥)) := by
    exact round1_h2
  exact ⟨h1, h2⟩
