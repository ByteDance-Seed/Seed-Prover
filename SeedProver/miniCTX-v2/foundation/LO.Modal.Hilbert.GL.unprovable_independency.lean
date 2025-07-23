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

/- Start of proof attempt -/
lemma round1_unprovable_independency (φ : Formula ℕ) : (Hilbert.GL _) ⊬ independency φ := by
  by_contra h
  have h1 : (Hilbert.GL _) ⊢! (∼□φ ⋏ ∼□(∼φ)) := by simpa [independency] using h
  have h2 : (Hilbert.GL _) ⊢! ((∼□φ ⋏ ∼□(∼φ)) ➝ ∼□φ) := by
    exact?
  have h3 : (Hilbert.GL _) ⊢! ∼□φ := h2 ⨀ h1
  have h4 : (Hilbert.GL _) ⊬ ∼□φ := unprovable_notbox
  contradiction

theorem unprovable_independency : (Hilbert.GL _) ⊬ independency φ  := by

  exact round1_unprovable_independency φ
