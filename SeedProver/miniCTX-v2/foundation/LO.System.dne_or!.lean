-- In foundation/Foundation/Logic/HilbertStyle/Supplemental.lean

import Foundation.Logic.System
import Foundation.Logic.HilbertStyle.Context

namespace LO.System

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [System F S]
         {𝓢 : S} [System.Minimal 𝓢]
         {φ ψ χ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

def mdp_in : 𝓢 ⊢ φ ⋏ (φ ➝ ψ) ➝ ψ := by
  apply deduct';
  have hp  : [φ, φ ➝ ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have hpq : [φ, φ ➝ ψ] ⊢[𝓢] φ ➝ ψ := FiniteContext.byAxm;
  exact hpq ⨀ hp;
lemma mdp_in! : 𝓢 ⊢! φ ⋏ (φ ➝ ψ) ➝ ψ := ⟨mdp_in⟩

def bot_of_mem_either (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  have hp : Γ ⊢[𝓢] φ := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢] φ ➝ ⊥ := neg_equiv'.mp $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

@[simp] lemma bot_of_mem_either! (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := ⟨bot_of_mem_either h₁ h₂⟩

def efq_of_mem_either [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ψ := efq' $ bot_of_mem_either h₁ h₂
@[simp] lemma efq_of_mem_either! [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ψ := ⟨efq_of_mem_either h₁ h₂⟩

def efq_imply_not₁ [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ∼φ ➝ φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma efq_imply_not₁! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ∼φ ➝ φ ➝ ψ := ⟨efq_imply_not₁⟩

def efq_imply_not₂ [HasAxiomEFQ 𝓢] : 𝓢 ⊢ φ ➝ ∼φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma efq_imply_not₂! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ➝ ∼φ ➝ ψ := ⟨efq_imply_not₂⟩

lemma efq_of_neg! [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! φ ➝ ψ := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [φ] ⊢[𝓢]! φ ➝ ⊥ := of'! $ neg_equiv'!.mp h;
  exact efq'! (dnp ⨀ FiniteContext.id!);

lemma efq_of_neg₂! [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼φ ➝ ψ := efq_imply_not₂! ⨀ h

def neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (neg_equiv'.mp hnp) ⨀ hn
-- infixl:90 "⨀" => neg_mdp

omit [DecidableEq F] in lemma neg_mdp! (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := ⟨neg_mdp hnp.some hn.some⟩
-- infixl:90 "⨀" => neg_mdp!

def dneOr [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ := or₃''' (impTrans'' dne or₁) (impTrans'' dne or₂) d
omit [DecidableEq F] in 
/- Start of proof attempt -/
lemma round1_dne_or! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := by
  have h1 : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := d.some
  have h2 : 𝓢 ⊢ φ ⋎ ψ := dneOr h1
  exact ⟨h2⟩

theorem dne_or! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ  := by

  exact round1_dne_or! d
