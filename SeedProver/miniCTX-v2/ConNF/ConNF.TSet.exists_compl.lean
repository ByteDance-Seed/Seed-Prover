-- In ConNF/ConNF/Model/Hailperin.lean

import ConNF.Model.TTT

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {α β γ δ ε ζ : Λ} (hβ : (β : TypeIndex) < α) (hγ : (γ : TypeIndex) < β)
  (hδ : (δ : TypeIndex) < γ) (hε : (ε : TypeIndex) < δ) (hζ : (ζ : TypeIndex) < ε)

namespace TSet

theorem exists_inter (x y : TSet α) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z ∈[hβ] x ∧ z ∈[hβ] y := by
  refine exists_of_symmetric {z | z ∈[hβ] x ∧ z ∈[hβ] y} hβ ?_
  obtain ⟨S, hS⟩ := symmetric x hβ
  obtain ⟨T, hT⟩ := symmetric y hβ
  use S + T
  intro ρ hρ
  specialize hS ρ (smul_eq_of_le Support.le_add_right hρ)
  specialize hT ρ (smul_eq_of_le Support.le_add_left hρ)
  simp [Set.ext_iff, Set.mem_smul_set_iff_inv_smul_mem] at hS hT ⊢
  aesop

/- Start of proof attempt -/
lemma round1_exists_compl (x : TSet α) :
    ∃ y : TSet α, ∀ z : TSet β, z ∈[hβ] y ↔ ¬z ∈[hβ] x := by
  refine exists_of_symmetric {z | ¬ z ∈[hβ] x} hβ ?_
  obtain ⟨S, hS⟩ := symmetric x hβ
  use S
  intro ρ hρ
  specialize hS ρ hρ
  simp [Set.ext_iff, Set.mem_smul_set_iff_inv_smul_mem] at hS ⊢
  <;> aesop

theorem exists_compl (x : TSet α) :
    ∃ y : TSet α, ∀ z : TSet β, z ∈[hβ] y ↔ ¬z ∈[hβ] x  := by

  exact round1_exists_compl hβ x
