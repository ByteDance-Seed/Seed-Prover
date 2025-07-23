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

theorem exists_compl (x : TSet α) :
    ∃ y : TSet α, ∀ z : TSet β, z ∈[hβ] y ↔ ¬z ∈[hβ] x := by
  refine exists_of_symmetric {z | ¬z ∈[hβ] x} hβ ?_
  obtain ⟨S, hS⟩ := symmetric x hβ
  use S
  intro ρ hρ
  specialize hS ρ hρ
  simp [Set.ext_iff, Set.mem_smul_set_iff_inv_smul_mem] at hS ⊢
  aesop

/- Start of proof attempt -/
lemma round1_exists_up (x y : TSet β) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z = x ∨ z = y := by
  set sx : TSet α := ConNF.singleton hβ x with h_sx
  set sy : TSet α := ConNF.singleton hβ y with h_sy
  rcases exists_compl hβ sx with ⟨sx', h_sx'⟩
  rcases exists_compl hβ sy with ⟨sy', h_sy'⟩
  rcases exists_inter hβ sx' sy' with ⟨sx'_inter_sy', h_sx'_inter_sy'⟩
  rcases exists_compl hβ sx'_inter_sy' with ⟨w, h_w⟩
  refine ⟨w, fun z => ?_⟩
  have h1 : z ∈[hβ] w ↔ ¬(z ∈[hβ] sx'_inter_sy') := h_w z
  have h2 : z ∈[hβ] sx'_inter_sy' ↔ z ∈[hβ] sx' ∧ z ∈[hβ] sy' := h_sx'_inter_sy' z
  have h3 : z ∈[hβ] sx' ↔ ¬(z ∈[hβ] sx) := h_sx' z
  have h4 : z ∈[hβ] sy' ↔ ¬(z ∈[hβ] sy) := h_sy' z
  have h5 : z ∈[hβ] sx ↔ z = x := by
    have h51 : z ∈[hβ] ConNF.singleton hβ x ↔ z = x := ConNF.typedMem_singleton_iff' hβ x z
    have h52 : sx = ConNF.singleton hβ x := by simp [h_sx]
    rw [h52]
    exact h51
  have h6 : z ∈[hβ] sy ↔ z = y := by
    have h61 : z ∈[hβ] ConNF.singleton hβ y ↔ z = y := ConNF.typedMem_singleton_iff' hβ y z
    have h62 : sy = ConNF.singleton hβ y := by simp [h_sy]
    rw [h62]
    exact h61
  tauto

theorem exists_up (x y : TSet β) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z = x ∨ z = y  := by

  exact round1_exists_up hβ x y
