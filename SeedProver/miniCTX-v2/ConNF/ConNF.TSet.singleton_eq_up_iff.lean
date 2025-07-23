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

theorem exists_up (x y : TSet β) :
    ∃ w : TSet α, ∀ z : TSet β, z ∈[hβ] w ↔ z = x ∨ z = y := by
  refine exists_of_symmetric {x, y} hβ ?_
  obtain ⟨S, hS⟩ := exists_support x
  obtain ⟨T, hT⟩ := exists_support y
  use (S + T) ↗ hβ
  intro ρ hρ
  rw [Support.smul_scoderiv, Support.scoderiv_inj, ← allPermSderiv_forget'] at hρ
  specialize hS (ρ ↘ hβ) (smul_eq_of_le Support.le_add_right hρ)
  specialize hT (ρ ↘ hβ) (smul_eq_of_le Support.le_add_left hρ)
  simp only [Set.smul_set_def, Set.image, Set.mem_insert_iff, Set.mem_singleton_iff,
    exists_eq_or_imp, hS, exists_eq_left, hT]
  ext z
  rw [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  aesop

/-- The unordered pair. -/
def up (x y : TSet β) : TSet α :=
  (exists_up hβ x y).choose

@[simp]
theorem mem_up_iff (x y z : TSet β) :
    z ∈[hβ] up hβ x y ↔ z = x ∨ z = y :=
  (exists_up hβ x y).choose_spec z

/-- The Kuratowski ordered pair. -/
def op (x y : TSet γ) : TSet α :=
  up hβ (singleton hγ x) (up hγ x y)

theorem up_injective {x y z w : TSet β} (h : up hβ x y = up hβ z w) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have h₁ := mem_up_iff hβ x y z
  have h₂ := mem_up_iff hβ x y w
  have h₃ := mem_up_iff hβ z w x
  have h₄ := mem_up_iff hβ z w y
  rw [h, mem_up_iff] at h₁ h₂
  rw [← h, mem_up_iff] at h₃ h₄
  aesop

@[simp]
theorem up_inj (x y z w : TSet β) :
    up hβ x y = up hβ z w ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  constructor
  · exact up_injective hβ
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · apply tSet_ext' hβ
      aesop

@[simp]
theorem up_self {x : TSet β} :
    up hβ x x = singleton hβ x := by
  apply tSet_ext' hβ
  aesop

@[simp]
theorem up_eq_singleton_iff (x y z : TSet β) :
    up hβ x y = singleton hβ z ↔ x = z ∧ y = z := by
  constructor
  · intro h
    have h₁ := typedMem_singleton_iff' hβ z x
    have h₂ := typedMem_singleton_iff' hβ z y
    rw [← h, mem_up_iff] at h₁ h₂
    aesop
  · rintro ⟨rfl, rfl⟩
    rw [up_self]

/- Start of proof attempt -/
lemma round1_singleton_eq_up_iff (x y z : TSet β) :
    singleton hβ z = up hβ x y ↔ x = z ∧ y = z := by
  constructor
  · -- Assume `singleton hβ z = up hβ x y`, we need to prove `x = z ∧ y = z`
    intro h
    have hx : x ∈[hβ] up hβ x y := by
      rw [mem_up_iff]
      <;> simp
    have hx2 : x ∈[hβ] singleton hβ z := by
      have h6 : singleton hβ z = up hβ x y := h
      rw [h6]
      exact hx
    have hx3 : x = z := by
      rw [typedMem_singleton_iff'] at hx2
      tauto
    have hy : y ∈[hβ] up hβ x y := by
      rw [mem_up_iff]
      <;> simp
    have hy2 : y ∈[hβ] singleton hβ z := by
      have h6 : singleton hβ z = up hβ x y := h
      rw [h6]
      exact hy
    have hy3 : y = z := by
      rw [typedMem_singleton_iff'] at hy2
      tauto
    exact ⟨hx3, hy3⟩
  · -- Assume `x = z ∧ y = z`, we need to prove `singleton hβ z = up hβ x y`
    rintro ⟨h1, h2⟩
    have h3 : up hβ x y = up hβ z z := by
      rw [h1, h2]
    have h4 : up hβ z z = singleton hβ z := by
      rw [up_self]
    have h5 : up hβ x y = singleton hβ z := by
      rw [h3, h4]
    rw [h5]
    <;> simp

theorem singleton_eq_up_iff (x y z : TSet β) :
    singleton hβ z = up hβ x y ↔ x = z ∧ y = z  := by

  exact round1_singleton_eq_up_iff hβ x y z
