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

@[simp]
theorem singleton_eq_up_iff (x y z : TSet β) :
    singleton hβ z = up hβ x y ↔ x = z ∧ y = z := by
  rw [← up_eq_singleton_iff hβ x y z, eq_comm]

theorem op_injective {x y z w : TSet γ} (h : op hβ hγ x y = op hβ hγ z w) :
    x = z ∧ y = w := by
  rw [op, op] at h
  simp only [up_inj, singleton_inj, singleton_eq_up_iff, up_eq_singleton_iff] at h
  obtain (⟨rfl, ⟨h, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨⟨rfl, rfl⟩, ⟨h, rfl⟩⟩) := h <;> simp only [and_self]

@[simp]
theorem op_inj (x y z w : TSet γ) :
    op hβ hγ x y = op hβ hγ z w ↔ x = z ∧ y = w := by
  constructor
  · exact op_injective hβ hγ
  · rintro ⟨rfl, rfl⟩
    rfl

/- Start of proof attempt -/
lemma round1_op_eq_singleton_iff (x y : TSet γ) (z : TSet β) :
    op hβ hγ x y = singleton hβ z ↔ singleton hγ x = z ∧ singleton hγ y = z := by
  constructor
  · -- Assume op hβ hγ x y = singleton hβ z
    intro h
    have h1 : op hβ hγ x y = up hβ (singleton hγ x) (up hγ x y) := rfl
    rw [h1] at h
    have h2 : up hβ (singleton hγ x) (up hγ x y) = singleton hβ z := h
    have h21 : singleton hγ x = z ∧ up hγ x y = z := by
      rw [up_eq_singleton_iff hβ (singleton hγ x) (up hγ x y) z] at h2
      tauto
    have h211 : singleton hγ x = z := h21.1
    have h212 : up hγ x y = z := h21.2
    have h23 : up hγ x y = singleton hγ x := by
      have h231 : up hγ x y = z := h212
      have h232 : z = singleton hγ x := by rw [h211]
      rw [h231, h232]
    have h24 : y = x := by
      have h241 : up hγ x y = singleton hγ x := h23
      have h242 : up hγ x y = singleton hγ x ↔ x = x ∧ y = x := by
        exact up_eq_singleton_iff hγ x y x
      have h243 : x = x ∧ y = x := (h242.mp h241)
      tauto
    have h25 : singleton hγ y = singleton hγ x := by
      rw [h24]
    have h26 : singleton hγ y = z := by
      have h261 : singleton hγ y = singleton hγ x := h25
      have h262 : singleton hγ x = z := h211
      rw [h261, h262]
    exact ⟨h211, h26⟩
  · -- Assume singleton hγ x = z ∧ singleton hγ y = z
    rintro ⟨h31, h32⟩
    have h33 : singleton hγ x = singleton hγ y := by
      have h331 : singleton hγ x = z := h31
      have h332 : singleton hγ y = z := h32
      have h333 : singleton hγ x = z := h331
      have h334 : singleton hγ y = z := h332
      have h335 : singleton hγ x = singleton hγ y := by
        rw [h333, h334]
        <;> rfl
      exact h335
    have h34 : x = y := by
      have h341 : singleton hγ x = singleton hγ y := h33
      exact singleton_inj.mp h341
    have h35 : up hγ x y = up hγ x x := by
      rw [h34]
    have h36 : up hγ x x = singleton hγ x := by simp [up_self]
    have h37 : up hγ x y = singleton hγ x := by
      rw [h35, h36]
    have h38 : up hγ x y = z := by
      have h371 : up hγ x y = singleton hγ x := h37
      have h311 : singleton hγ x = z := h31
      rw [h371, h311]
    have h39 : singleton hγ x = z ∧ up hγ x y = z := ⟨h31, h38⟩
    have h40 : up hβ (singleton hγ x) (up hγ x y) = singleton hβ z := by
      rw [up_eq_singleton_iff hβ (singleton hγ x) (up hγ x y) z]
      tauto
    have h41 : op hβ hγ x y = up hβ (singleton hγ x) (up hγ x y) := rfl
    rw [h41]
    exact h40

theorem op_eq_singleton_iff (x y : TSet γ) (z : TSet β) :
    op hβ hγ x y = singleton hβ z ↔ singleton hγ x = z ∧ singleton hγ y = z  := by

  exact round1_op_eq_singleton_iff hβ hγ x y z
