-- In Seymour/Seymour/ForMathlib/Basic.lean

import Mathlib.Tactic

/- Start of proof attempt -/
lemma round1_h5 (α β : Type)
  [Fintype α]
  [Fintype β]
  (n : ℕ)
  (hα : Fintype.card α < n)
  (hn : n ≤ Fintype.card α + Fintype.card β):
  ∃ (b : Finset β), Finset.card b = n - Fintype.card α := by
  have h3 : 0 < n - Fintype.card α := by omega
  have h4 : n - Fintype.card α ≤ Fintype.card β := by omega
  have h4' : n - Fintype.card α ≤ (Finset.univ : Finset β).card := by
    have h41 : (Finset.univ : Finset β).card = Fintype.card β := by simp
    linarith
  have h51 : ∃ (b : Finset β), b ⊆ Finset.univ ∧ Finset.card b = n - Fintype.card α := by
    exact?
  rcases h51 with ⟨b, h511, h512⟩
  refine ⟨b, h512⟩

lemma round1_h7 (α β : Type)
  [Fintype α]
  [Fintype β]
  (n : ℕ)
  (b : Finset β)
  (h5 : Finset.card b = n - Fintype.card α)
  (hα : Fintype.card α < n):
  0 < Finset.card b := by
  omega

lemma round1_h10 (α β : Type)
  [Fintype α]
  [Fintype β]
  (n : ℕ)
  (b : Finset β)
  (h5 : Finset.card b = n - Fintype.card α)
  (hα : Fintype.card α < n):
  Fintype.card (α ⊕ b) = n := by
  have h11 : Fintype.card (α ⊕ b) = Fintype.card α + Finset.card b := by
    simp [Fintype.card_sum]
    <;>
    aesop
  rw [h11]
  omega

lemma round1_h11 (α β : Type)
  [Fintype α]
  [Fintype β]
  (n : ℕ)
  (b : Finset β)
  (h5 : Finset.card b = n - Fintype.card α)
  (hα : Fintype.card α < n)
  (h7 : 0 < Finset.card b):
  Nonempty b := by
  have h111 : 0 < Finset.card b := h7
  have h112 : b.Nonempty := Finset.card_pos.mp h111
  rcases h112 with ⟨x, hx⟩
  refine ⟨⟨x, hx⟩⟩

theorem finset_of_cardinality_between {α β : Type} [Fintype α] [Fintype β] {n : ℕ}
    (hα : Fintype.card α < n) (hn : n ≤ Fintype.card α + Fintype.card β) :
    ∃ b : Finset β, Fintype.card (α ⊕ b) = n ∧ Nonempty b  := by

  have h5 : ∃ (b : Finset β), Finset.card b = n - Fintype.card α := by
    exact round1_h5 α β n hα hn
  obtain ⟨b, h5⟩ := h5
  have h7 : 0 < Finset.card b := by
    exact round1_h7 α β n b h5 hα
  have h10 : Fintype.card (α ⊕ b) = n := by
    exact round1_h10 α β n b h5 hα
  have h11 : Nonempty b := by
    exact round1_h11 α β n b h5 hα h7
  refine ⟨b, ⟨h10, h11⟩⟩
