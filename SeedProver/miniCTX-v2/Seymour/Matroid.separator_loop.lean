-- In Seymour/Seymour/Matroid/Notions/Connectivity.lean

import Seymour.Matroid.Notions.Circuit
import Seymour.Matroid.Notions.Loop
import Seymour.Matroid.Notions.Coloop

variable {α : Type}

section SimpleConnectivity

/-- The connectivity relation, aka ξ in Oxley's book -/
def Matroid.ConnectivityRelation (M : Matroid α) (e f : α) : Prop :=
  e = f ∨ ∃ C : Set α, C ⊆ M.E ∧ M.Circuit C ∧ e ∈ C ∧ f ∈ C

/-- The connectivity relation is reflexive -/
@[refl]
lemma Matroid.ConnectivityRelation.refl (M : Matroid α) {e : α} :
    M.ConnectivityRelation e e :=
  Or.inl rfl

/-- The connectivity relation is symmetric -/
@[symm]
lemma Matroid.ConnectivityRelation.symm (M : Matroid α) {e f : α} :
    M.ConnectivityRelation e f → M.ConnectivityRelation f e := by
  intro hef
  cases hef with
  | inl hef => exact Or.inl hef.symm
  | inr hef =>
    right
    obtain ⟨C, _, _, _, _⟩ := hef
    use C

/-- The connectivity relation is transitive -/
@[trans]
lemma Matroid.ConnectivityRelation.trans (M : Matroid α) {e f g : α} :
    M.ConnectivityRelation e f → M.ConnectivityRelation f g → M.ConnectivityRelation e g := by
  intro hef hfg
  cases hef with
  | inl hef => exact hef ▸ hfg
  | inr hef =>
    cases hfg with
    | inl hfg => exact Or.inr (hfg ▸ hef)
    | inr hfg =>
      obtain ⟨C₁, hC₁, hMC₁, heC₁, hfC₁⟩ := hef
      obtain ⟨C₂, hC₂, hMC₂, hfC₂, hgC₂⟩ := hfg
      right
      -- todo: see proof of Lemma 7 in Bruhn Wollman 2011 (page 5)
      -- note: that proof uses matroid contraction
      sorry

/-- A component is an equivalence class under the connectivity relation, i.e., a ξ-equivalence class -/
def Matroid.Component (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f ↔ f ∈ X

/-- A separator is a union of components -/
def Matroid.Separator (M : Matroid α) (X : Set α) : Prop :=
  ∀ e ∈ X, ∀ f ∈ M.E, M.ConnectivityRelation e f → f ∈ X

/-- Every component is a separator -/
lemma Matroid.separator_component (M : Matroid α) {X : Set α} (hX : M.Component X) :
    M.Separator X :=
  fun e he f hf hef => (hX e he f hf).→ hef

/- Start of proof attempt -/
lemma round1_separator_loop {α : Type} (M : Matroid α) (x : α) (hx : M.Loop x) :
    M.Separator {x} := by
  intro e he f hf h1
  have he_eq_x : e = x := by simpa using he
  have h2 : M.ConnectivityRelation x f := by
    rw [he_eq_x] at h1
    exact h1
  have h3 : x = f ∨ ∃ C : Set α, C ⊆ M.E ∧ M.Circuit C ∧ x ∈ C ∧ f ∈ C := by
    simpa [Matroid.ConnectivityRelation] using h2
  rcases h3 with (h3 | h3)
  · -- Case 1: x = f
    have h4 : f = x := by tauto
    simp [h4]
  · -- Case 2: ∃ C : Set α, C ⊆ M.E ∧ M.Circuit C ∧ x ∈ C ∧ f ∈ C
    rcases h3 with ⟨C, hC1, hC2, hx_in_C, hf_in_C⟩
    by_cases h61 : f = x
    · -- Subcase 2.1: f = x
      simp [h61]
    · -- Subcase 2.2: f ≠ x
      have h61' : f ≠ x := h61
      have h5 : M.Indep (C \ {f}) := by
        exact?
      have h62 : x ∈ C \ {f} := by
        have h621 : x ∈ C := hx_in_C
        have h622 : x ∉ ({f} : Set α) := by
          simp [h61']
          <;> aesop
        exact Set.mem_diff_of_mem h621 h622
      have h63 : ({x} : Set α) ⊆ C \ {f} := by
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        rw [hz]
        exact h62
      have h64 : M.Indep ({x} : Set α) := by
        exact?
      have h65 : M.Dep ({x} : Set α) := hx.2
      have h651 : ¬M.Indep ({x} : Set α) := by
        have h652 : M.Dep ({x} : Set α) := h65
        have h653 : ¬M.Indep ({x} : Set α) := by
          exact?
        exact h653
      contradiction

/-- Every loop is a separator -/
theorem Matroid.separator_loop {M : Matroid α} {x : α} (hx : M.Loop x) :
    M.Separator {x}  := by

  exact round1_separator_loop M x hx
