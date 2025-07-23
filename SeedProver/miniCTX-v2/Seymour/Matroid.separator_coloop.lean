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

/-- Every loop is a separator -/
lemma Matroid.separator_loop {M : Matroid α} {x : α} (hx : M.Loop x) :
    M.Separator {x} := by
  intro e hex f hfE hf
  cases hf with
  | inl hef => exact Set.mem_of_eq_of_mem hef.symm hex
  | inr hfC =>
    obtain ⟨C, hCE, circC, heC, hfC⟩ := hfC
    rw [hex, ←Set.singleton_subset_iff] at heC
    rw [Matroid.loop_iff_circuit] at hx
    apply Matroid.Circuit.not_ssubset_circuit hx at circC
    rw [Set.ssubset_def] at circC
    push_neg at circC
    exact circC heC hfC

/- Start of proof attempt -/
lemma round1_separator_coloop {M : Matroid α} {x : α} (hx : M.Coloop x) :
    M.Separator {x} := by
  intro e he f hf hef
  have h11 : e = x := by simpa using he
  have h12 : M.ConnectivityRelation e f := hef
  rw [h11] at h12
  have h13 : M.ConnectivityRelation x f := h12
  have h14 : x = f ∨ ∃ (C : Set α), C ⊆ M.E ∧ M.Circuit C ∧ x ∈ C ∧ f ∈ C := h13
  cases h14 with
  | inl h15 =>
    have h16 : x = f := h15
    have h17 : f = x := by tauto
    have h18 : f ∈ ({x} : Set α) := by
      simp [h17]
    tauto
  | inr h15 =>
    rcases h15 with ⟨C, hC1, hC2, hC3, hC4⟩
    have h19 : ∀ (C : Set α), M.Circuit C → x ∉ C := (Matroid.coloop_iff_in_no_circuit M).mp hx |>.2
    have h20 : x ∉ C := h19 C hC2
    contradiction

/-- Every coloop is a separator -/
theorem Matroid.separator_coloop {M : Matroid α} {x : α} (hx : M.Coloop x) :
    M.Separator {x}  := by

  exact round1_separator_coloop hx
