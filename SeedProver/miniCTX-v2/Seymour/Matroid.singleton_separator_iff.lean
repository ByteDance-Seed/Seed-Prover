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

/-- Every coloop is a separator -/
lemma Matroid.separator_coloop {M : Matroid α} {x : α} (hx : M.Coloop x) :
    M.Separator {x} := by
  intro e hex f hfE hf
  cases hf with
  | inl hef => exact Set.mem_of_eq_of_mem hef.symm hex
  | inr hfC =>
    rw [Matroid.coloop_iff_in_no_circuit] at hx
    obtain ⟨_hxE, hxC⟩ := hx
    obtain ⟨C, _hCE, hCcirc, heC, hfC⟩ := hfC
    rw [hex, ←Set.singleton_subset_iff] at heC
    specialize hxC C hCcirc
    tauto

/-- Every singleton separator is a loop or a coloop -/
lemma Matroid.singleton_separator_loop_coloop {M : Matroid α} {x : α} (hx : x ∈ M.E) :
    M.Separator {x} → M.Loop x ∨ M.Coloop x := by
  intro sep_x
  by_contra! contr
  obtain ⟨notLoop, notColoop⟩ := contr
  rw [Matroid.loop_iff_circuit] at notLoop
  rw [Matroid.coloop_iff_in_no_circuit] at notColoop
  push_neg at notColoop
  specialize notColoop hx
  obtain ⟨C, hC, hxC⟩ := notColoop
  obtain ⟨f, hfC, hfx⟩ : ∃ f ∈ C, f ≠ x
  · by_contra! hf
    have hCx : ∀ f ∈ C, f ∈ ({x} : Set α)
    · by_contra! hg
      obtain ⟨f', hf'⟩ := hg
      exact (hf f' hf'.left ▸ hf'.right) rfl
    have x_sub_C : {x} ⊆ C := Set.singleton_subset_iff.← hxC
    have hCeqx : {x} = C := x_sub_C.antisymm hf
    rw [hCeqx] at notLoop
    exact notLoop hC
  have hCE := hC.subset_ground
  exact hfx (sep_x x rfl f (hCE hfC) (Or.inr ⟨C, hCE, hC, hxC, hfC⟩))

/- Start of proof attempt -/
lemma round1_forward_direction {M : Matroid α} (x : α) (h : x ∈ M.E ∧ M.Separator {x}) :
    M.Loop x ∨ M.Coloop x := by
  obtain ⟨hx, h1⟩ := h
  exact Matroid.singleton_separator_loop_coloop hx h1

lemma round1_backward_direction {M : Matroid α} (x : α) (h : M.Loop x ∨ M.Coloop x) :
    x ∈ M.E ∧ M.Separator {x} := by
  cases h with
  | inl h2 =>
    have hx1 : x ∈ M.E := by
      have h4 : M.Loop x := h2
      have h5 : x ∈ M.E := by
        exact?
      exact h5
    have h5 : M.Separator {x} := Matroid.separator_loop h2
    exact ⟨hx1, h5⟩
  | inr h2 =>
    have hx2 : x ∈ M.E := by
      have h4 : M.Coloop x := h2
      have h5 : x ∈ M.E := by
        exact?
      exact h5
    have h5 : M.Separator {x} := Matroid.separator_coloop h2
    exact ⟨hx2, h5⟩

/-- Singleton element is a separator iff it is a loop or a coloop -/
theorem Matroid.singleton_separator_iff {M : Matroid α} (x : α) :
    x ∈ M.E ∧ M.Separator {x} ↔ M.Loop x ∨ M.Coloop x  := by

  constructor
  · exact round1_forward_direction x
  · exact round1_backward_direction x
