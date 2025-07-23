-- In Seymour/Seymour/Matroid/Notions/IndepAxioms.lean

import Mathlib.Data.Matroid.Basic
import Seymour.Basic

/-- Independence predicate, defines which sets are independent. -/
abbrev IndepPredicate (α : Type) := Set α → Prop

variable {α : Type}

/-- Independence predicate of matroid. -/
def Matroid.IndepPredicate (M : Matroid α) : IndepPredicate α := M.Indep
-- TODO why does this definition exist?

section IndepAxioms

/-- Axiom (I1): empty set is independent. -/
def IndepPredicate.IndepEmpty (P : IndepPredicate α) : Prop := P ∅
alias IndepPredicate.BruhnI1 := IndepPredicate.IndepEmpty

/-- Axiom (I2): subset of independent set is independent. -/
def IndepPredicate.IndepSubset (P : IndepPredicate α) : Prop := ∀ I J : Set α, P J → I ⊆ J → P I
alias IndepPredicate.BruhnI2 := IndepPredicate.IndepSubset

/-- Axiom (I3): augmentation property. -/
def IndepPredicate.IndepAug (P : IndepPredicate α) : Prop :=
  ∀ I B : Set α, P I → ¬Maximal P I → Maximal P B → ∃ x ∈ B \ I, P (x ᕃ I)
alias IndepPredicate.BruhnI3 := IndepPredicate.IndepAug

/-- Axiom (IM): set of all independent sets has the maximal subset property. -/
def IndepPredicate.IndepMaximal (P : IndepPredicate α) (E : Set α) : Prop :=
  ∀ X : Set α, X ⊆ E → Matroid.ExistsMaximalSubsetProperty P X
alias IndepPredicate.BruhnIM := IndepPredicate.IndepMaximal

/-- Every independent set is a subset of the ground set. -/
def IndepPredicate.SubsetGround (P : IndepPredicate α) (E : Set α) : Prop := ∀ C : Set α, P C → C ⊆ E
alias IndepPredicate.BruhnCE := IndepPredicate.SubsetGround

end IndepAxioms

section MatroidIndepAxioms

/-- Independence predicate of matroid satisfies (I1): empty set is independent. -/
lemma Matroid.indepEmpty (M : Matroid α) :
    M.IndepPredicate.IndepEmpty :=
  M.empty_indep

/-- Independence predicate of matroid satisfies (I2): subset of independent set is independent. -/
lemma Matroid.indepSubset (M : Matroid α) :
    M.IndepPredicate.IndepSubset :=
  fun _ _ => Matroid.Indep.subset

/-- Independence predicate of matroid satisfies (I3): augmentation property. -/
lemma Matroid.indepAug (M : Matroid α) :
    M.IndepPredicate.IndepAug :=
  fun _ _ hI nonmaximal_M_I maximal_M_I' => Indep.exists_insert_of_not_maximal M hI nonmaximal_M_I maximal_M_I'

/-- (Alternative proof.) Independence predicate of matroid satisfies (I3): augmentation property. -/
lemma Matroid.indepAug' (M : Matroid α) :
    M.IndepPredicate.IndepAug := by
  -- Follows part of proof from Theorem 4.1 (i) from Bruhn et al.
  intro I I' hI nonmaximal_M_I maximal_M_I'
  have ⟨B, hIB, maximal_B⟩ := M.maximality M.E Set.Subset.rfl I hI (Matroid.Indep.subset_ground hI)
  if hBI : (B \ I).Nonempty then
    obtain ⟨x, hx⟩ := hBI
    if hxI' : x ∈ I' then
      exact ⟨x,
        Set.mem_diff_of_mem hxI' (Set.not_mem_of_mem_diff hx),
        Matroid.Indep.subset maximal_B.left.left (Set.insert_subset (Set.mem_of_mem_diff hx) hIB),
      ⟩
    else
      have hB : Maximal M.Indep B :=
        ⟨maximal_B.left.left, fun C hC hBC => maximal_B.right ⟨hC, Matroid.Indep.subset_ground hC⟩ hBC⟩
      unfold Matroid.IndepPredicate at maximal_M_I'
      rw [←Matroid.base_iff_maximal_indep] at maximal_M_I' hB
      obtain ⟨y, hy, hMyBx⟩ := M.base_exchange B I' hB maximal_M_I' x (Set.mem_diff_of_mem (Set.mem_of_mem_diff hx) hxI')
      exact ⟨y,
        Set.mem_diff_of_mem (Set.mem_of_mem_diff hy) (fun a => (Set.not_mem_of_mem_diff hy) (hIB a)),
        Matroid.Indep.subset (Matroid.Base.indep hMyBx)
          (Set.insert_subset_insert (Set.subset_diff_singleton hIB (Set.not_mem_of_mem_diff hx))),
      ⟩
  else
    have I_eq_B : I = B := Set.union_empty I ▸ (Set.not_nonempty_iff_eq_empty.→ hBI) ▸ Set.union_diff_cancel hIB
    have maximal_B : Maximal M.Indep B :=
      ⟨maximal_B.left.left, fun _ hC hBC => maximal_B.right ⟨hC, Matroid.Indep.subset_ground hC⟩ hBC⟩
    exact (nonmaximal_M_I (I_eq_B ▸ maximal_B)).elim

/- Start of proof attempt -/
lemma round1_matroid_indep_maximal (M : Matroid α) :
    M.IndepPredicate.IndepMaximal M.E := by
  intro X hX
  have h : Matroid.ExistsMaximalSubsetProperty M.Indep X := M.maximality X hX
  have h' : Matroid.ExistsMaximalSubsetProperty M.IndepPredicate X := by
    simpa [Matroid.IndepPredicate] using h
  exact h'

/-- Independence predicate of matroid satisfies (IM): set of all independent sets has the maximal subset property. -/
theorem Matroid.indepMaximal (M : Matroid α) :
    M.IndepPredicate.IndepMaximal M.E  := by

  exact round1_matroid_indep_maximal M
