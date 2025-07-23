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

/- Start of proof attempt -/
lemma round1_Matroid_indepAug' (M : Matroid α) :
    M.IndepPredicate.IndepAug  := by
  exact Matroid.indepAug M

/-- (Alternative proof.) Independence predicate of matroid satisfies (I3): augmentation property. -/
theorem Matroid.indepAug' (M : Matroid α) :
    M.IndepPredicate.IndepAug  := by

  exact round1_Matroid_indepAug' M
