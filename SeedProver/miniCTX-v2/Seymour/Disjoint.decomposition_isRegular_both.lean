-- In Seymour/Seymour/Matroid/Operations/Sum1/Regularity.lean

import Seymour.Matroid.Operations.Sum1.Basic
import Seymour.Matroid.Classes.Regular

variable {α : Type} [DecidableEq α] {M₁ M₂ : Matroid α} [Fintype M₁.E.Elem] [Fintype M₂.E.Elem]

section Composition

lemma Disjoint.build1sum_isRepresentedBy {R X₁ X₂ : Type} [Ring R] {A₁ : Matrix X₁ M₁.E R} {A₂ : Matrix X₂ M₂.E R}
    (hE : M₁.E ⫗ M₂.E) (hA₁ : M₁.IsRepresentedBy A₁) (hA₂ : M₂.IsRepresentedBy A₂) :
    hE.build1sum.IsRepresentedBy (Matrix.fromBlocks A₁ 0 0 A₂) := by
  sorry

end Composition

section Decomposition

/-- todo: desc-/
lemma Matroid.oneSum.ofRepr₁ {X R : Type} [Ring R] (hE : M₁.E ⫗ M₂.E) {A : Matrix X hE.build1sum.E R}
    (hA : have : Fintype hE.build1sum.E := (by sorry); -- should be somewhere already
      hE.build1sum.IsRepresentedBy A) :
    ∃ X₁ : Type, ∃ A₁ : Matrix X₁ M₁.E R, M₁.IsRepresentedBy A₁ :=
  sorry

/-- todo: desc-/
lemma Matroid.oneSum.ofRepr₂ {X R : Type} [Ring R] (hE : M₁.E ⫗ M₂.E) {A : Matrix X hE.build1sum.E R}
    (hA : have : Fintype hE.build1sum.E := (by sorry); -- should be somewhere already
      hE.build1sum.IsRepresentedBy A) :
    ∃ X₂ : Type, ∃ A₂ : Matrix X₂ M₂.E R, M₂.IsRepresentedBy A₂ :=
  sorry

/-- If a regular matroid is a 1-sum of binary matroids, the left summand is regular. -/
lemma Disjoint.decomposition_isRegular_left (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₁.IsRegular := by
  sorry

/-- If a regular matroid is a 1-sum of binary matroids, the right summand is regular. -/
lemma Disjoint.decomposition_isRegular_right (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₂.IsRegular :=
  hE.symm.decomposition_isRegular_left (hE.symm.build1sum_comm ▸ regularity)

/- Start of proof attempt -/
lemma round1_decomposition_isRegular_both (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₁.IsRegular ∧ M₂.IsRegular := by
  have h1 : M₁.IsRegular := Disjoint.decomposition_isRegular_left hE regularity
  have h2 : M₂.IsRegular := Disjoint.decomposition_isRegular_right hE regularity
  exact ⟨h1, h2⟩

/-- If a regular matroid is a 1-sum of binary matroids, both summand matroids are regular. -/
theorem Disjoint.decomposition_isRegular_both (hE : M₁.E ⫗ M₂.E) (regularity : hE.build1sum.IsRegular) :
    M₁.IsRegular ∧ M₂.IsRegular  := by

  exact round1_decomposition_isRegular_both hE regularity
