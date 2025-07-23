-- In Seymour/Seymour/Matroid/Operations/MatrixSums/BinaryMatroids.lean

import Mathlib.Data.Matroid.IndepAxioms

import Seymour.Basic
import Seymour.ForMathlib.SetTheory

/-- Data describing a binary matroid on the ground set `X ∪ Y` where `X` and `Y` are bundled.
Not in sync with `Matroid.Constructors.VectorMatroid/StandardRepr` currently! -/
structure StandardRepresentation (α : Type) [DecidableEq α] where
  /-- Basis elements → row indices of [`1 | B`] -/
  X : Set α
  /-- Non-basis elements → column indices of `B` -/
  Y : Set α
  /-- Necessary decidability -/
  decmemX : ∀ a, Decidable (a ∈ X)
  /-- Necessary decidability -/
  decmemY : ∀ a, Decidable (a ∈ Y)
  /-- Basis and nonbasis elements are disjoint -/
  hXY : X ⫗ Y
  /-- The standard representation matrix -/
  B : Matrix X Y Z2

-- Automatically infer decidability when `StandardRepresentation` is present.
attribute [instance] StandardRepresentation.decmemX
attribute [instance] StandardRepresentation.decmemY

variable {α : Type} [DecidableEq α] {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)]

/-- Given matrix `B`, whether the set of columns `S` in the (standard) representation [`1 | B`] `Z2`-independent. -/
def Matrix.IndepCols (B : Matrix X Y Z2) (S : Set α) : Prop :=
  ∃ hs : S ⊆ X ∪ Y, LinearIndependent Z2 ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ hs.elem)).transpose

/-- The empty set of columns is linearly independent. -/
theorem Matrix.indepCols_empty {B : Matrix X Y Z2} : B.IndepCols ∅ := by
  use Set.empty_subset (X ∪ Y)
  exact linearIndependent_empty_type

/- Start of proof attempt -/
lemma round1_indepCols_subset {B : Matrix X Y Z2} (I J : Set α) (hBJ : B.IndepCols J) (hIJ : I ⊆ J) :
    ∃ (hs : I ⊆ X ∪ Y), LinearIndependent Z2 ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ hs.elem)).transpose := by
  rcases hBJ with ⟨hsJ, hlin⟩
  have h4 : I ⊆ X ∪ Y := by
    exact Set.Subset.trans hIJ hsJ
  have h5 : ∀ (x : I), (x : α) ∈ J := by
    intro x
    exact hIJ x.2
  have h6 : Function.Injective (fun (x : I) => (⟨(x : α), h5 x⟩ : J)) := by
    intro x1 x2 h
    simp at h
    <;> aesop
  have h7 : LinearIndependent Z2 ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ h4.elem)).transpose := by
    have h9 : LinearIndependent Z2 (fun (i : I) => ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ hsJ.elem)).transpose (⟨(i : α), h5 i⟩ : J)) := by
      exact LinearIndependent.comp hlin (fun (x : I) => (⟨(x : α), h5 x⟩ : J)) h6
    have h10 : (fun (i : I) => ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ hsJ.elem)).transpose (⟨(i : α), h5 i⟩ : J)) = (fun (i : I) => ((Matrix.fromCols 1 B).submatrix id (Subtype.toSum ∘ h4.elem)).transpose i) := by
      funext i
      simp [Subtype.ext_iff]
      <;> aesop
    rw [h10] at h9
    simpa using h9
  refine ⟨h4, h7⟩

/-- A subset of a linearly independent set of columns is linearly independent. -/
theorem Matrix.indepCols_subset {B : Matrix X Y Z2} (I J : Set α) (hBJ : B.IndepCols J) (hIJ : I ⊆ J) :
    B.IndepCols I  := by

  exact round1_indepCols_subset I J hBJ hIJ
