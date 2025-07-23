-- In Seymour/Seymour/Matroid/Classes/Binary.lean

import Seymour.Basic
import Seymour.Matroid.Constructors.VectorMatroid
import Seymour.Matroid.Classes.Representable

variable {α : Type}

section Definitions

/-- Binary matroid is vector matroid of matrix over `Z2`. -/
abbrev BinaryMatroid (α : Type) := VectorMatroid α Z2

/-- Matroid `M` is binary if it is representable over `Z2` -/
def Matroid.IsBinary [DecidableEq α] (M : Matroid α) : Prop :=
  M.IsRepresentableOver Z2

/-- `Matroid` is binary iff it can be constructed from a `BinaryMatroid`. -/
lemma Matroid.isBinary_iff [DecidableEq α] (M : Matroid α) : M.IsBinary ↔ ∃ B : BinaryMatroid α, B.toMatroid = M := by
  rfl

/- Start of proof attempt -/
lemma round1_h1 [DecidableEq α] (M : BinaryMatroid α) : ∃ (B : BinaryMatroid α), B.toMatroid = M.toMatroid := by
  refine ⟨M, rfl⟩

/-- Every `BinaryMatroid` is binary. -/
theorem BinaryMatroid.isBinary [DecidableEq α] (M : BinaryMatroid α) : M.toMatroid.IsBinary  := by

  have h : M.toMatroid.IsBinary ↔ ∃ (B : BinaryMatroid α), B.toMatroid = M.toMatroid := Matroid.isBinary_iff (M.toMatroid)
  have h1 : ∃ (B : BinaryMatroid α), B.toMatroid = M.toMatroid := round1_h1 M
  rw [h]
  exact h1
