-- In Seymour/Seymour/Matroid/Operations/MatrixSums/Sum3.lean

import Seymour.Matroid.Operations.MatrixSums.BinaryMatroids

/-!
This file contains everything about 3-sum of binary matroids — the old version (in terms of explicit matrices).
-/

variable {α : Type}

/-- `Matrix`-level 3-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
noncomputable abbrev Matrix_3sumComposition {β : Type} [CommRing β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ (Y₁ ⊕ Fin 2) β) (A₂ : Matrix (Fin 2 ⊕ X₂) Y₂ β)
    (z₁ : Y₁ → β) (z₂ : X₂ → β) (D : Matrix (Fin 2) (Fin 2) β) (D₁ : Matrix (Fin 2) Y₁ β) (D₂ : Matrix X₂ (Fin 2) β) :
    Matrix ((X₁ ⊕ Unit) ⊕ (Fin 2 ⊕ X₂)) ((Y₁ ⊕ Fin 2) ⊕ (Unit ⊕ Y₂)) β :=
  -- Unfortunately `Ring.inverse` is `noncomputable` and upgrading `β` to `Field` does not help.
  let D₁₂ : Matrix X₂ Y₁ β := D₂ * D⁻¹ * D₁
  Matrix.fromBlocks
    (Matrix.fromRows A₁ (Matrix.row Unit (Sum.elim z₁ ![1, 1]))) 0
    (Matrix.fromBlocks D₁ D D₁₂ D₂) (Matrix.fromCols (Matrix.col Unit (Sum.elim ![1, 1] z₂)) A₂)

variable [DecidableEq α] {M₁ M₂ : StandardRepresentation α}

/-- `StandardRepresentation`-level 3-sum of two matroids.
The second part checks legitimacy (invertibility of a certain 2x2 submatrix and specific 1s and 0s on concrete positions). -/
noncomputable def StandardRepresentation_3sum {x₁ x₂ x₃ y₁ y₂ y₃ : α}
    (hXX : M₁.X ∩ M₂.X = {x₁, x₂, x₃}) (hYY : M₁.Y ∩ M₂.Y = {y₁, y₂, y₃}) (hXY : M₁.X ⫗ M₂.Y) (hYX : M₁.Y ⫗ M₂.X) :
    StandardRepresentation α × Prop :=
  have hxxx₁ : {x₁, x₂, x₃} ⊆ M₁.X := hXX.symm.subset.trans Set.inter_subset_left
  have hxxx₂ : {x₁, x₂, x₃} ⊆ M₂.X := hXX.symm.subset.trans Set.inter_subset_right
  have hyyy₁ : {y₁, y₂, y₃} ⊆ M₁.Y := hYY.symm.subset.trans Set.inter_subset_left
  have hyyy₂ : {y₁, y₂, y₃} ⊆ M₂.Y := hYY.symm.subset.trans Set.inter_subset_right
  have x₁inX₁ : x₁ ∈ M₁.X := hxxx₁ (Set.mem_insert x₁ {x₂, x₃})
  have x₁inX₂ : x₁ ∈ M₂.X := hxxx₂ (Set.mem_insert x₁ {x₂, x₃})
  have x₂inX₁ : x₂ ∈ M₁.X := hxxx₁ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
  have x₂inX₂ : x₂ ∈ M₂.X := hxxx₂ (Set.insert_comm x₁ x₂ {x₃} ▸ Set.mem_insert x₂ {x₁, x₃})
  have x₃inX₁ : x₃ ∈ M₁.X := hxxx₁ (by simp)
  have x₃inX₂ : x₃ ∈ M₂.X := hxxx₂ (by simp)
  have y₃inY₁ : y₃ ∈ M₁.Y := hyyy₁ (by simp)
  have y₃inY₂ : y₃ ∈ M₂.Y := hyyy₂ (by simp)
  have y₂inY₁ : y₂ ∈ M₁.Y := hyyy₁ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₂inY₂ : y₂ ∈ M₂.Y := hyyy₂ (Set.insert_comm y₁ y₂ {y₃} ▸ Set.mem_insert y₂ {y₁, y₃})
  have y₁inY₁ : y₁ ∈ M₁.Y := hyyy₁ (Set.mem_insert y₁ {y₂, y₃})
  have y₁inY₂ : y₁ ∈ M₂.Y := hyyy₂ (Set.mem_insert y₁ {y₂, y₃})
  -- The actual definition starts here:
  let A₁ : Matrix (M₁.X \ {x₁, x₂, x₃}).Elem ((M₁.Y \ {y₁, y₂, y₃}).Elem ⊕ Fin 2) Z2 := -- the top left submatrix
    Matrix.of (fun i j => M₁.B
        ⟨i.val, Set.mem_of_mem_diff i.property⟩
        (j.casesOn (fun j' => ⟨j'.val, Set.mem_of_mem_diff j'.property⟩) ![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩]))
  let A₂ : Matrix (Fin 2 ⊕ (M₂.X \ {x₁, x₂, x₃}).Elem) (M₂.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom right submatrix
    Matrix.of (fun i j => M₂.B
        (i.casesOn ![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] (fun i' => ⟨i'.val, Set.mem_of_mem_diff i'.property⟩))
        ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₁ : (M₁.Y \ {y₁, y₂, y₃}).Elem → Z2 := -- the middle left "row vector"
    (fun j => M₁.B ⟨x₁, x₁inX₁⟩ ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let z₂ : (M₂.X \ {x₁, x₂, x₃}).Elem → Z2 := -- the bottom middle "column vector"
    (fun i => M₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ ⟨y₃, y₃inY₂⟩)
  let D_₁ : Matrix (Fin 2) (Fin 2) Z2 := -- the bottom middle 2x2 submatrix
    Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) (![⟨y₂, y₂inY₁⟩, ⟨y₁, y₁inY₁⟩] j))
  let D_₂ : Matrix (Fin 2) (Fin 2) Z2 := -- the middle left 2x2 submatrix
    Matrix.of (fun i j => M₂.B (![⟨x₂, x₂inX₂⟩, ⟨x₃, x₃inX₂⟩] i) (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
  let D₁ : Matrix (Fin 2) (M₁.Y \ {y₁, y₂, y₃}).Elem Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => M₁.B (![⟨x₂, x₂inX₁⟩, ⟨x₃, x₃inX₁⟩] i) ⟨j.val, Set.mem_of_mem_diff j.property⟩)
  let D₂ : Matrix (M₂.X \ {x₁, x₂, x₃}).Elem (Fin 2) Z2 := -- the bottom left submatrix
    Matrix.of (fun i j => M₂.B ⟨i.val, Set.mem_of_mem_diff i.property⟩ (![⟨y₂, y₂inY₂⟩, ⟨y₁, y₁inY₂⟩] j))
  ⟨
    ⟨
      (M₁.X \ {x₁, x₂, x₃}) ∪ M₂.X,
      M₁.Y ∪ (M₂.Y \ {y₁, y₂, y₃}),
      inferInstance,
      inferInstance,
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact
          ⟨⟨M₁.hXY.disjoint_sdiff_left, hYX.symm⟩, ⟨hXY.disjoint_sdiff_right.disjoint_sdiff_left, M₂.hXY.disjoint_sdiff_right⟩⟩,
      Matrix.of (fun i j =>
        Matrix_3sumComposition A₁ A₂ z₁ z₂ D_₁ D₁ D₂ (
          if hi₁ : i.val ∈ M₁.X \ {x₁, x₂, x₃} then Sum.inl (Sum.inl ⟨i, hi₁⟩) else
          if hi₂ : i.val ∈ M₂.X \ {x₁, x₂, x₃} then Sum.inr (Sum.inr ⟨i, hi₂⟩) else
          if hx₁ : i.val = x₁ then Sum.inl (Sum.inr ()) else
          if hx₂ : i.val = x₂ then Sum.inr (Sum.inl 0) else
          if hx₃ : i.val = x₃ then Sum.inr (Sum.inl 1) else
          (i.property.elim hi₁ (by simp_all)).elim
          -- TODO can `Matrix.toMatrixUnionUnion` be combined with something else to simplify this definition?
        ) (
          if hj₁ : j.val ∈ M₁.Y \ {y₁, y₂, y₃} then Sum.inl (Sum.inl ⟨j, hj₁⟩) else
          if hj₂ : j.val ∈ M₂.Y \ {y₁, y₂, y₃} then Sum.inr (Sum.inr ⟨j, hj₂⟩) else
          if hy₁ : j.val = y₁ then Sum.inl (Sum.inr 1) else
          if hy₂ : j.val = y₂ then Sum.inl (Sum.inr 0) else
          if hy₃ : j.val = y₃ then Sum.inr (Sum.inl ()) else
          (j.property.elim (by simp_all) hj₂).elim
        )
      )
    ⟩,
    IsUnit D_₁ ∧ D_₁ = D_₂ -- the matrix `D_₁ = D_₂` (called D-bar in the book) is invertible
    ∧ M₁.B ⟨x₁, x₁inX₁⟩ ⟨y₁, y₁inY₁⟩ = 1
    ∧ M₁.B ⟨x₁, x₁inX₁⟩ ⟨y₂, y₂inY₁⟩ = 1
    ∧ M₁.B ⟨x₂, x₂inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
    ∧ M₁.B ⟨x₃, x₃inX₁⟩ ⟨y₃, y₃inY₁⟩ = 1
    ∧ M₂.B ⟨x₁, x₁inX₂⟩ ⟨y₁, y₁inY₂⟩ = 1
    ∧ M₂.B ⟨x₁, x₁inX₂⟩ ⟨y₂, y₂inY₂⟩ = 1
    ∧ M₂.B ⟨x₂, x₂inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
    ∧ M₂.B ⟨x₃, x₃inX₂⟩ ⟨y₃, y₃inY₂⟩ = 1
    ∧ (∀ x : α, ∀ hx : x ∈ M₁.X, x ≠ x₂ ∧ x ≠ x₃ → M₁.B ⟨x, hx⟩ ⟨y₃, y₃inY₁⟩ = 0) -- the rest of the rightmost column is `0`s
    ∧ (∀ y : α, ∀ hy : y ∈ M₂.Y, y ≠ y₂ ∧ y ≠ y₁ → M₂.B ⟨x₁, x₁inX₂⟩ ⟨y, hy⟩ = 0) -- the rest of the topmost row is `0`s
  ⟩

/-- Binary matroid `M` is a result of 3-summing `M₁` and `M₂` in some way. -/
def StandardRepresentation.Is3sumOf (M : StandardRepresentation α) (M₁ M₂ : StandardRepresentation α) : Prop :=
  ∃ x₁ x₂ x₃ y₁ y₂ y₃ : α,
    ∃ hXX : M₁.X ∩ M₂.X = {x₁, x₂, x₃}, ∃ hYY : M₁.Y ∩ M₂.Y = {y₁, y₂, y₃}, ∃ hXY : M₁.X ⫗ M₂.Y, ∃ hYX : M₁.Y ⫗ M₂.X,
      let M₀ := StandardRepresentation_3sum hXX hYY hXY hYX
      M.toMatroid = M₀.fst.toMatroid ∧ M₀.snd

variable {M : StandardRepresentation α}

-- API for access to individual assumptions and identities in the definition of 3-sum

lemma StandardRepresentation.Is3sumOf.interXX (hM : M.Is3sumOf M₁ M₂) :
    ∃ x₁ x₂ x₃ : α, M₁.X ∩ M₂.X = {x₁, x₂, x₃} := by
  obtain ⟨x₁, x₂, x₃, -, -, -, hXX, -⟩ := hM
  exact ⟨x₁, x₂, x₃, hXX⟩

lemma StandardRepresentation.Is3sumOf.interYY (hM : M.Is3sumOf M₁ M₂) :
    ∃ y₁ y₂ y₃ : α, M₁.Y ∩ M₂.Y = {y₁, y₂, y₃} := by
  obtain ⟨-, -, -, y₁, y₂, y₃, -, hYY, -⟩ := hM
  exact ⟨y₁, y₂, y₃, hYY⟩

/- Start of proof attempt -/
lemma round1_disjoXY (hM : M.Is3sumOf M₁ M₂) : M₁.X ⫗ M₂.Y := by
  rcases hM with ⟨x₁, x₂, x₃, y₁, y₂, y₃, hXX, hYY, hXY, hYX, h⟩
  exact hXY

theorem StandardRepresentation.Is3sumOf.disjoXY (hM : M.Is3sumOf M₁ M₂) :
    M₁.X ⫗ M₂.Y  := by

  exact round1_disjoXY hM
