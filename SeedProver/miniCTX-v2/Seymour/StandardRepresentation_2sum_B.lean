-- In Seymour/Seymour/Matroid/Operations/MatrixSums/Sum2.lean

import Seymour.Matroid.Operations.MatrixSums.BinaryMatroids

/-!
This file contains everything about 2-sum of binary matroids — the old version (in terms of explicit matrices).
-/

variable {α : Type}

/-- `Matrix`-level 2-sum for matroids defined by their standard representation matrices; does not check legitimacy. -/
abbrev Matrix_2sumComposition {β : Type} [Semiring β] {X₁ Y₁ X₂ Y₂ : Set α}
    (A₁ : Matrix X₁ Y₁ β) (x : Y₁ → β) (A₂ : Matrix X₂ Y₂ β) (y : X₂ → β) :
    Matrix (X₁ ⊕ X₂) (Y₁ ⊕ Y₂) β :=
  Matrix.fromBlocks A₁ 0 (fun i j => y i * x j) A₂

variable [DecidableEq α] {M₁ M₂ : StandardRepresentation α}

/-- `StandardRepresentation`-level 2-sum of two matroids.
The second part checks legitimacy: the ground sets of `M₁` and `M₂` are disjoint except for the element `a ∈ M₁.X ∩ M₂.Y`,
and the bottom-most row of `M₁` and the left-most column of `M₂` are each nonzero vectors. -/
def StandardRepresentation_2sum {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    StandardRepresentation α × Prop :=
  let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
  let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
  let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rw [ha]; rfl)⟩ -- the bottom row of `B₁`
  let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rw [ha]; rfl)⟩) -- the left column of `B₂`
  ⟨
    ⟨
      (M₁.X \ {a}) ∪ M₂.X,
      M₁.Y ∪ (M₂.Y \ {a}),
      inferInstance,
      inferInstance,
      by
        rw [Set.disjoint_union_right, Set.disjoint_union_left, Set.disjoint_union_left]
        exact ⟨⟨M₁.hXY.disjoint_sdiff_left, hXY⟩, ⟨disjoint_of_singleton_inter_both_wo ha, M₂.hXY.disjoint_sdiff_right⟩⟩,
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion
    ⟩,
    (M₁.X ⫗ M₂.X ∧ M₁.Y ⫗ M₂.Y) ∧ (x ≠ 0 ∧ y ≠ 0)
  ⟩

/-- Binary matroid `M` is a result of 2-summing `M₁` and `M₂` in some way. -/
def StandardRepresentation.Is2sumOf (M : StandardRepresentation α) (M₁ M₂ : StandardRepresentation α) : Prop :=
  ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a}, ∃ hXY : M₂.X ⫗ M₁.Y,
    let M₀ := StandardRepresentation_2sum ha hXY
    M.toMatroid = M₀.fst.toMatroid ∧ M₀.snd

variable {M : StandardRepresentation α}

lemma StandardRepresentation.Is2sumOf.disjoXX (hM : M.Is2sumOf M₁ M₂) :
    M₁.X ⫗ M₂.X := by
  obtain ⟨a, -, -, -, ⟨hXX, -⟩, -⟩ := hM
  exact hXX

lemma StandardRepresentation.Is2sumOf.disjoYY (hM : M.Is2sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.Y := by
  obtain ⟨a, -, -, -, ⟨-, hYY⟩, -⟩ := hM
  exact hYY

lemma StandardRepresentation.Is2sumOf.interXY (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, M₁.X ∩ M₂.Y = {a} := by
  obtain ⟨a, ha, -⟩ := hM
  exact ⟨a, ha⟩

lemma StandardRepresentation.Is2sumOf.disjoYX (hM : M.Is2sumOf M₁ M₂) :
    M₁.Y ⫗ M₂.X := by
  obtain ⟨a, -, hXY, -⟩ := hM
  exact hXY.symm

lemma StandardRepresentation.Is2sumOf.indep (hM : M.Is2sumOf M₁ M₂) :
    ∃ a : α, ∃ ha : M₁.X ∩ M₂.Y = {a},
      let A₁ : Matrix (M₁.X \ {a}).Elem M₁.Y.Elem Z2 := M₁.B ∘ Set.diff_subset.elem -- the top submatrix of `B₁`
      let A₂ : Matrix M₂.X.Elem (M₂.Y \ {a}).Elem Z2 := (M₂.B · ∘ Set.diff_subset.elem) -- the right submatrix of `B₂`
      let x : M₁.Y.Elem → Z2 := M₁.B ⟨a, Set.mem_of_mem_inter_left (by rewrite [ha]; rfl)⟩ -- the bottom row of `B₁`
      let y : M₂.X.Elem → Z2 := (M₂.B · ⟨a, Set.mem_of_mem_inter_right (by rewrite [ha]; rfl)⟩) -- the left column of `B₂`
      (Matrix_2sumComposition A₁ x A₂ y).toMatrixUnionUnion.IndepCols =
      M.toMatroid.Indep := by
  obtain ⟨a, ha, _, hMM, -⟩ := hM
  use a, ha
  rewrite [hMM]
  rfl

lemma Matrix_2sumComposition_isTotallyUnimodular {X₁ Y₁ X₂ Y₂ : Set α} {A₁ : Matrix X₁ Y₁ ℚ} {A₂ : Matrix X₂ Y₂ ℚ}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) (x : Y₁ → ℚ) (y : X₂ → ℚ) :
    (Matrix_2sumComposition A₁ x A₂ y).IsTotallyUnimodular := by
  sorry

/- Start of proof attempt -/
lemma round1_h1 (a : α)
  (ha : M₁.X ∩ M₂.Y = {a})
  (hXY : M₂.X ⫗ M₁.Y):
  a ∈ M₁.X ∩ M₂.Y := by
  have h2 : a ∈ ({a} : Set α) := by simp
  rw [ha] at *
  tauto

theorem StandardRepresentation_2sum_B {a : α} (ha : M₁.X ∩ M₂.Y = {a}) (hXY : M₂.X ⫗ M₁.Y) :
    ∃ haX₁ : a ∈ M₁.X, ∃ haY₂ : a ∈ M₂.Y,
      (StandardRepresentation_2sum ha hXY).fst.B =
      (Matrix_2sumComposition
        (M₁.B ∘ Set.diff_subset.elem)
        (M₁.B ⟨a, haX₁⟩)
        (M₂.B · ∘ Set.diff_subset.elem)
        (M₂.B · ⟨a, haY₂⟩)
      ).toMatrixUnionUnion  := by

  have h1 : a ∈ M₁.X ∩ M₂.Y := by
    exact round1_h1 a ha hXY
  have haX₁ : a ∈ M₁.X := h1.1
  have haY₂ : a ∈ M₂.Y := h1.2
  refine' ⟨haX₁, haY₂, _⟩
  simp [StandardRepresentation_2sum]
  <;> aesop
  <;> simp_all
  <;> aesop
