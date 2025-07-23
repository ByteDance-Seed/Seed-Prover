-- In Seymour/Seymour/Basic.lean

import Seymour.ForMathlib.MatrixTU

/-!
This file provides notation used in the project and conversions between set-theoretical and type-theoretical definitions.
-/

/-- The finite field on 2 elements; write `Z2` for "value" type but `Fin 2` for "indexing" type. -/
abbrev Z2 : Type := ZMod 2

/-- The finite field on 3 elements; write `Z3` for "value" type but `Fin 3` for "indexing" type. -/
abbrev Z3 : Type := ZMod 3

/-- Roughly speaking `a ᕃ A` is `A ∪ {a}`. -/
infixr:66 " ᕃ " => Insert.insert

/-- Writing `X ⫗ Y` is slightly more general than writing `X ∩ Y = ∅`. -/
infix:61 " ⫗ " => Disjoint

/-- The left-to-right direction of `↔`. -/
postfix:max ".→" => Iff.mp

/-- The right-to-left direction of `↔`. -/
postfix:max ".←" => Iff.mpr

section utils

lemma Fin2_eq_1_of_ne_0 {a : Fin 2} (ha : a ≠ 0) : a = 1 := by
  omega

lemma Fin3_eq_2_of_ne_0_1 {a : Fin 3} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a = 2 := by
  omega

variable {α : Type}

/-- Given `X ⊆ Y` cast an element of `X` as an element of `Y`. -/
def HasSubset.Subset.elem {X Y : Set α} (hXY : X ⊆ Y) (x : X.Elem) : Y.Elem :=
  ⟨x.val, hXY x.property⟩

lemma HasSubset.Subset.elem_injective {X Y : Set α} (hXY : X ⊆ Y) : hXY.elem.Injective := by
  intro x y hxy
  ext
  simpa [HasSubset.Subset.elem] using hxy

/-- Convert `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem`. -/
def Subtype.toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) : X.Elem ⊕ Y.Elem :=
  if hiX : i.val ∈ X then Sum.inl ⟨i, hiX⟩ else
  if hiY : i.val ∈ Y then Sum.inr ⟨i, hiY⟩ else
  (i.property.elim hiX hiY).elim

/-- Convert `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem`. -/
def Sum.toUnion {X Y : Set α} (i : X.Elem ⊕ Y.Elem) : (X ∪ Y).Elem :=
  i.casesOn Set.subset_union_left.elem Set.subset_union_right.elem

/-- Converting `(X ∪ Y).Elem` to `X.Elem ⊕ Y.Elem` and back to `(X ∪ Y).Elem` gives the original element. -/
lemma toSum_toUnion {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (i : (X ∪ Y).Elem) :
    i.toSum.toUnion = i := by
  if hiX : i.val ∈ X then
    simp_all [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem]
  else if hiY : i.val ∈ Y then
    simp_all [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem]
  else
    exfalso
    exact i.property.elim hiX hiY

/-- Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
`X` and `Y` are disjoint. -/
lemma toUnion_toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i := by
  rw [Set.disjoint_right] at hXY
  cases i <;> simp [Subtype.toSum, Sum.toUnion, HasSubset.Subset.elem, hXY]

variable {T₁ T₂ S₁ S₂ : Set α} {β : Type}
  [∀ a, Decidable (a ∈ T₁)]
  [∀ a, Decidable (a ∈ T₂)]
  [∀ a, Decidable (a ∈ S₁)]
  [∀ a, Decidable (a ∈ S₂)]

/-- Convert a block matrix to a matrix over set unions. -/
def Matrix.toMatrixUnionUnion (C : Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β) :
    Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β :=
  ((C ∘ Subtype.toSum) · ∘ Subtype.toSum)

/-- Convert a matrix over set unions to a block matrix. -/
def Matrix.toMatrixSumSum (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    Matrix (T₁.Elem ⊕ T₂.Elem) (S₁.Elem ⊕ S₂.Elem) β :=
  ((C ∘ Sum.toUnion) · ∘ Sum.toUnion)

/-- Converting a block matrix to a matrix over set unions and back to a block matrix gives the original matrix, assuming that
both said unions are disjoint. -/
lemma toMatrixUnionUnion_toMatrixSumSum (hT : T₁ ⫗ T₂) (hS : S₁ ⫗ S₂) (C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β) :
    C.toMatrixUnionUnion.toMatrixSumSum = C := by
  ext
  simp_all [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toUnion_toSum]

/-- Converting a matrix over set unions to a block matrix and back to a matrix over set unions gives the original matrix. -/
lemma toMatrixSumSum_toMatrixUnionUnion (C : Matrix (T₁ ∪ T₂).Elem (S₁ ∪ S₂).Elem β) :
    C.toMatrixSumSum.toMatrixUnionUnion = C := by
  ext
  simp_all [Matrix.toMatrixUnionUnion, Matrix.toMatrixSumSum, toSum_toUnion]

/-- A totally unimodular block matrix stays totally unimodular after converting to a matrix over set unions. -/
lemma Matrix.IsTotallyUnimodular.toMatrixUnionUnion [CommRing β] {C : Matrix (T₁ ⊕ T₂) (S₁ ⊕ S₂) β}
    (hC : C.IsTotallyUnimodular) :
    C.toMatrixUnionUnion.IsTotallyUnimodular := by
  rw [Matrix.isTotallyUnimodular_iff] at hC ⊢
  intros
  apply hC

end utils

section TU_tautologies

/- Start of proof attempt -/
lemma round1_h3 (h1 : ∀ (x : Z2), x = 0 ∨ x = 1) : ∀ (x : Z2), x = 0 ∨ x = 1 → x ∈ Set.range SignType.cast := by
  intro x h
  cases h with
  | inl h0 =>
    -- Case x = 0
    rw [h0]
    refine' ⟨0, by simp⟩
  | inr h1 =>
    -- Case x = 1
    rw [h1]
    refine' ⟨1, by simp⟩

lemma round1_h4 (h1 : ∀ (x : Z2), x = 0 ∨ x = 1) (h3 : ∀ (x : Z2), x = 0 ∨ x = 1 → x ∈ Set.range SignType.cast) :
  ∀ (x : Z2), x ∈ Set.range SignType.cast := by
  intro x
  have h11 : x = 0 ∨ x = 1 := h1 x
  exact h3 x h11

theorem Matrix.overZ2_isTotallyUnimodular {X Y : Type} (A : Matrix X Y Z2) : A.IsTotallyUnimodular  := by

  have h1 : ∀ (x : Z2), x = 0 ∨ x = 1 := by
    intro x
    fin_cases x <;> simp
  have h3 : ∀ (x : Z2), x = 0 ∨ x = 1 → x ∈ Set.range SignType.cast := by
    exact round1_h3 h1
  have h4 : ∀ (x : Z2), x ∈ Set.range SignType.cast := by
    exact round1_h4 h1 h3
  intro n r c _ _
  exact h4 ((A.submatrix r c).det)
