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

/- Start of proof attempt -/
lemma round1_toUnion_toSum {α : Type} {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] 
    (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) : i.toUnion.toSum = i := by
  cases i with
  | inl x =>
    simp [Sum.toUnion, Subtype.toSum, HasSubset.Subset.elem]
    <;> aesop
  | inr y =>
    have h1 : (y : α) ∈ Y := y.property
    have h2 : (y : α) ∉ X := by
      intro h3
      have h4 : (y : α) ∈ X ∩ Y := ⟨h3, h1⟩
      have h6 : X ∩ Y = ∅ := by simpa [Set.disjoint_iff_inter_eq_empty] using hXY
      rw [h6] at h4
      aesop
    simp [Sum.toUnion, Subtype.toSum, HasSubset.Subset.elem, h2]
    <;> aesop

/-- Converting `X.Elem ⊕ Y.Elem` to `(X ∪ Y).Elem` and back to `X.Elem ⊕ Y.Elem` gives the original element, assuming that
`X` and `Y` are disjoint. -/
theorem toUnion_toSum {X Y : Set α} [∀ a, Decidable (a ∈ X)] [∀ a, Decidable (a ∈ Y)] (hXY : X ⫗ Y) (i : X.Elem ⊕ Y.Elem) :
    i.toUnion.toSum = i  := by

  exact round1_toUnion_toSum hXY i
