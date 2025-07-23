-- In HepLean/HepLean/PerturbationTheory/FieldSpecification/CrAnSection.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.CrAnFieldOp
/-!

# Creation and annihilation sections

In the module
`HepLean.PerturbationTheory.FieldSpecification.Basic`
we defined states for a field specification, and in the module
`HepLean.PerturbationTheory.FieldStatistics.CrAnFieldOp`
we defined a refinement of states called `CrAnFieldOp` which distinquishes between the
creation and annihilation components of states.
There exists, in particular, a map from `CrAnFieldOp` to `FieldOp` called `crAnFieldOpToFieldOp`.

Given a list of `FieldOp`, `φs`, in this module we define a section of `φs` to be a list of
`CrAnFieldOp`, `ψs`, such that under the map `crAnFieldOpToFieldOp`, `ψs` is mapped to `φs`.
That is to say, the states underlying `ψs` are the states in `φs`.
We denote these sections as `CrAnSection φs`.

Looking forward the main consequence of this definition is the lemma
`FieldSpecification.FieldOpFreeAlgebra.ofFieldOpListF_sum`.

In this module we define various properties of `CrAnSection`.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-- The sections in `𝓕.CrAnFieldOp` over a list `φs : List 𝓕.FieldOp`.
  In terms of physics, given some fields `φ₁...φₙ`, the different ways one can associate
  each field as a `creation` or an `annilation` operator. E.g. the number of terms
  `φ₁⁰φ₂¹...φₙ⁰` `φ₁¹φ₂¹...φₙ⁰` etc. If some fields are exclusively creation or annihilation
  operators at this point (e.g. asymptotic states) this is accounted for. -/
def CrAnSection (φs : List 𝓕.FieldOp) : Type :=
  {ψs : List 𝓕.CrAnFieldOp // ψs.map 𝓕.crAnFieldOpToFieldOp = φs}
  -- Π i, 𝓕.fieldOpToCreateAnnihilateType (φs.get i)

namespace CrAnSection
open FieldStatistic
variable {𝓕 : FieldSpecification} {φs : List 𝓕.FieldOp}

@[simp]
lemma length_eq (ψs : CrAnSection φs) : ψs.1.length = φs.length := by
  simpa using congrArg List.length ψs.2

/-- The tail of a section for `φs`. -/
def tail : {φs : List 𝓕.FieldOp} → (ψs : CrAnSection φs) → CrAnSection φs.tail
  | [], ⟨[], h⟩ => ⟨[], h⟩
  | φ :: φs, ⟨[], h⟩ => False.elim (by simp at h)
  | φ :: φs, ⟨ψ :: ψs, h⟩ => ⟨ψs, by rw [List.map_cons, List.cons.injEq] at h; exact h.2⟩

lemma head_state_eq {φ : 𝓕.FieldOp} : (ψs : CrAnSection (φ :: φs)) →
    (ψs.1.head (by simp [← List.length_pos_iff_ne_nil])).1 = φ
  | ⟨[], h⟩ => False.elim (by simp at h)
  | ⟨ψ :: ψs, h⟩ => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact h.1

lemma statistics_eq_state_statistics (ψs : CrAnSection φs) :
    (𝓕 |>ₛ ψs.1) = 𝓕 |>ₛ φs := by
  erw [FieldStatistic.ofList_eq_prod, FieldStatistic.ofList_eq_prod, crAnStatistics]
  rw [← List.map_comp_map, Function.comp_apply, ψs.2]

lemma take_statistics_eq_take_state_statistics (ψs : CrAnSection φs) n :
    (𝓕 |>ₛ (ψs.1.take n)) = 𝓕 |>ₛ (φs.take n) := by
  erw [FieldStatistic.ofList_eq_prod, FieldStatistic.ofList_eq_prod, crAnStatistics]
  simp only [instCommGroup, List.map_take]
  rw [← List.map_comp_map, Function.comp_apply, ψs.2]

/-- The head of a section for `φ :: φs` as an element in `𝓕.fieldOpToCreateAnnihilateType φ`. -/
def head : {φ : 𝓕.FieldOp} → (ψs : CrAnSection (φ :: φs)) →
    𝓕.fieldOpToCrAnType φ
  | φ, ⟨[], h⟩ => False.elim (by simp at h)
  | φ, ⟨ψ :: ψs, h⟩ => 𝓕.fieldOpToCreateAnnihilateTypeCongr (by
    simpa using head_state_eq ⟨ψ :: ψs, h⟩) ψ.2

lemma eq_head_cons_tail {φ : 𝓕.FieldOp} {ψs : CrAnSection (φ :: φs)} :
    ψs.1 = ⟨φ, head ψs⟩ :: ψs.tail.1 := by
  match ψs with
  | ⟨[], h⟩ => exact False.elim (by simp at h)
  | ⟨ψ :: ψs, h⟩ =>
    have h2 := head_state_eq ⟨ψ :: ψs, h⟩
    simp only [List.head_cons] at h2
    subst h2
    rfl

/-- The creation of a section from for `φ : φs` from a section for `φs` and a
  element of `𝓕.fieldOpToCreateAnnihilateType φ`. -/
def cons {φ : 𝓕.FieldOp} (ψ : 𝓕.fieldOpToCrAnType φ) (ψs : CrAnSection φs) :
    CrAnSection (φ :: φs) := ⟨⟨φ, ψ⟩ :: ψs.1, by
  simp [List.map_cons, ψs.2]⟩

/-- For the empty list of states there is only one `CrAnSection`. Corresponding to the
  empty list of `CrAnFieldOp`. -/
def nilEquiv : CrAnSection (𝓕 := 𝓕) [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], rfl⟩
  left_inv ψs := Subtype.ext <| by
    have h2 := ψs.2
    simp only [List.map_eq_nil_iff] at h2
    simp [h2]
  right_inv _ := by
    simp

/-- The creation and annihilation sections for a singleton list is given by
  a choice of `𝓕.fieldOpToCreateAnnihilateType φ`. If `φ` is a asymptotic state
  there is no choice here, else there are two choices. -/
def singletonEquiv {φ : 𝓕.FieldOp} : CrAnSection [φ] ≃
    𝓕.fieldOpToCrAnType φ where
  toFun ψs := ψs.head
  invFun ψ := ⟨[⟨φ, ψ⟩], by simp⟩
  left_inv ψs := by
    apply Subtype.ext
    simp only
    have h1 := eq_head_cons_tail (ψs := ψs)
    rw [h1]
    have h2 := ψs.tail.2
    simp only [List.tail_cons, List.map_eq_nil_iff] at h2
    simp [h2]
  right_inv ψ := by
    simp only [head]
    rfl

/-- An equivalence separating the head of a creation and annihilation section
  from the tail. -/
def consEquiv {φ : 𝓕.FieldOp} {φs : List 𝓕.FieldOp} : CrAnSection (φ :: φs) ≃
    𝓕.fieldOpToCrAnType φ × CrAnSection φs where
  toFun ψs := ⟨ψs.head, ψs.tail⟩
  invFun ψψs :=
    match ψψs with
    | (ψ, ψs) => cons ψ ψs
  left_inv ψs := by
    apply Subtype.ext
    exact Eq.symm eq_head_cons_tail
  right_inv ψψs := by
    match ψψs with
    | (ψ, ψs) => rfl

/-- The instance of a finite type on `CrAnSection`s defined recursively through
  `consEquiv`. -/
instance fintype : (φs : List 𝓕.FieldOp) → Fintype (CrAnSection φs)
  | [] => Fintype.ofEquiv _ nilEquiv.symm
  | _ :: φs =>
    haveI : Fintype (CrAnSection φs) := fintype φs
    Fintype.ofEquiv _ consEquiv.symm

@[simp]
lemma card_nil_eq : Fintype.card (CrAnSection (𝓕 := 𝓕) []) = 1 := by
  rw [Fintype.ofEquiv_card nilEquiv.symm]
  simp

lemma card_cons_eq {φ : 𝓕.FieldOp} {φs : List 𝓕.FieldOp} :
    Fintype.card (CrAnSection (φ :: φs)) = Fintype.card (𝓕.fieldOpToCrAnType φ) *
    Fintype.card (CrAnSection φs) := by
  rw [Fintype.ofEquiv_card consEquiv.symm]
  simp

lemma card_eq_mul : {φs : List 𝓕.FieldOp} → Fintype.card (CrAnSection φs) =
    2 ^ (List.countP 𝓕.statesIsPosition φs)
  | [] => by
    simp
  | FieldOp.position _ :: φs => by
      simp only [statesIsPosition, List.countP_cons_of_pos]
      rw [card_cons_eq]
      rw [card_eq_mul]
      simp only [fieldOpToCrAnType, CreateAnnihilate.CreateAnnihilate_card_eq_two]
      ring
  | FieldOp.inAsymp x_ :: φs => by
      simp only [statesIsPosition, Bool.false_eq_true, not_false_eq_true, List.countP_cons_of_neg]
      rw [card_cons_eq]
      rw [card_eq_mul]
      simp [fieldOpToCrAnType]
  | FieldOp.outAsymp _ :: φs => by
      simp only [statesIsPosition, Bool.false_eq_true, not_false_eq_true, List.countP_cons_of_neg]
      rw [card_cons_eq]
      rw [card_eq_mul]
      simp [fieldOpToCrAnType]

lemma card_perm_eq {φs φs' : List 𝓕.FieldOp} (h : φs.Perm φs') :
    Fintype.card (CrAnSection φs) = Fintype.card (CrAnSection φs') := by
  rw [card_eq_mul, card_eq_mul]
  congr 1
  exact List.Perm.countP_congr h fun x => congrFun rfl

@[simp]
lemma sum_nil (f : CrAnSection (𝓕 := 𝓕) [] → M) [AddCommMonoid M] :
    ∑ (s : CrAnSection []), f s = f ⟨[], rfl⟩ := by
  rw [← nilEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  rfl

lemma sum_cons (f : CrAnSection (φ :: φs) → M) [AddCommMonoid M] :
    ∑ (s : CrAnSection (φ :: φs)), f s = ∑ (a : 𝓕.fieldOpToCrAnType φ),
    ∑ (s : CrAnSection φs), f (cons a s) := by
  rw [← consEquiv.symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_over_length {s : CrAnSection φs} (f : Fin s.1.length → M)
    [AddCommMonoid M] : ∑ (n : Fin s.1.length), f n =
    ∑ (n : Fin φs.length), f (Fin.cast (length_eq s).symm n) := by
  rw [← (finCongr (length_eq s)).sum_comp]
  rfl

/-- The equivalence between `CrAnSection φs` and
  `CrAnSection φs'` induced by an equality `φs = φs'`. -/
def congr : {φs φs' : List 𝓕.FieldOp} → (h : φs = φs') →
    CrAnSection φs ≃ CrAnSection φs'
  | _, _, rfl => Equiv.refl _

@[simp]
lemma congr_fst {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (ψs : CrAnSection φs) :
    (congr h ψs).1 = ψs.1 := by
  cases h
  rfl

@[simp]
lemma congr_symm {φs φs' : List 𝓕.FieldOp} (h : φs = φs') :
    (congr h).symm = congr h.symm := by
  cases h
  rfl

@[simp]
lemma congr_trans_apply {φs φs' φs'' : List 𝓕.FieldOp} (h1 : φs = φs') (h2 : φs' = φs'')
    (ψs : CrAnSection φs) :
    (congr h2 (congr h1 ψs)) = congr (by rw [h1, h2]) ψs := by
  subst h1 h2
  rfl

/-- Returns the first `n` elements of a section and its underlying list. -/
def take (n : ℕ) (ψs : CrAnSection φs) : CrAnSection (φs.take n) :=
  ⟨ψs.1.take n, by simp [ψs.2]⟩

@[simp]
lemma take_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (n : ℕ)
    (ψs : CrAnSection φs) :
    (take n (congr h ψs)) = congr (by rw [h]) (take n ψs) := by
  subst h
  rfl

/-- Removes the first `n` elements of a section and its underlying list. -/
def drop (n : ℕ) (ψs : CrAnSection φs) : CrAnSection (φs.drop n) :=
  ⟨ψs.1.drop n, by simp [ψs.2]⟩

/- Start of proof attempt -/
lemma round1_drop_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (n : ℕ)
    (ψs : CrAnSection φs) :
    (drop n (congr h ψs)) = congr (by rw [h]) (drop n ψs) := by
  subst h
  rfl

theorem drop_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') (n : ℕ)
    (ψs : CrAnSection φs) :
    (drop n (congr h ψs)) = congr (by rw [h]) (drop n ψs)  := by

  exact round1_drop_congr h n ψs
