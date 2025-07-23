-- In HepLean/HepLean/PerturbationTheory/FieldSpecification/TimeOrder.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.CrAnSection
import HepLean.PerturbationTheory.FieldSpecification.NormalOrder
/-!

# Time ordering of states

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-!

## Time ordering for states

-/

/-- The time ordering relation on states. We have that `timeOrderRel φ0 φ1` is true
  if and only if `φ1` has a time less-then or equal to `φ0`, or `φ1` is a negative
  asymptotic state, or `φ0` is a positive asymptotic state. -/
def timeOrderRel : 𝓕.FieldOp → 𝓕.FieldOp → Prop
  | FieldOp.outAsymp _, _ => True
  | FieldOp.position φ0, FieldOp.position φ1 => φ1.2 0 ≤ φ0.2 0
  | FieldOp.position _, FieldOp.inAsymp _ => True
  | FieldOp.position _, FieldOp.outAsymp _ => False
  | FieldOp.inAsymp _, FieldOp.outAsymp _ => False
  | FieldOp.inAsymp _, FieldOp.position _ => False
  | FieldOp.inAsymp _, FieldOp.inAsymp _ => True

/-- The relation `timeOrderRel` is decidable, but not computable so due to
  `Real.decidableLE`. -/
noncomputable instance : (φ φ' : 𝓕.FieldOp) → Decidable (timeOrderRel φ φ')
  | FieldOp.outAsymp _, _ => isTrue True.intro
  | FieldOp.position φ0, FieldOp.position φ1 => inferInstanceAs (Decidable (φ1.2 0 ≤ φ0.2 0))
  | FieldOp.position _, FieldOp.inAsymp _ => isTrue True.intro
  | FieldOp.position _, FieldOp.outAsymp _ => isFalse (fun a => a)
  | FieldOp.inAsymp _, FieldOp.outAsymp _ => isFalse (fun a => a)
  | FieldOp.inAsymp _, FieldOp.position _ => isFalse (fun a => a)
  | FieldOp.inAsymp _, FieldOp.inAsymp _ => isTrue True.intro

/-- Time ordering is total. -/
instance : IsTotal 𝓕.FieldOp 𝓕.timeOrderRel where
  total a b := by
    cases a <;> cases b <;>
      simp only [or_self, or_false, or_true, timeOrderRel, Fin.isValue, implies_true, imp_self,
        IsEmpty.forall_iff]
    exact LinearOrder.le_total _ _

/-- Time ordering is transitive. -/
instance : IsTrans 𝓕.FieldOp 𝓕.timeOrderRel where
  trans a b c := by
    cases a <;> cases b <;> cases c <;>
      simp only [timeOrderRel, Fin.isValue, implies_true, imp_self, IsEmpty.forall_iff]
    exact fun h1 h2 => Preorder.le_trans _ _ _ h2 h1

noncomputable section

open FieldStatistic
open HepLean.List

/-- Given a list `φ :: φs` of states, the (zero-based) position of the state which is
  of maximum time. For example
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `1`.
  This is defined for a list `φ :: φs` instead of `φs` to ensure that such a position exists.
-/
def maxTimeFieldPos (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) : ℕ :=
  insertionSortMinPos timeOrderRel φ φs

lemma maxTimeFieldPos_lt_length (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    maxTimeFieldPos φ φs < (φ :: φs).length := by
  simp [maxTimeFieldPos]

/-- Given a list `φ :: φs` of states, the left-most state of maximum time, if there are more.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `φ2(t = 5)`.
  It is the state at the position `maxTimeFieldPos φ φs`.
-/
def maxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) : 𝓕.FieldOp :=
  insertionSortMin timeOrderRel φ φs

/-- Given a list `φ :: φs` of states, the list with the left-most state of maximum
  time removed.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return
    `[φ1(t = 4), φ3(t = 3), φ4(t = 5)]`.
-/
def eraseMaxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) : List 𝓕.FieldOp :=
  insertionSortDropMinPos timeOrderRel φ φs

@[simp]
lemma eraseMaxTimeField_length (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    (eraseMaxTimeField φ φs).length = φs.length := by
  simp [eraseMaxTimeField, insertionSortDropMinPos, eraseIdx_length']

lemma maxTimeFieldPos_lt_eraseMaxTimeField_length_succ (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    maxTimeFieldPos φ φs < (eraseMaxTimeField φ φs).length.succ := by
  simp only [eraseMaxTimeField_length, Nat.succ_eq_add_one]
  exact maxTimeFieldPos_lt_length φ φs

/-- Given a list `φ :: φs` of states, the position of the left-most state of maximum
  time as an element of `Fin (eraseMaxTimeField φ φs).length.succ`.
  As an example:
  - for the list `[φ1(t = 4), φ2(t = 5), φ3(t = 3), φ4(t = 5)]` this would return `⟨1,...⟩`.
-/
def maxTimeFieldPosFin (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    Fin (eraseMaxTimeField φ φs).length.succ :=
  insertionSortMinPosFin timeOrderRel φ φs

lemma lt_maxTimeFieldPosFin_not_timeOrder (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin (eraseMaxTimeField φ φs).length)
    (hi : (maxTimeFieldPosFin φ φs).succAbove i < maxTimeFieldPosFin φ φs) :
    ¬ timeOrderRel ((eraseMaxTimeField φ φs)[i.val]) (maxTimeField φ φs) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt timeOrderRel φ φs i hi

lemma timeOrder_maxTimeField (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin (eraseMaxTimeField φ φs).length) :
    timeOrderRel (maxTimeField φ φs) ((eraseMaxTimeField φ φs)[i.val]) := by
  exact insertionSortMin_lt_mem_insertionSortDropMinPos timeOrderRel φ φs _

/-- The sign associated with putting a list of states into time order (with
  the state of greatest time to the left).
  We pick up a minus sign for every fermion paired crossed. -/
def timeOrderSign (φs : List 𝓕.FieldOp) : ℂ :=
  Wick.koszulSign 𝓕.fieldOpStatistic 𝓕.timeOrderRel φs

@[simp]
lemma timeOrderSign_nil : timeOrderSign (𝓕 := 𝓕) [] = 1 := by
  simp only [timeOrderSign]
  rfl

lemma timeOrderSign_pair_ordered {φ ψ : 𝓕.FieldOp} (h : timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 1 := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, mul_one, ite_eq_left_iff,
    ite_eq_right_iff, and_imp]
  exact fun h' => False.elim (h' h)

/- Start of proof attempt -/
lemma round1_timeOrderSign_pair_not_ordered {φ ψ : 𝓕.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) := by
  simp only [timeOrderSign, Wick.koszulSign, Wick.koszulSignInsert, h, if_false]
  simp [FieldStatistic.exchangeSign]
  cases h1 : 𝓕.fieldOpStatistic φ <;> cases h2 : 𝓕.fieldOpStatistic ψ <;> simp [h1, h2]
  <;> aesop

theorem timeOrderSign_pair_not_ordered {φ ψ : 𝓕.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    timeOrderSign [φ, ψ] = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ)  := by

  exact round1_timeOrderSign_pair_not_ordered h
