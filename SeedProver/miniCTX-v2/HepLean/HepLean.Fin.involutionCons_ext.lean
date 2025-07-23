-- In HepLean/HepLean/Mathematics/Fin/Involutions.lean

/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorial.DoubleFactorial
/-!
# Fin involutions

Some properties of involutions of `Fin n`.

These involutions are used in e.g. proving results about Wick contractions.

-/
namespace HepLean.Fin

open Nat

/-- There is an equivalence between involutions of `Fin n.succ` and involutions of
  `Fin n` and an optional valid choice of an element in `Fin n` (which is where `0`
    in `Fin n.succ` will be sent). -/
def involutionCons (n : ℕ) : {f : Fin n.succ → Fin n.succ // Function.Involutive f } ≃
    (f : {f : Fin n → Fin n // Function.Involutive f}) × {i : Option (Fin n) //
      ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} where
  toFun f := ⟨⟨
    fun i =>
    if h : f.1 i.succ = 0 then i
    else Fin.pred (f.1 i.succ) h, by
    intro i
    by_cases h : f.1 i.succ = 0
    · simp [h]
    · simp only [succ_eq_add_one, h, ↓reduceDIte, Fin.succ_pred]
      simp only [f.2 i.succ, Fin.pred_succ, dite_eq_ite, ite_eq_right_iff]
      intro h
      exact False.elim (Fin.succ_ne_zero i h)⟩,
    ⟨if h : f.1 0 = 0 then none else Fin.pred (f.1 0) h, by
    by_cases h0 : f.1 0 = 0
    · simp [h0]
    · simp only [succ_eq_add_one, h0, ↓reduceDIte, Option.isSome_some, Option.get_some,
      Fin.succ_pred, dite_eq_left_iff, Fin.pred_inj, forall_const]
      refine fun h => False.elim (h (f.2 0))⟩⟩
  invFun f := ⟨
      if h : (f.2.1).isSome then
        Fin.cons (f.2.1.get h).succ (Function.update (Fin.succ ∘ f.1.1) (f.2.1.get h) 0)
      else
        Fin.cons 0 (Fin.succ ∘ f.1.1), by
    by_cases hs : (f.2.1).isSome
    · simp only [Nat.succ_eq_add_one, hs, ↓reduceDIte, Fin.coe_eq_castSucc]
      let a := f.2.1.get hs
      change Function.Involutive (Fin.cons a.succ (Function.update (Fin.succ ∘ ↑f.fst) a 0))
      intro i
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
      · subst hi
        rw [Fin.cons_zero, Fin.cons_succ]
        simp
      · subst hj
        rw [Fin.cons_succ]
        by_cases hja : j = a
        · subst hja
          simp
        · rw [Function.update_apply]
          rw [if_neg hja]
          simp only [Function.comp_apply, Fin.cons_succ]
          have hf2 := f.2.2 hs
          change f.1.1 a = a at hf2
          have hjf1 : f.1.1 j ≠ a := by
            by_contra hn
            have haj : j = f.1.1 a := by
              rw [← hn]
              rw [f.1.2]
            rw [hf2] at haj
            exact hja haj
          rw [Function.update_apply, if_neg hjf1]
          simp only [Function.comp_apply, Fin.succ_inj]
          rw [f.1.2]
    · simp only [succ_eq_add_one, hs, Bool.false_eq_true, ↓reduceDIte]
      intro i
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
      · subst hi
        simp
      · subst hj
        simp only [Fin.cons_succ, Function.comp_apply, Fin.succ_inj]
        rw [f.1.2]⟩
  left_inv f := by
    match f with
    | ⟨f, hf⟩ =>
    simp only [succ_eq_add_one, Option.isSome_dite', Option.get_dite', Fin.succ_pred,
      Fin.cons_update, dite_eq_ite, ite_not, Subtype.mk.injEq]
    ext i
    by_cases h0 : f 0 = 0
    · simp only [h0, ↓reduceIte]
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
      · subst hi
        simp [h0]
      · subst hj
        simp only [Fin.cons_succ, Function.comp_apply, Fin.val_succ]
        by_cases hj : f j.succ =0
        · rw [← h0] at hj
          have hn := Function.Involutive.injective hf hj
          exact False.elim (Fin.succ_ne_zero j hn)
        · simp only [hj, ↓reduceDIte, Fin.coe_pred]
          rw [Fin.ext_iff] at hj
          simp only [succ_eq_add_one, Fin.val_zero] at hj
          omega
    · rw [if_neg h0]
      by_cases hf' : i = f 0
      · subst hf'
        simp only [Function.update_self, Fin.val_zero]
        rw [hf]
        simp
      · rw [Function.update_apply, if_neg hf']
        rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
        · subst hi
          simp
        · subst hj
          simp only [Fin.cons_succ, Function.comp_apply, Fin.val_succ]
          by_cases hj : f j.succ =0
          · rw [← hj] at hf'
            rw [hf] at hf'
            simp only [not_true_eq_false] at hf'
          · simp only [hj, ↓reduceDIte, Fin.coe_pred]
            rw [Fin.ext_iff] at hj
            simp only [succ_eq_add_one, Fin.val_zero] at hj
            omega
  right_inv f := by
    match f with
    | ⟨⟨f, hf⟩, ⟨f0, hf0⟩⟩ =>
    ext i
    · simp only [succ_eq_add_one, Fin.cons_update]
      by_cases hs : f0.isSome
      · simp only [hs, ↓reduceDIte]
        by_cases hi : i = f0.get hs
        · simp only [Function.update_apply, hi, ↓reduceIte, ↓reduceDIte]
          exact Eq.symm (Fin.val_eq_of_eq (hf0 hs))
        · simp only [ne_eq, Fin.succ_inj, hi, not_false_eq_true, Function.update_of_ne,
          Fin.cons_succ, Function.comp_apply, Fin.pred_succ, dite_eq_ite]
          split
          · rename_i h
            exact False.elim (Fin.succ_ne_zero (f i) h)
          · rfl
      · simp only [hs, Bool.false_eq_true, ↓reduceDIte, Fin.cons_succ, Function.comp_apply,
        Fin.pred_succ, dite_eq_ite]
        split
        · rename_i h
          exact False.elim (Fin.succ_ne_zero (f i) h)
        · rfl
    · simp only [Nat.succ_eq_add_one, Option.mem_def,
      Option.dite_none_left_eq_some, Option.some.injEq]
      by_cases hs : f0.isSome
      · simp only [hs, ↓reduceDIte]
        simp only [Fin.cons_zero, Fin.pred_succ, exists_prop]
        have hx : ¬ (f0.get hs).succ = 0 := (Fin.succ_ne_zero (f0.get hs))
        simp only [hx, not_false_eq_true, true_and]
        refine Iff.intro (fun hi => ?_) (fun hi => ?_)
        · rw [← hi]
          exact
            Option.eq_some_of_isSome
              (Eq.mpr_prop (Eq.refl (f0.isSome = true))
                (of_eq_true (Eq.trans (congrArg (fun x => x = true) hs) (eq_self true))))
        · subst hi
          exact rfl
      · simp only [hs, Bool.false_eq_true, ↓reduceDIte, Fin.cons_zero, not_true_eq_false,
        IsEmpty.exists_iff, false_iff]
        simp only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at hs
        subst hs
        exact ne_of_beq_false rfl

/- Start of proof attempt -/
lemma round1_h3 (n : ℕ)
  (f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)})
  (h1 : f1.1 = f2.1)
  (h2 : f1.2 = Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2):
  (f1.2 : Option (Fin n)) = (f2.2 : Option (Fin n)) := by
  have h31 : (f1.2 : Option (Fin n)) = ((Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2 : {i : Option (Fin n) // ∀ (h : i.isSome), f1.1.1 (Option.get i h) = Option.get i h}) : Option (Fin n)) := by
    rw [h2]
    <;> rfl
  have h32 : ((Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2 : {i : Option (Fin n) // ∀ (h : i.isSome), f1.1.1 (Option.get i h) = Option.get i h}) : Option (Fin n)) = (f2.2 : Option (Fin n)) := by simp
  rw [h31, h32]

lemma round1_h5 (n : ℕ)
  (f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)})
  (h1 : f1.1 = f2.1)
  (h3 : (f1.2 : Option (Fin n)) = (f2.2 : Option (Fin n))):
  ((involutionCons n).invFun f1).1 = ((involutionCons n).invFun f2).1 := by
  simp [h1, h3]
  <;> aesop

lemma round1_h6 (n : ℕ)
  (f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)})
  (h5 : ((involutionCons n).invFun f1).1 = ((involutionCons n).invFun f2).1):
  (involutionCons n).invFun f1 = (involutionCons n).invFun f2 := by
  apply Subtype.ext
  exact h5

lemma round1_h_main (n : ℕ)
  (f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)})
  (h1 : f1.1 = f2.1)
  (h2 : f1.2 = Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2)
  (h3 : (f1.2 : Option (Fin n)) = (f2.2 : Option (Fin n)))
  (h5 : ((involutionCons n).invFun f1).1 = ((involutionCons n).invFun f2).1)
  (h6 : (involutionCons n).invFun f1 = (involutionCons n).invFun f2):
  f1 = f2 := by
  have h7 : (involutionCons n).toFun ((involutionCons n).invFun f1) = (involutionCons n).toFun ((involutionCons n).invFun f2) := by
    rw [h6]
  have h8 : (involutionCons n).toFun ((involutionCons n).invFun f1) = f1 := (involutionCons n).right_inv f1
  have h9 : (involutionCons n).toFun ((involutionCons n).invFun f2) = f2 := (involutionCons n).right_inv f2
  rw [h8, h9] at h7
  exact h7

theorem involutionCons_ext {n : ℕ} {f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}}
    (h1 : f1.1 = f2.1) (h2 : f1.2 = Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2) : f1 = f2  := by

  have h3 : (f1.2 : Option (Fin n)) = (f2.2 : Option (Fin n)) := by
    exact round1_h3 n f1 f2 h1 h2
  have h5 : ((involutionCons n).invFun f1).1 = ((involutionCons n).invFun f2).1 := by
    exact round1_h5 n f1 f2 h1 h3
  have h6 : (involutionCons n).invFun f1 = (involutionCons n).invFun f2 := by
    exact round1_h6 n f1 f2 h5
  have h_main : f1 = f2 := by
    exact round1_h_main n f1 f2 h1 h2 h3 h5 h6
  exact h_main
