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

lemma involutionCons_ext {n : ℕ} {f1 f2 : (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}}
    (h1 : f1.1 = f2.1) (h2 : f1.2 = Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2) : f1 = f2 := by
  cases f1
  cases f2
  simp only at h1 h2
  subst h1
  rename_i fst snd snd_1
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  obtain ⟨val, property⟩ := fst
  obtain ⟨val_1, property_1⟩ := snd
  obtain ⟨val_2, property_2⟩ := snd_1
  simp_all only
  rfl

/-- Given an involution of `Fin n`, the optional choice of an element in `Fin n` which
  maps to itself is equivalent to the optional choice of an element in
  `Fin (Finset.univ.filter fun i => f.1 i = i).card`. -/
def involutionAddEquiv {n : ℕ} (f : {f : Fin n → Fin n // Function.Involutive f}) :
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} ≃
    Option (Fin (Finset.univ.filter fun i => f.1 i = i).card) := by
  let e1 : {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}
        ≃ Option {i : Fin n // f.1 i = i} :=
    { toFun := fun i => match i with
        | ⟨some i, h⟩ => some ⟨i, by simpa using h⟩
        | ⟨none, h⟩ => none
      invFun := fun i => match i with
        | some ⟨i, h⟩ => ⟨some i, by simpa using h⟩
        | none => ⟨none, by simp⟩
      left_inv := by
        intro a
        cases a
        aesop
      right_inv := by
        intro a
        cases a
        rfl
        simp_all only [Subtype.coe_eta] }
  let s : Finset (Fin n) := Finset.univ.filter fun i => f.1 i = i
  let e2' : { i : Fin n // f.1 i = i} ≃ {i // i ∈ s} := by
    apply Equiv.subtypeEquivProp
    simp [s]
  let e2 : {i // i ∈ s} ≃ Fin (Finset.card s) := by
    refine (Finset.orderIsoOfFin _ ?_).symm.toEquiv
    simp [s]
  refine e1.trans (Equiv.optionCongr (e2'.trans (e2)))

lemma involutionAddEquiv_none_image_zero {n : ℕ} :
    {f : {f : Fin n.succ → Fin n.succ // Function.Involutive f}}
    → involutionAddEquiv (involutionCons n f).1 (involutionCons n f).2 = none
    → f.1 ⟨0, Nat.zero_lt_succ n⟩ = ⟨0, Nat.zero_lt_succ n⟩ := by
  intro f h
  simp only [Nat.succ_eq_add_one, involutionCons, Equiv.coe_fn_mk, involutionAddEquiv,
    Option.isSome_some, Option.get_some, Option.isSome_none, Equiv.trans_apply,
    Equiv.optionCongr_apply, Equiv.coe_trans, RelIso.coe_fn_toEquiv, Option.map_eq_none'] at h
  simp_all only [List.length_cons, Fin.zero_eta]
  obtain ⟨val, property⟩ := f
  simp_all only [List.length_cons]
  split at h
  next i i_1 h_1 heq =>
    split at heq
    next h_2 => simp_all only [reduceCtorEq]
    next h_2 => simp_all only [reduceCtorEq]
  next i h_1 heq =>
    split at heq
    next h_2 => simp_all only
    next h_2 => simp_all only [Subtype.mk.injEq, reduceCtorEq]

/- Start of proof attempt -/
lemma round1_involutionAddEquiv_cast {n : ℕ} {f1 f2 : {f : Fin n → Fin n // Function.Involutive f}}
    (hf : f1 = f2) :
    involutionAddEquiv f1 = (Equiv.subtypeEquivRight (by rw [hf]; simp)).trans
      ((involutionAddEquiv f2).trans (Equiv.optionCongr (finCongr (by rw [hf])))) := by
  subst hf
  simp [Equiv.optionCongr, finCongr, Equiv.trans_assoc]
  <;>
  aesop

theorem involutionAddEquiv_cast {n : ℕ} {f1 f2 : {f : Fin n → Fin n // Function.Involutive f}}
    (hf : f1 = f2) :
    involutionAddEquiv f1 = (Equiv.subtypeEquivRight (by rw [hf]; simp)).trans
      ((involutionAddEquiv f2).trans (Equiv.optionCongr (finCongr (by rw [hf]))))  := by

  exact round1_involutionAddEquiv_cast hf
