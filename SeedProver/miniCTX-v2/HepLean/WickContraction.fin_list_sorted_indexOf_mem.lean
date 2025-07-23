-- In HepLean/HepLean/PerturbationTheory/WickContraction/UncontractedList.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.ExtractEquiv
/-!

# List of uncontracted elements of a Wick contraction

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

/-!

## Some properties of lists of fin

-/

lemma fin_list_sorted_monotone_sorted {n m : ℕ} (l: List (Fin n)) (hl : l.Sorted (· ≤ ·))
    (f : Fin n → Fin m) (hf : StrictMono f) : ((List.map f l)).Sorted (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sorted_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · simp only [List.sorted_cons] at hl
      intro b hb
      have hl1 := hl.1 b hb
      exact (StrictMono.le_iff_le hf).mpr hl1
    · simp only [List.sorted_cons] at hl
      exact ih hl.2

lemma fin_list_sorted_succAboveEmb_sorted (l: List (Fin n)) (hl : l.Sorted (· ≤ ·))
    (i : Fin n.succ) : ((List.map i.succAboveEmb l)).Sorted (· ≤ ·) := by
  apply fin_list_sorted_monotone_sorted
  exact hl
  simp only [Fin.coe_succAboveEmb]
  exact Fin.strictMono_succAbove i

lemma fin_finset_sort_map_monotone {n m : ℕ} (a : Finset (Fin n)) (f : Fin n ↪ Fin m)
    (hf : StrictMono f) : (Finset.sort (· ≤ ·) a).map f =
    (Finset.sort (· ≤ ·) (a.map f)) := by
  have h1 : ((Finset.sort (· ≤ ·) a).map f).Sorted (· ≤ ·) := by
    apply fin_list_sorted_monotone_sorted
    exact Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) a
    exact hf
  have h2 : ((Finset.sort (· ≤ ·) a).map f).Nodup := by
    refine (List.nodup_map_iff_inj_on ?_).mpr ?_
    exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) a
    intro a ha b hb hf
    exact f.2 hf
  have h3 : ((Finset.sort (· ≤ ·) a).map f).toFinset = (a.map f) := by
    ext a
    simp
  rw [← h3]
  exact ((List.toFinset_sort (· ≤ ·) h2).mpr h1).symm

lemma fin_list_sorted_split :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : ℕ) →
    l = l.filter (fun x => x.1 < i) ++ l.filter (fun x => i ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.sorted_cons] at hl
    by_cases ha : a < i
    · conv_lhs => rw [fin_list_sorted_split l hl.2 i]
      rw [← List.cons_append]
      rw [List.filter_cons_of_pos, List.filter_cons_of_neg]
      simp only [decide_eq_true_eq, not_le, ha]
      simp [ha]
    · have hx : List.filter (fun x => decide (x.1 < i)) (a :: l) = [] := by
        simp only [ha, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
          List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append]
      rw [List.filter_cons_of_pos]
      simp only [List.cons.injEq, true_and]
      have hl' := fin_list_sorted_split l hl.2 i
      have hx : List.filter (fun x => decide (x.1 < i)) (l) = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append] at hl'
      conv_lhs => rw [hl']
      simp only [decide_eq_true_eq]
      omega

lemma fin_list_sorted_indexOf_filter_le_mem :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    (hl : i ∈ l) →
    List.indexOf i (List.filter (fun x => decide (↑i ≤ ↑x)) l) = 0
  | [], _, _, _ => by simp
  | a :: l, hl, i, hi => by
    simp only [List.sorted_cons] at hl
    by_cases ha : i ≤ a
    · simp only [ha, decide_true, List.filter_cons_of_pos]
      have ha : a = i := by
        simp only [List.mem_cons] at hi
        rcases hi with hi | hi
        · subst hi
          rfl
        · have hl' := hl.1 i hi
          exact Fin.le_antisymm hl' ha
      subst ha
      simp
    · simp only [not_le] at ha
      rw [List.filter_cons_of_neg (by simpa using ha)]
      rw [fin_list_sorted_indexOf_filter_le_mem l hl.2]
      simp only [List.mem_cons] at hi
      rcases hi with hi | hi
      · omega
      · exact hi

/- Start of proof attempt -/
lemma round1_fin_list_sorted_indexOf_mem :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    (hi : i ∈ l) →
    l.indexOf i = (l.filter (fun x => x.1 < i.1)).length := by
  intro l
  induction l with
  | nil =>
    intro hl i hi
    simp at hi <;> tauto
  | cons a t ih =>
    intro hl i hi
    have h1 : ∀ (x : Fin n), x ∈ t → a ≤ x := by
      simp only [List.sorted_cons] at hl
      tauto
    have h2 : t.Sorted (· ≤ ·) := by
      simp only [List.sorted_cons] at hl
      tauto
    by_cases h3 : i = a
    · -- Case 1: i = a
      have h41 : ∀ (x : Fin n), x ∈ t → ¬ (x.1 < a.1) := by
        intro x hx
        have h5 : a ≤ x := h1 x hx
        have h51 : a.1 ≤ x.1 := by exact_mod_cast h5
        linarith
      have h42 : ∀ (x : Fin n), x ∈ t → ¬ (decide (x.1 < a.1) = true) := by
        intro x hx
        have h411 : ¬ (x.1 < a.1) := h41 x hx
        intro h421
        have h422 : x.1 < a.1 := by simpa using h421
        contradiction
      have h42' : t.filter (fun x => x.1 < a.1) = [] := by
        apply List.filter_eq_nil.mpr
        intro x hx
        simpa using h42 x hx
      have h61 : ¬ (a.1 < a.1) := by linarith
      have h6 : (a :: t).filter (fun x => x.1 < a.1) = [] := by
        simp [List.filter, h61, h42']
        <;> aesop
      have h61' : ((a :: t).filter (fun x => x.1 < a.1)).length = 0 := by
        rw [h6]
        <;> simp
      have h62 : (a :: t).indexOf a = 0 := by simp
      have h63 : (a :: t).indexOf i = ((a :: t).filter (fun x => x.1 < i.1)).length := by
        have h64 : i = a := h3
        have h65 : (a :: t).indexOf i = (a :: t).indexOf a := by rw [h64]
        have h66 : ((a :: t).filter (fun x => x.1 < i.1)).length = ((a :: t).filter (fun x => x.1 < a.1)).length := by
          have h67 : i = a := h3
          simp [h67]
        have h67 : (a :: t).indexOf a = 0 := by simp
        have h68 : ((a :: t).filter (fun x => x.1 < a.1)).length = 0 := by simpa using h61'
        linarith
      simp [h3] at *
      <;> linarith
    · -- Case 2: i ≠ a
      have h3' : i ≠ a := by tauto
      have h7 : i ∈ t := by
        simp at hi
        tauto
      have h8 : a ≤ i := by
        exact h1 i h7
      have h9 : a < i := by
        by_contra h9
        have h91 : ¬ a < i := h9
        have h92 : a = i := by
          have h921 : a ≤ i := h8
          have h922 : ¬ a < i := h91
          have h923 : a.1 ≤ i.1 := by exact_mod_cast h921
          have h924 : ¬ a.1 < i.1 := by exact_mod_cast h922
          have h925 : a.1 = i.1 := by linarith
          exact Fin.eq_of_val_eq h925
        have h93 : a = i := h92
        have h94 : i = a := by tauto
        tauto
      have h91 : a.1 < i.1 := by exact_mod_cast h9
      have h12 : t.indexOf i = (t.filter (fun x => x.1 < i.1)).length := by
        exact ih h2 i h7
      have h13 : (a :: t).indexOf i = t.indexOf i + 1 := by
        have h131 : a ≠ i := by tauto
        simp [List.indexOf_cons, h131]
        <;> aesop
      have h14 : (a :: t).filter (fun x => x.1 < i.1) = a :: (t.filter (fun x => x.1 < i.1)) := by
        simp [List.filter, h91]
        <;> aesop
      have h15 : ((a :: t).filter (fun x => x.1 < i.1)).length = 1 + (t.filter (fun x => x.1 < i.1)).length := by
        rw [h14]
        simp [List.length]
        <;> ring
      linarith

theorem fin_list_sorted_indexOf_mem :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    (hi : i ∈ l) →
    l.indexOf i = (l.filter (fun x => x.1 < i.1)).length  := by

  exact round1_fin_list_sorted_indexOf_mem
