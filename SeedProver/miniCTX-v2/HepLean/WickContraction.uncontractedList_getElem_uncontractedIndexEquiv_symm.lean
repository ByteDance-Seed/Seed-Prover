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

lemma fin_list_sorted_indexOf_mem :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    (hi : i ∈ l) →
    l.indexOf i = (l.filter (fun x => x.1 < i.1)).length := by
  intro l hl i hi
  conv_lhs => rw [fin_list_sorted_split l hl i]
  rw [List.indexOf_append_of_not_mem]
  erw [fin_list_sorted_indexOf_filter_le_mem l hl i hi]
  · simp
  · simp

lemma orderedInsert_of_fin_list_sorted :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    List.orderedInsert (· ≤ ·) i l = l.filter (fun x => x.1 < i.1) ++
    i :: l.filter (fun x => i.1 ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.sorted_cons] at hl
    by_cases ha : i ≤ a
    · simp only [List.orderedInsert, ha, ↓reduceIte, Fin.val_fin_lt, decide_eq_true_eq, not_lt,
      List.filter_cons_of_neg, Fin.val_fin_le, decide_true, List.filter_cons_of_pos]
      have h1 : List.filter (fun x => decide (↑x < ↑i)) l = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro a ha
        have ha' := hl.1 a ha
        omega
      have hl : l = List.filter (fun x => decide (i ≤ x)) l := by
        conv_lhs => rw [fin_list_sorted_split l hl.2 i]
        simp [h1]
      simp [← hl, h1]
    · simp only [List.orderedInsert, ha, ↓reduceIte, Fin.val_fin_lt, Fin.val_fin_le, decide_false,
      Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      rw [List.filter_cons_of_pos]
      rw [orderedInsert_of_fin_list_sorted l hl.2 i]
      simp only [Fin.val_fin_lt, Fin.val_fin_le, List.cons_append]
      simp only [decide_eq_true_eq]
      omega

lemma orderedInsert_eq_insertIdx_of_fin_list_sorted (l : List (Fin n)) (hl : l.Sorted (· ≤ ·))
    (i : Fin n) :
    List.orderedInsert (· ≤ ·) i l = l.insertIdx (l.filter (fun x => x.1 < i.1)).length i := by
  let n : Fin l.length.succ := ⟨(List.filter (fun x => decide (x < i)) l).length, by
    have h1 := l.length_filter_le (fun x => x.1 < i.1)
    simp only [Fin.val_fin_lt] at h1
    omega⟩
  simp only [Fin.val_fin_lt]
  conv_rhs => rw [insertIdx_eq_take_drop _ _ n]
  rw [orderedInsert_of_fin_list_sorted]
  congr
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]
  exact hl

/-!

## Uncontracted List

-/

/-- Given a Wick contraction `c`, the ordered list of elements of `Fin n` which are not contracted,
  i.e. do not appear anywhere in `c.1`. -/
def uncontractedList : List (Fin n) := List.filter (fun x => x ∈ c.uncontracted) (List.finRange n)

lemma uncontractedList_mem_iff (i : Fin n) :
    i ∈ c.uncontractedList ↔ i ∈ c.uncontracted := by
  simp [uncontractedList]

@[simp]
lemma uncontractedList_empty : (empty (n := n)).uncontractedList = List.finRange n := by
  simp [uncontractedList]

lemma nil_zero_uncontractedList : (empty (n := 0)).uncontractedList = [] := by
  simp [empty, uncontractedList]

lemma congr_uncontractedList {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).uncontractedList = List.map (finCongr h) c.uncontractedList := by
  subst h
  simp [congr]

lemma uncontractedList_get_mem_uncontracted (i : Fin c.uncontractedList.length) :
    c.uncontractedList.get i ∈ c.uncontracted := by
  rw [← uncontractedList_mem_iff]
  simp

lemma uncontractedList_sorted : List.Sorted (· ≤ ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Sorted.filter
  rw [← List.ofFn_id]
  exact Monotone.ofFn_sorted fun ⦃a b⦄ a => a

lemma uncontractedList_sorted_lt : List.Sorted (· < ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Sorted.filter
  rw [← List.ofFn_id]
  exact List.sorted_lt_ofFn_iff.mpr fun ⦃a b⦄ a => a

lemma uncontractedList_nodup : c.uncontractedList.Nodup := by
  rw [uncontractedList]
  refine List.Nodup.filter (fun x => decide (x ∈ c.uncontracted)) ?_
  exact List.nodup_finRange n

lemma uncontractedList_toFinset (c : WickContraction n) :
    c.uncontractedList.toFinset = c.uncontracted := by
  simp [uncontractedList]

lemma uncontractedList_eq_sort (c : WickContraction n) :
    c.uncontractedList = c.uncontracted.sort (· ≤ ·) := by
  symm
  rw [← uncontractedList_toFinset]
  refine (List.toFinset_sort (α := Fin n) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_nodup c
  · exact uncontractedList_sorted c

lemma uncontractedList_length_eq_card (c : WickContraction n) :
    c.uncontractedList.length = c.uncontracted.card := by
  rw [uncontractedList_eq_sort]
  exact Finset.length_sort fun x1 x2 => x1 ≤ x2

lemma filter_uncontractedList (c : WickContraction n) (p : Fin n → Prop) [DecidablePred p] :
    (c.uncontractedList.filter p) = (c.uncontracted.filter p).sort (· ≤ ·) := by
  have h1 : (c.uncontractedList.filter p).Sorted (· ≤ ·) := by
    apply List.Sorted.filter
    exact uncontractedList_sorted c
  have h2 : (c.uncontractedList.filter p).Nodup := by
    refine List.Nodup.filter _ ?_
    exact uncontractedList_nodup c
  have h3 : (c.uncontractedList.filter p).toFinset = (c.uncontracted.filter p) := by
    ext a
    simp only [List.toFinset_filter, decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset,
      and_congr_left_iff]
    rw [uncontractedList_mem_iff]
    simp
  have hx := (List.toFinset_sort (· ≤ ·) h2).mpr h1
  rw [← hx, h3]

/-!

## uncontractedIndexEquiv

-/

/-- The equivalence between the positions of `c.uncontractedList` i.e. elements of
  `Fin (c.uncontractedList).length` and the finite set `c.uncontracted` considered as a finite type.
-/
def uncontractedIndexEquiv (c : WickContraction n) :
    Fin (c.uncontractedList).length ≃ c.uncontracted where
  toFun i := ⟨c.uncontractedList.get i, c.uncontractedList_get_mem_uncontracted i⟩
  invFun i := ⟨List.indexOf i.1 c.uncontractedList,
    List.indexOf_lt_length_iff.mpr ((c.uncontractedList_mem_iff i.1).mpr i.2)⟩
  left_inv i := by
    ext
    exact List.get_indexOf (uncontractedList_nodup c) _
  right_inv i := by
    ext
    simp

/- Start of proof attempt -/
lemma round1_h1 (c : WickContraction n) (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedIndexEquiv.symm k).val] = k.1 := by
  have h1 : k.1 ∈ c.uncontractedList := by
    rw [uncontractedList_mem_iff]
    exact k.2
  have h2 : c.uncontractedList.Nodup := uncontractedList_nodup c
  simp [uncontractedIndexEquiv, Equiv.symm_apply_apply] at *
  <;>
  aesop <;>
  (try simp_all) <;>
  (try aesop) <;>
  (try simp_all [List.get_indexOf]) <;>
  (try aesop)

theorem uncontractedList_getElem_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedIndexEquiv.symm k).val] = k  := by

  exact round1_h1 c k
