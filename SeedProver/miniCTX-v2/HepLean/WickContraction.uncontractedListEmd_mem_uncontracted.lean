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

@[simp]
lemma uncontractedList_getElem_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedIndexEquiv.symm k).val] = k := by
  simp [uncontractedIndexEquiv]

lemma uncontractedIndexEquiv_symm_eq_filter_length (k : c.uncontracted) :
    (c.uncontractedIndexEquiv.symm k).val =
    (List.filter (fun i => i < k.val) c.uncontractedList).length := by
  simp only [uncontractedIndexEquiv, List.get_eq_getElem, Equiv.coe_fn_symm_mk]
  rw [fin_list_sorted_indexOf_mem]
  · simp
  · exact uncontractedList_sorted c
  · rw [uncontractedList_mem_iff]
    exact k.2

lemma take_uncontractedIndexEquiv_symm (k : c.uncontracted) :
    c.uncontractedList.take (c.uncontractedIndexEquiv.symm k).val =
    c.uncontractedList.filter (fun i => i < k.val) := by
  have hl := fin_list_sorted_split c.uncontractedList (uncontractedList_sorted c) k.val
  conv_lhs =>
    rhs
    rw [hl]
  rw [uncontractedIndexEquiv_symm_eq_filter_length]
  simp
/-!

## Uncontracted List get

-/

/-- Given a Wick Contraction `φsΛ` of a list `φs` of `𝓕.FieldOp`. The list
  `φsΛ.uncontractedListGet` of `𝓕.FieldOp` is defined as the list `φs` with
  all contracted positions removed, leaving the uncontracted `𝓕.FieldOp`.

  The notation `[φsΛ]ᵘᶜ` is used for `φsΛ.uncontractedListGet`. -/
def uncontractedListGet {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) :
    List 𝓕.FieldOp := φsΛ.uncontractedList.map φs.get

@[inherit_doc uncontractedListGet]
scoped[WickContraction] notation "[" φsΛ "]ᵘᶜ" => uncontractedListGet φsΛ

@[simp]
lemma uncontractedListGet_empty {φs : List 𝓕.FieldOp} :
    (empty (n := φs.length)).uncontractedListGet = φs := by
  simp [uncontractedListGet]

/-!

## uncontractedFieldOpEquiv

-/

/-- The equivalence between the type `Option c.uncontracted` for `WickContraction φs.length` and
  `Option (Fin (c.uncontractedList.map φs.get).length)`, that is optional positions of
  `c.uncontractedList.map φs.get` induced by `uncontractedIndexEquiv`. -/
def uncontractedFieldOpEquiv (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    Option φsΛ.uncontracted ≃ Option (Fin [φsΛ]ᵘᶜ.length) :=
  Equiv.optionCongr (φsΛ.uncontractedIndexEquiv.symm.trans
    (finCongr (by simp [uncontractedListGet])))

@[simp]
lemma uncontractedFieldOpEquiv_none (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    (uncontractedFieldOpEquiv φs φsΛ).toFun none = none := by
  simp [uncontractedFieldOpEquiv]

lemma uncontractedFieldOpEquiv_list_sum [AddCommMonoid α] (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (f : Option (Fin [φsΛ]ᵘᶜ.length) → α) :
    ∑ (i : Option (Fin [φsΛ]ᵘᶜ.length)), f i =
    ∑ (i : Option φsΛ.uncontracted), f (φsΛ.uncontractedFieldOpEquiv φs i) := by
  rw [(φsΛ.uncontractedFieldOpEquiv φs).sum_comp]

/-!

## uncontractedListEmd

-/

/-- The embedding of `Fin [φsΛ]ᵘᶜ.length` into `Fin φs.length`. -/
def uncontractedListEmd {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length} :
    Fin [φsΛ]ᵘᶜ.length ↪ Fin φs.length := ((finCongr (by simp [uncontractedListGet])).trans
  φsΛ.uncontractedIndexEquiv).toEmbedding.trans
  (Function.Embedding.subtype fun x => x ∈ φsΛ.uncontracted)

lemma uncontractedListEmd_congr {φs : List 𝓕.FieldOp} {φsΛ φsΛ' : WickContraction φs.length}
    (h : φsΛ = φsΛ') : φsΛ.uncontractedListEmd =
    (finCongr (by simp [h])).toEmbedding.trans φsΛ'.uncontractedListEmd := by
  subst h
  rfl

lemma uncontractedListEmd_toFun_eq_get (φs : List 𝓕.FieldOp) (φsΛ : WickContraction φs.length) :
    (uncontractedListEmd (φsΛ := φsΛ)).toFun =
    φsΛ.uncontractedList.get ∘ (finCongr (by simp [uncontractedListGet])) := by
  rfl

lemma uncontractedListEmd_strictMono {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    {i j : Fin [φsΛ]ᵘᶜ.length} (h : i < j) : uncontractedListEmd i < uncontractedListEmd j := by
  simp only [uncontractedListEmd, uncontractedIndexEquiv, List.get_eq_getElem,
    Equiv.trans_toEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, finCongr_apply,
    Equiv.coe_fn_mk, Fin.coe_cast, Function.Embedding.coe_subtype]
  exact List.Sorted.get_strictMono φsΛ.uncontractedList_sorted_lt h

/- Start of proof attempt -/
lemma round1_h1 (φs : List 𝓕.FieldOp)
  (φsΛ : WickContraction φs.length)
  (i : Fin [φsΛ]ᵘᶜ.length):
  φsΛ.uncontractedList.get ((finCongr (by simp [uncontractedListGet])).toEmbedding i) ∈ φsΛ.uncontracted := by
  apply uncontractedList_get_mem_uncontracted

lemma round1_h2 (φs : List 𝓕.FieldOp)
  (φsΛ : WickContraction φs.length)
  (i : Fin [φsΛ]ᵘᶜ.length):
  (uncontractedListEmd (φsΛ := φsΛ)) i = φsΛ.uncontractedList.get ((finCongr (by simp [uncontractedListGet])).toEmbedding i) := by
  have h21 : (uncontractedListEmd (φsΛ := φsΛ)).toFun = φsΛ.uncontractedList.get ∘ (finCongr (by simp [uncontractedListGet])) := by
    exact uncontractedListEmd_toFun_eq_get φs φsΛ
  simp [h21]
  <;> aesop

theorem uncontractedListEmd_mem_uncontracted {φs : List 𝓕.FieldOp} {φsΛ : WickContraction φs.length}
    (i : Fin [φsΛ]ᵘᶜ.length) : uncontractedListEmd i ∈ φsΛ.uncontracted  := by

  have h1 : φsΛ.uncontractedList.get ((finCongr (by simp [uncontractedListGet])).toEmbedding i) ∈ φsΛ.uncontracted := by
    exact round1_h1 φs φsΛ i
  have h2 : (uncontractedListEmd (φsΛ := φsΛ)) i = φsΛ.uncontractedList.get ((finCongr (by simp [uncontractedListGet])).toEmbedding i) := by
    exact round1_h2 φs φsΛ i
  rw [h2]
  exact h1
