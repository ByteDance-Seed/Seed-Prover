-- In HepLean/HepLean/PerturbationTheory/WickContraction/Basic.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.Basic
/-!

# Wick contractions

-/
open FieldSpecification

variable {𝓕 : FieldSpecification}

/--
Given a natural number `n`, which will correspond to the number of fields needing
contracting, a Wick contraction
is a finite set of pairs of `Fin n` (numbers `0`, …, `n-1`), such that no
element of `Fin n` occurs in more then one pair. The pairs are the positions of fields we
'contract' together.
-/
def WickContraction (n : ℕ) : Type :=
  {f : Finset ((Finset (Fin n))) // (∀ a ∈ f, a.card = 2) ∧
    (∀ a ∈ f, ∀ b ∈ f, a = b ∨ Disjoint a b)}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List

remark contraction_notation := "Given a field specification `𝓕`, and a list `φs`
  of `𝓕.FieldOp`, a Wick contraction of `φs` will mean a Wick contraction in
  `WickContraction φs.length`. The notation `φsΛ` will be used for such contractions.
  The terminology that `φsΛ` contracts pairs within of `φs` will also be used, even though
  `φsΛ` is really contains positions of `φs`."

/-- Wick contractions are decidable. -/
instance : DecidableEq (WickContraction n) := Subtype.instDecidableEq

/-- The contraction consisting of no contracted pairs. -/
def empty : WickContraction n := ⟨∅, by simp, by simp⟩

lemma card_zero_iff_empty (c : WickContraction n) : c.1.card = 0 ↔ c = empty := by
  rw [Subtype.eq_iff]
  simp [empty]

lemma exists_pair_of_not_eq_empty (c : WickContraction n) (h : c ≠ empty) :
    ∃ i j, {i, j} ∈ c.1 := by
  by_contra hn
  simp only [not_exists] at hn
  have hc : c.1 = ∅ := by
    ext a
    simp only [Finset.not_mem_empty, iff_false]
    by_contra hn'
    have hc := c.2.1 a hn'
    rw [@Finset.card_eq_two] at hc
    obtain ⟨x, y, hx, rfl⟩ := hc
    exact hn x y hn'
  apply h
  apply Subtype.eq
  simp [empty, hc]

/-- The equivalence between `WickContraction n` and `WickContraction m`
  derived from a propositional equality of `n` and `m`. -/
def congr : {n m : ℕ} → (h : n = m) → WickContraction n ≃ WickContraction m
  | n, .(n), rfl => Equiv.refl _

@[simp]
lemma congr_refl : c.congr rfl = c := by
  rfl

@[simp]
lemma card_congr {n m : ℕ} (h : n = m) (c : WickContraction n) :
    (congr h c).1.card = c.1.card := by
  subst h
  simp

lemma congr_contractions {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).1 = Finset.map (Finset.mapEmbedding (finCongr h)).toEmbedding c.1 := by
  subst h
  simp only [congr_refl, Finset.le_eq_subset, finCongr_refl, Equiv.refl_toEmbedding]
  ext a
  apply Iff.intro
  · intro ha
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    use a
    simp only [ha, true_and]
    rw [Finset.mapEmbedding_apply]
    simp
  · intro ha
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding] at ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [Finset.mapEmbedding_apply] at hab
    simp only [Finset.map_refl] at hab
    subst hab
    exact hb

@[simp]
lemma congr_trans {n m o : ℕ} (h1 : n = m) (h2 : m = o) :
    (congr h1).trans (congr h2) = congr (h1.trans h2) := by
  subst h1 h2
  simp [congr]

@[simp]
lemma congr_trans_apply {n m o : ℕ} (h1 : n = m) (h2 : m = o) (c : WickContraction n) :
    (congr h2) ((congr h1) c) = congr (h1.trans h2) c := by
  subst h1 h2
  simp

lemma mem_congr_iff {n m : ℕ} (h : n = m) {c : WickContraction n } {a : Finset (Fin m)} :
    a ∈ (congr h c).1 ↔ Finset.map (finCongr h.symm).toEmbedding a ∈ c.1 := by
  subst h
  simp

/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
def congrLift {n m : ℕ} (h : n = m) {c : WickContraction n} (a : c.1) : (congr h c).1 :=
  ⟨a.1.map (finCongr h).toEmbedding, by
    subst h
    simp⟩

@[simp]
lemma congrLift_rfl {n : ℕ} {c : WickContraction n} :
    c.congrLift rfl = id := by
  funext a
  simp [congrLift]

lemma congrLift_injective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Injective (c.congrLift h) := by
  subst h
  simp only [congrLift_rfl]
  exact fun ⦃a₁ a₂⦄ a => a

lemma congrLift_surjective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Surjective (c.congrLift h) := by
  subst h
  simp only [congrLift_rfl]
  exact Function.surjective_id

lemma congrLift_bijective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Bijective (c.congrLift h) := by
  exact ⟨c.congrLift_injective h, c.congrLift_surjective h⟩

/-- Given a contracted pair in `c : WickContraction n` the contracted pair
  in `congr h c`. -/
def congrLiftInv {n m : ℕ} (h : n = m) {c : WickContraction n} (a : (congr h c).1) : c.1 :=
  ⟨a.1.map (finCongr h.symm).toEmbedding, by
    subst h
    simp⟩

lemma congrLiftInv_rfl {n : ℕ} {c : WickContraction n} :
    c.congrLiftInv rfl = id := by
  funext a
  simp [congrLiftInv]

lemma eq_filter_mem_self : c.1 = Finset.filter (fun x => x ∈ c.1) Finset.univ := by
  exact Eq.symm (Finset.filter_univ_mem c.1)

/-- For a contraction `c : WickContraction n` and `i : Fin n` the `j` such that
  `{i, j}` is a contracted pair in `c`. If such an `j` does not exist, this returns `none`. -/
def getDual? (i : Fin n) : Option (Fin n) := Fin.find (fun j => {i, j} ∈ c.1)

lemma getDual?_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (i : Fin m) :
    (congr h c).getDual? i = Option.map (finCongr h) (c.getDual? (finCongr h.symm i)) := by
  subst h
  simp

lemma getDual?_congr_get {n m : ℕ} (h : n = m) (c : WickContraction n) (i : Fin m)
    (hg : ((congr h c).getDual? i).isSome) :
    ((congr h c).getDual? i).get hg =
    (finCongr h ((c.getDual? (finCongr h.symm i)).get (by simpa [getDual?_congr] using hg))) := by
  simp only [getDual?_congr, finCongr_apply]
  exact Option.get_map

lemma getDual?_eq_some_iff_mem (i j : Fin n) :
    c.getDual? i = some j ↔ {i, j} ∈ c.1 := by
  simp only [getDual?]
  rw [Fin.find_eq_some_iff]
  apply Iff.intro
  · intro h
    exact h.1
  · intro h
    simp only [h, true_and]
    intro k hk
    have hc := c.2.2 _ h _ hk
    simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, true_or,
      not_true_eq_false, Finset.disjoint_singleton_right, not_or, false_and, or_false] at hc
    have hj : k ∈ ({i, j} : Finset (Fin n)) := by
      simp [hc]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · subst hj
      simp only [Finset.mem_singleton, Finset.insert_eq_of_mem] at hk
      have hc := c.2.1 _ hk
      simp at hc
    · subst hj
      simp

@[simp]
lemma getDual?_one_eq_none (c : WickContraction 1) (i : Fin 1) : c.getDual? i = none := by
  by_contra h
  have hn : (c.getDual? i).isSome := by
    rw [← Option.not_isSome_iff_eq_none] at h
    simpa [- Option.not_isSome, -Option.isNone_iff_eq_none] using h
  rw [@Option.isSome_iff_exists] at hn
  obtain ⟨a, hn⟩ := hn
  rw [getDual?_eq_some_iff_mem] at hn
  have hc := c.2.1 {i, a} hn
  fin_cases i
  fin_cases a
  simp at hc

@[simp]
lemma getDual?_get_self_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {(c.getDual? i).get h, i} ∈ c.1 := by
  rw [@Finset.pair_comm]
  rw [← getDual?_eq_some_iff_mem]
  simp

@[simp]
lemma self_getDual?_get_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {i, (c.getDual? i).get h} ∈ c.1 := by
  rw [← getDual?_eq_some_iff_mem]
  simp

lemma getDual?_eq_some_neq (i j : Fin n) (h : c.getDual? i = some j) :
    ¬ i = j := by
  rw [getDual?_eq_some_iff_mem] at h
  by_contra hn
  subst hn
  have hc := c.2.1 _ h
  simp at hc

@[simp]
lemma self_neq_getDual?_get (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ i = (c.getDual? i).get h := by
  by_contra hn
  have hx : {i, (c.getDual? i).get h} ∈ c.1 := by simp
  have hc := c.2.1 _ hx
  nth_rewrite 1 [hn] at hc
  simp at hc

@[simp]
lemma getDual?_get_self_neq (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? i).get h = i := by
  by_contra hn
  have hx : {i, (c.getDual? i).get h} ∈ c.1 := by simp
  have hc := c.2.1 _ hx
  nth_rewrite 1 [hn] at hc
  simp at hc

lemma getDual?_isSome_iff (i : Fin n) : (c.getDual? i).isSome ↔ ∃ (a : c.1), i ∈ a.1 := by
  apply Iff.intro
  · intro h
    simp only [getDual?] at h
    rw [Fin.isSome_find_iff] at h
    obtain ⟨a, ha⟩ := h
    use ⟨{i, a}, ha⟩
    simp
  · intro h
    obtain ⟨a, ha⟩ := h
    have ha := c.2.1 a a.2
    rw [@Finset.card_eq_two] at ha
    obtain ⟨x, y, hx, hy⟩ := ha
    rw [hy] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    match ha with
    | Or.inl ha =>
      subst ha
      simp only [getDual?]
      rw [Fin.isSome_find_iff]
      use y
      rw [← hy]
      exact a.2
    | Or.inr ha =>
      subst ha
      simp only [getDual?]
      rw [Fin.isSome_find_iff]
      use x
      rw [Finset.pair_comm]
      rw [← hy]
      exact a.2

lemma getDual?_isSome_of_mem (a : c.1) (i : a.1) : (c.getDual? i).isSome := by
  rw [getDual?_isSome_iff]
  use ⟨a.1, a.2⟩
  simp

@[simp]
lemma getDual?_getDual?_get_get (i : Fin n) (h : (c.getDual? i).isSome) :
    c.getDual? ((c.getDual? i).get h) = some i := by
  rw [getDual?_eq_some_iff_mem]
  simp

lemma getDual?_getDual?_get_isSome (i : Fin n) (h : (c.getDual? i).isSome) :
    (c.getDual? ((c.getDual? i).get h)).isSome := by
  simp

lemma getDual?_getDual?_get_not_none (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? ((c.getDual? i).get h)) = none := by
  simp

/-!

## Extracting parts from a contraction.

-/

/-- The smallest of the two positions in a contracted pair given a Wick contraction. -/
def fstFieldOfContract (c : WickContraction n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).head (by
    have hx : (Finset.sort (fun x1 x2 => x1 ≤ x2) a.1).length = a.1.card := by
      exact Finset.length_sort fun x1 x2 => x1 ≤ x2
    by_contra hn
    rw [hn, c.2.1 a.1 a.2] at hx
    simp at hx)

@[simp]
lemma fstFieldOfContract_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (a : c.1) :
    (congr h c).fstFieldOfContract (c.congrLift h a) = (finCongr h) (c.fstFieldOfContract a) := by
  subst h
  simp [congr]

/-- The largest of the two positions in a contracted pair given a Wick contraction. -/
def sndFieldOfContract (c : WickContraction n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).tail.head (by
    have hx : (Finset.sort (fun x1 x2 => x1 ≤ x2) a.1).length = a.1.card := by
      exact Finset.length_sort fun x1 x2 => x1 ≤ x2
    by_contra hn
    have hn := congrArg List.length hn
    simp only [List.length_tail, Finset.length_sort, List.length_nil] at hn
    rw [c.2.1 a.1 a.2] at hn
    omega)

@[simp]
lemma sndFieldOfContract_congr {n m : ℕ} (h : n = m) (c : WickContraction n) (a : c.1) :
    (congr h c).sndFieldOfContract (c.congrLift h a) = (finCongr h) (c.sndFieldOfContract a) := by
  subst h
  simp [congr]

lemma finset_eq_fstFieldOfContract_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} := by
  have h1 := c.2.1 a.1 a.2
  rw [Finset.card_eq_two] at h1
  obtain ⟨x, y, hxy, ha⟩ := h1
  rw [ha]
  by_cases hxyle : x ≤ y
  · have ha : a.1.sort (· ≤ ·) = [x, y] := by
      rw [ha]
      trans Finset.sort (· ≤ ·) (Finset.cons x {y} (by simp [hxy]))
      · congr
        simp
      rw [Finset.sort_cons]
      simp only [Finset.sort_singleton]
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst hb
      omega
    simp [fstFieldOfContract, ha, sndFieldOfContract]
  · have ha : a.1.sort (· ≤ ·) = [y, x] := by
      rw [ha]
      trans Finset.sort (· ≤ ·) (Finset.cons y {x} (by simp only [Finset.mem_singleton]; omega))
      · congr
        simp only [Finset.cons_eq_insert]
        rw [@Finset.pair_comm]
      rw [Finset.sort_cons]
      simp only [Finset.sort_singleton]
      intro b hb
      simp only [Finset.mem_singleton] at hb
      subst hb
      omega
    simp only [fstFieldOfContract, ha, List.head_cons, sndFieldOfContract, List.tail_cons]
    rw [Finset.pair_comm]

lemma fstFieldOfContract_neq_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ≠ c.sndFieldOfContract a := by
  have h1 := c.2.1 a.1 a.2
  have h2 := c.finset_eq_fstFieldOfContract_sndFieldOfContract a
  by_contra hn
  rw [h2, hn] at h1
  simp at h1

lemma fstFieldOfContract_le_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ≤ c.sndFieldOfContract a := by
  simp only [fstFieldOfContract, sndFieldOfContract, List.head_tail]
  have h1 (n : ℕ) (l : List (Fin n)) (h : l ≠ []) (hl : l.Sorted (· ≤ ·)) :
      ∀ a ∈ l, l.head h ≤ a := by
    induction l with
    | nil => simp at h
    | cons i l ih =>
      simp only [List.sorted_cons] at hl
      simpa using hl.1
  apply h1
  · exact Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) _
  · exact List.getElem_mem _

lemma fstFieldOfContract_lt_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a < c.sndFieldOfContract a :=
  lt_of_le_of_ne (c.fstFieldOfContract_le_sndFieldOfContract a)
    (c.fstFieldOfContract_neq_sndFieldOfContract a)

@[simp]
lemma fstFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.fstFieldOfContract a ∈ a.1 := by
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract]
  simp

lemma fstFieldOfContract_getDual?_isSome (c : WickContraction n) (a : c.1) :
    (c.getDual? (c.fstFieldOfContract a)).isSome := by
  rw [getDual?_isSome_iff]
  use a
  simp

@[simp]
lemma fstFieldOfContract_getDual? (c : WickContraction n) (a : c.1) :
    c.getDual? (c.fstFieldOfContract a) = some (c.sndFieldOfContract a) := by
  rw [getDual?_eq_some_iff_mem]
  erw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2

/- Start of proof attempt -/
lemma round1_sndFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.sndFieldOfContract a ∈ a.1 := by
  have h : a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} := by
    exact c.finset_eq_fstFieldOfContract_sndFieldOfContract a
  rw [h]
  simp

theorem sndFieldOfContract_mem (c : WickContraction n) (a : c.1) :
    c.sndFieldOfContract a ∈ a.1  := by

  exact round1_sndFieldOfContract_mem c a
