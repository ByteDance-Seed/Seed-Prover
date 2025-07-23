-- In mathlib/Mathlib/Algebra/Homology/Embedding/Boundary.lean

/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Basic
import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Boundary of an embedding of complex shapes

In the file `Mathlib.Algebra.Homology.Embedding.Basic`, given `p : ℤ`, we have defined
an embedding `embeddingUpIntGE p` of `ComplexShape.up ℕ` in `ComplexShape.up ℤ`
which sends `n : ℕ` to `p + n`. The (canonical) truncation (`≥ p`) of
`K : CochainComplex C ℤ` shall be defined as the extension to `ℤ`
(see `Mathlib.Algebra.Homology.Embedding.Extend`) of
a certain cochain complex indexed by `ℕ`:

`Q ⟶ K.X (p + 1) ⟶ K.X (p + 2) ⟶ K.X (p + 3) ⟶ ...`

where in degree `0`, the object `Q` identifies to the cokernel
of `K.X (p - 1) ⟶ K.X p` (this is `K.opcycles p`). In this case,
we see that the degree `0 : ℕ` needs a particular attention when
constructing the truncation.

In this file, more generally, for `e : Embedding c c'`, we define
a predicate `ι → Prop` named `e.BoundaryGE` which shall be relevant
when constructing the truncation `K.truncGE e` when `e.IsTruncGE`.
In the case of `embeddingUpIntGE p`, we show that `0 : ℕ` is the
only element in this lower boundary. Similarly, we define
`Embedding.BoundaryLE`.

-/

namespace ComplexShape

namespace Embedding

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')

/-- The lower boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `i' : ι'` not in the image of `e.f`
such that `c'.Rel i' (e.f j)`. -/
def BoundaryGE (j : ι) : Prop :=
  c'.Rel (c'.prev (e.f j)) (e.f j) ∧ ∀ i, ¬c'.Rel (e.f i) (e.f j)

lemma boundaryGE {i' : ι'} {j : ι} (hj : c'.Rel i' (e.f j)) (hi' : ∀ i, e.f i ≠ i') :
    e.BoundaryGE j := by
  constructor
  · simpa only [c'.prev_eq' hj] using hj
  · intro i hi
    apply hi' i
    rw [← c'.prev_eq' hj, c'.prev_eq' hi]

lemma not_boundaryGE_next [e.IsRelIff] {j k : ι} (hk : c.Rel j k) :
    ¬ e.BoundaryGE k := by
  dsimp [BoundaryGE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hk⟩

lemma not_boundaryGE_next' [e.IsRelIff] {j k : ι} (hj : ¬ e.BoundaryGE j) (hk : c.next j = k) :
    ¬ e.BoundaryGE k := by
  by_cases hjk : c.Rel j k
  · exact e.not_boundaryGE_next hjk
  · subst hk
    simpa only [c.next_eq_self j hjk] using hj

variable {e} in
lemma BoundaryGE.not_mem {j : ι} (hj : e.BoundaryGE j) {i' : ι'} (hi' : c'.Rel i' (e.f j))
    (a : ι) : e.f a ≠ i' := fun ha =>
  hj.2 a (by simpa only [ha] using hi')

lemma prev_f_of_not_boundaryGE [e.IsRelIff] {i j : ι} (hij : c.prev j = i)
    (hj : ¬ e.BoundaryGE j) :
    c'.prev (e.f j) = e.f i := by
  by_cases hij' : c.Rel i j
  · exact c'.prev_eq' (by simpa only [e.rel_iff] using hij')
  · obtain rfl : j = i := by
      simpa only [c.prev_eq_self j (by simpa only [hij] using hij')] using hij
    apply c'.prev_eq_self
    intro hj'
    simp only [BoundaryGE, not_and, not_forall, not_not] at hj
    obtain ⟨i, hi⟩ := hj hj'
    rw [e.rel_iff] at hi
    rw [c.prev_eq' hi] at hij
    exact hij' (by simpa only [hij] using hi)

variable {e} in
lemma BoundaryGE.false_of_isTruncLE {j : ι} (hj : e.BoundaryGE j) [e.IsTruncLE] : False := by
  obtain ⟨i, hi⟩ := e.mem_prev hj.1
  exact hj.2 i (by simpa only [hi] using hj.1)

/-- The upper boundary of an embedding `e : Embedding c c'`, as a predicate on `ι`.
It is satisfied by `j : ι` when there exists `k' : ι'` not in the image of `e.f`
such that `c'.Rel (e.f j) k'`. -/
def BoundaryLE (j : ι) : Prop :=
  c'.Rel (e.f j) (c'.next (e.f j)) ∧ ∀ k, ¬c'.Rel (e.f j) (e.f k)

lemma boundaryLE {k' : ι'} {j : ι} (hj : c'.Rel (e.f j) k') (hk' : ∀ i, e.f i ≠ k') :
    e.BoundaryLE j := by
  constructor
  · simpa only [c'.next_eq' hj] using hj
  · intro k hk
    apply hk' k
    rw [← c'.next_eq' hj, c'.next_eq' hk]

lemma not_boundaryLE_prev [e.IsRelIff] {i j : ι} (hi : c.Rel i j) :
    ¬ e.BoundaryLE i := by
  dsimp [BoundaryLE]
  simp only [not_and, not_forall, not_not]
  intro
  exact ⟨j, by simpa only [e.rel_iff] using hi⟩

lemma not_boundaryLE_prev' [e.IsRelIff] {i j : ι} (hj : ¬ e.BoundaryLE j) (hk : c.prev j = i) :
    ¬ e.BoundaryLE i := by
  by_cases hij : c.Rel i j
  · exact e.not_boundaryLE_prev hij
  · subst hk
    simpa only [c.prev_eq_self j hij] using hj

variable {e} in
lemma BoundaryLE.not_mem {j : ι} (hj : e.BoundaryLE j) {k' : ι'} (hk' : c'.Rel (e.f j) k')
    (a : ι) : e.f a ≠ k' := fun ha =>
  hj.2 a (by simpa only [ha] using hk')

lemma next_f_of_not_boundaryLE [e.IsRelIff] {j k : ι} (hjk : c.next j = k)
    (hj : ¬ e.BoundaryLE j) :
    c'.next (e.f j) = e.f k := by
  by_cases hjk' : c.Rel j k
  · exact c'.next_eq' (by simpa only [e.rel_iff] using hjk')
  · obtain rfl : j = k := by
      simpa only [c.next_eq_self j (by simpa only [hjk] using hjk')] using hjk
    apply c'.next_eq_self
    intro hj'
    simp only [BoundaryLE, not_and, not_forall, not_not] at hj
    obtain ⟨k, hk⟩ := hj hj'
    rw [e.rel_iff] at hk
    rw [c.next_eq' hk] at hjk
    exact hjk' (by simpa only [hjk] using hk)

lemma next_f [e.IsTruncGE] {j k : ι} (hjk : c.next j = k) : c'.next (e.f j) = e.f k := by
  by_cases hj : c'.Rel (e.f j) (c'.next (e.f j))
  · obtain ⟨k', hk'⟩ := e.mem_next hj
    rw [← hk', e.rel_iff] at hj
    rw [← hk', ← c.next_eq' hj, hjk]
  · rw [c'.next_eq_self _ hj, ← hjk, c.next_eq_self j]
    intro hj'
    apply hj
    rw [← e.rel_iff] at hj'
    simpa only [c'.next_eq' hj'] using hj'

lemma prev_f [e.IsTruncLE] {i j : ι} (hij : c.prev j = i) : c'.prev (e.f j) = e.f i :=
  e.op.next_f hij

variable {e} in
lemma BoundaryLE.false_of_isTruncGE {j : ι} (hj : e.BoundaryLE j) [e.IsTruncGE] : False := by
  obtain ⟨k, hk⟩ := e.mem_next hj.1
  exact hj.2 k (by simpa only [hk] using hj.1)

/- Start of proof attempt -/
lemma round1_h3 (ι' : Type*) (c' : ComplexShape ι') :
  ∀ (x : ι'), c'.symm.next x = c'.prev x := by
  intro x
  rfl

lemma round1_symm_rel_iff (ι' : Type*) (c' : ComplexShape ι') :
  ∀ (a b : ι'), c'.symm.Rel a b ↔ c'.Rel b a := by
  intro a b
  simp [ComplexShape.symm]

lemma round1_forward_direction (ι ι' : Type*) (c : ComplexShape ι) (c' : ComplexShape ι') (e : Embedding c c') (j : ι)
  (h3 : ∀ (x : ι'), c'.symm.next x = c'.prev x)
  (symm_rel_iff : ∀ (a b : ι'), c'.symm.Rel a b ↔ c'.Rel b a) :
  e.op.BoundaryLE j → e.BoundaryGE j := by
  intro h
  have h11 : c'.symm.Rel (e.op.f j) (c'.symm.next (e.op.f j)) := h.1
  have h12 : c'.symm.Rel (e.op.f j) (c'.prev (e.op.f j)) := by
    have h121 : c'.symm.next (e.op.f j) = c'.prev (e.op.f j) := h3 (e.op.f j)
    rw [h121] at h11
    exact h11
  have h13 : c'.symm.Rel (e.f j) (c'.prev (e.f j)) := by
    have h131 : e.op.f j = e.f j := by simp [Embedding.op_f]
    rw [h131] at h12
    exact h12
  have h14 : c'.Rel (c'.prev (e.f j)) (e.f j) := by
    have h141 := (symm_rel_iff (e.f j) (c'.prev (e.f j))).mp h13
    tauto
  have h2 : ∀ i, ¬c'.Rel (e.f i) (e.f j) := by
    intro i
    intro h21
    have h22 : c'.symm.Rel (e.f j) (e.f i) := by
      have h221 := (symm_rel_iff (e.f j) (e.f i)).mpr h21
      tauto
    have h23 : c'.symm.Rel (e.op.f j) (e.op.f i) := by
      have h231 : e.op.f j = e.f j := by simp [Embedding.op_f]
      have h232 : e.op.f i = e.f i := by simp [Embedding.op_f]
      rw [h231, h232]
      exact h22
    have h24 : ¬c'.symm.Rel (e.op.f j) (e.op.f i) := h.2 i
    contradiction
  exact ⟨h14, h2⟩

lemma round1_backward_direction (ι ι' : Type*) (c : ComplexShape ι) (c' : ComplexShape ι') (e : Embedding c c') (j : ι)
  (h3 : ∀ (x : ι'), c'.symm.next x = c'.prev x)
  (symm_rel_iff : ∀ (a b : ι'), c'.symm.Rel a b ↔ c'.Rel b a) :
  e.BoundaryGE j → e.op.BoundaryLE j := by
  intro h
  have h1 : c'.Rel (c'.prev (e.f j)) (e.f j) := h.1
  have h11 : c'.symm.Rel (e.f j) (c'.prev (e.f j)) := by
    have h111 := (symm_rel_iff (e.f j) (c'.prev (e.f j))).mpr h1
    tauto
  have h12 : c'.symm.Rel (e.op.f j) (c'.symm.next (e.op.f j)) := by
    have h13 : c'.symm.next (e.op.f j) = c'.prev (e.f j) := by
      have h131 : c'.symm.next (e.op.f j) = c'.prev (e.op.f j) := h3 (e.op.f j)
      have h132 : e.op.f j = e.f j := by simp [Embedding.op_f]
      rw [h131, h132]
      <;> rfl
    have h14 : c'.symm.Rel (e.op.f j) (c'.prev (e.f j)) := by
      have h141 : e.op.f j = e.f j := by simp [Embedding.op_f]
      rw [h141]
      exact h11
    rw [h13]
    exact h14
  have h2 : ∀ k, ¬c'.symm.Rel (e.op.f j) (e.op.f k) := by
    intro k
    intro h21
    have h22 : c'.symm.Rel (e.f j) (e.f k) := by
      have h221 : e.op.f j = e.f j := by simp [Embedding.op_f]
      have h222 : e.op.f k = e.f k := by simp [Embedding.op_f]
      rw [h221, h222] at h21
      exact h21
    have h23 : c'.Rel (e.f k) (e.f j) := by
      have h231 := (symm_rel_iff (e.f j) (e.f k)).mp h22
      tauto
    have h24 : ¬c'.Rel (e.f k) (e.f j) := h.2 k
    contradiction
  exact ⟨h12, h2⟩

theorem op_boundaryLE_iff {j : ι} : e.op.BoundaryLE j ↔ e.BoundaryGE j  := by

  have h3 : ∀ (x : ι'), c'.symm.next x = c'.prev x := by
    exact round1_h3 ι' c'
  have symm_rel_iff : ∀ (a b : ι'), c'.symm.Rel a b ↔ c'.Rel b a := by
    exact round1_symm_rel_iff ι' c'
  constructor
  · exact round1_forward_direction ι ι' c c' e j h3 symm_rel_iff
  · exact round1_backward_direction ι ι' c c' e j h3 symm_rel_iff
