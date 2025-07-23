-- In mathlib/Mathlib/Data/Set/Pairwise/Lattice.lean

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic

/-!
# Relations holding pairwise

In this file we prove many facts about `Pairwise` and the set lattice.
-/

open Function Set Order

variable {α ι ι' : Type*} {κ : Sort*} {r : α → α → Prop}
section Pairwise

variable {f : ι → α} {s : Set α}

namespace Set

theorem pairwise_iUnion {f : κ → Set α} (h : Directed (· ⊆ ·) f) :
    (⋃ n, f n).Pairwise r ↔ ∀ n, (f n).Pairwise r := by
  constructor
  · intro H n
    exact Pairwise.mono (subset_iUnion _ _) H
  · intro H i hi j hj hij
    rcases mem_iUnion.1 hi with ⟨m, hm⟩
    rcases mem_iUnion.1 hj with ⟨n, hn⟩
    rcases h m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij

theorem pairwise_sUnion {r : α → α → Prop} {s : Set (Set α)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).Pairwise r ↔ ∀ a ∈ s, Set.Pairwise a r := by
  rw [sUnion_eq_iUnion, pairwise_iUnion h.directed_val, SetCoe.forall]

end Set

end Pairwise

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s : Set ι} {f : ι → α}

theorem pairwiseDisjoint_iUnion {g : ι' → Set ι} (h : Directed (· ⊆ ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ ∀ ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_iUnion h

theorem pairwiseDisjoint_sUnion {s : Set (Set ι)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).PairwiseDisjoint f ↔ ∀ ⦃a⦄, a ∈ s → Set.PairwiseDisjoint a f :=
  pairwise_sUnion h

end PartialOrderBot

section CompleteLattice

variable [CompleteLattice α] {s : Set ι} {t : Set ι'}

/-- Bind operation for `Set.PairwiseDisjoint`. If you want to only consider finsets of indices, you
can use `Set.PairwiseDisjoint.biUnion_finset`. -/
theorem PairwiseDisjoint.biUnion {s : Set ι'} {g : ι' → Set ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => ⨆ i ∈ g i', f i)
    (hg : ∀ i ∈ s, (g i).PairwiseDisjoint f) : (⋃ i ∈ s, g i).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd ▸ ha) hb hab
  -- Porting note: the elaborator couldn't figure out `f` here.
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono
      (le_iSup₂ (f := fun i (_ : i ∈ g c) => f i) a ha)
      (le_iSup₂ (f := fun i (_ : i ∈ g d) => f i) b hb)

/-- If the suprema of columns are pairwise disjoint and suprema of rows as well, then everything is
pairwise disjoint. Not to be confused with `Set.PairwiseDisjoint.prod`. -/
theorem PairwiseDisjoint.prod_left {f : ι × ι' → α}
    (hs : s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i'))
    (ht : t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i')) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f := by
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h
  rw [mem_prod] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht hi.2 hj.2 <| (Prod.mk.inj_left _).ne_iff.1 h).mono ?_ ?_
    · convert le_iSup₂ (α := α) i hi.1; rfl
    · convert le_iSup₂ (α := α) i hj.1; rfl
  · refine (hs hi.1 hj.1 hij).mono ?_ ?_
    · convert le_iSup₂ (α := α) i' hi.2; rfl
    · convert le_iSup₂ (α := α) j' hj.2; rfl

end CompleteLattice

section Frame

variable [Frame α]

theorem pairwiseDisjoint_prod_left {s : Set ι} {t : Set ι'} {f : ι × ι' → α} :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f ↔
      (s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i')) ∧
        t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i') := by
  refine
      ⟨fun h => ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩, fun h => h.1.prod_left h.2⟩ <;>
    simp_rw [Function.onFun, iSup_disjoint_iff, disjoint_iSup_iff] <;>
    intro i' hi' j' hj'
  · exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne Prod.fst hij)
  · exact h (mk_mem_prod hi' hi) (mk_mem_prod hj' hj) (ne_of_apply_ne Prod.snd hij)

end Frame

theorem biUnion_diff_biUnion_eq {s t : Set ι} {f : ι → Set α} (h : (s ∪ t).PairwiseDisjoint f) :
    ((⋃ i ∈ s, f i) \ ⋃ i ∈ t, f i) = ⋃ i ∈ s \ t, f i := by
  refine
    (biUnion_diff_biUnion_subset f s t).antisymm
      (iUnion₂_subset fun i hi a ha => (mem_diff _).2 ⟨mem_biUnion hi.1 ha, ?_⟩)
  rw [mem_iUnion₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def biUnionEqSigmaOfDisjoint {s : Set ι} {f : ι → Set α} (h : s.PairwiseDisjoint f) :
    (⋃ i ∈ s, f i) ≃ Σi : s, f i :=
  (Equiv.setCongr (biUnion_eq_iUnion _ _)).trans <|
    unionEqSigmaOfDisjoint fun ⟨_i, hi⟩ ⟨_j, hj⟩ ne => h hi hj fun eq => ne <| Subtype.eq eq

end Set

section

variable {f : ι → Set α} {s t : Set ι}

/- Start of proof attempt -/
lemma round1_pairwiseDisjoint_imp (s : Set ι) (f : ι → Set α) :
    s.PairwiseDisjoint f → ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  intro h1 i hi j hj h2
  by_cases h3 : i = j
  · exact h3
  · -- Case i ≠ j
    have h4 : Disjoint (f i) (f j) := h1 hi hj h3
    have h5 : (f i ∩ f j).Nonempty := h2
    have h6 : f i ∩ f j = ∅ := by simpa [Set.disjoint_iff_inter_eq_empty] using h4
    rw [h6] at h5
    simp at h5

lemma round1_imp_pairwiseDisjoint (s : Set ι) (f : ι → Set α) :
    (∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j) → s.PairwiseDisjoint f := by
  intro h
  intro i hi j hj h3
  have h4 : Disjoint (f i) (f j) := by
    by_contra h5
    have h6 : (f i ∩ f j).Nonempty := by
      have h61 : ¬Disjoint (f i) (f j) := h5
      have h62 : ∃ x, x ∈ f i ∩ f j := by
        by_contra h63
        have h64 : f i ∩ f j = ∅ := by
          simp_all [Set.eq_empty_iff_forall_not_mem]
        have h65 : Disjoint (f i) (f j) := by
          simpa [Set.disjoint_iff_inter_eq_empty] using h64
        contradiction
      obtain ⟨x, hx⟩ := h62
      exact ⟨x, hx⟩
    have h7 : i = j := h hi hj h6
    contradiction
  exact h4

theorem Set.pairwiseDisjoint_iff :
    s.PairwiseDisjoint f ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j  := by

  constructor
  · exact round1_pairwiseDisjoint_imp s f
  · exact round1_imp_pairwiseDisjoint s f
