-- In HepLean/HepLean/PerturbationTheory/FieldOpAlgebra/TimeOrder.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.TimeOrder
import HepLean.PerturbationTheory.FieldOpAlgebra.SuperCommute
/-!

# Time Ordering on Field operator algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

lemma ι_timeOrderF_superCommuteF_superCommuteF_eq_time_ofCrAnListF {φ1 φ2 φ3 : 𝓕.CrAnFieldOp}
    (φs1 φs2 : List 𝓕.CrAnFieldOp) (h :
      crAnTimeOrderRel φ1 φ2 ∧ crAnTimeOrderRel φ1 φ3 ∧
      crAnTimeOrderRel φ2 φ1 ∧ crAnTimeOrderRel φ2 φ3 ∧
      crAnTimeOrderRel φ3 φ1 ∧ crAnTimeOrderRel φ3 φ2) :
    ι 𝓣ᶠ(ofCrAnListF φs1 * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca *
    ofCrAnListF φs2) = 0 := by
  let l1 :=
    (List.takeWhile (fun c => ¬ crAnTimeOrderRel φ1 c)
    ((φs1 ++ φs2).insertionSort crAnTimeOrderRel))
    ++ (List.filter (fun c => crAnTimeOrderRel φ1 c ∧ crAnTimeOrderRel c φ1) φs1)
  let l2 := (List.filter (fun c => crAnTimeOrderRel φ1 c ∧ crAnTimeOrderRel c φ1) φs2)
    ++ (List.filter (fun c => crAnTimeOrderRel φ1 c ∧ ¬ crAnTimeOrderRel c φ1)
    ((φs1 ++ φs2).insertionSort crAnTimeOrderRel))
  have h123 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ1, φ2, φ3]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ1, φ2, φ3] φs2
      (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ1 :: φ2 :: φ3 :: φs2 = φs1 ++ [φ1, φ2, φ3] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [List.append_assoc, List.singleton_append, decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
  have h132 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ1 :: φ3 :: φ2 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ1, φ3, φ2]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ1, φ3, φ2] φs2
        (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ1 :: φ3 :: φ2 :: φs2 = φs1 ++ [φ1, φ3, φ2] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [List.singleton_append, decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
    congr 1
    have hp : List.Perm [φ1, φ3, φ2] [φ1, φ2, φ3] := by
      refine List.Perm.cons φ1 ?_
      exact List.Perm.swap φ2 φ3 []
    rw [crAnTimeOrderSign, Wick.koszulSign_perm_eq _ _ φ1 _ _ _ _ _ hp, ← crAnTimeOrderSign]
    · simp
    · intro φ4 hφ4
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ4
      rcases hφ4 with hφ4 | hφ4 | hφ4
      all_goals
        subst hφ4
        simp_all
  have hp231 : List.Perm [φ2, φ3, φ1] [φ1, φ2, φ3] := by
      refine List.Perm.trans (l₂ := [φ2, φ1, φ3]) ?_ ?_
      refine List.Perm.cons φ2 (List.Perm.swap φ1 φ3 [])
      exact List.Perm.swap φ1 φ2 [φ3]
  have h231 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ2 :: φ3 :: φ1 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ2, φ3, φ1]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ2, φ3, φ1] φs2
        (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ2 :: φ3 :: φ1 :: φs2 = φs1 ++ [φ2, φ3, φ1] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [List.singleton_append, decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
    congr 1
    rw [crAnTimeOrderSign, Wick.koszulSign_perm_eq _ _ φ1 _ _ _ _ _ hp231, ← crAnTimeOrderSign]
    · simp
    · intro φ4 hφ4
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ4
      rcases hφ4 with hφ4 | hφ4 | hφ4
      all_goals
        subst hφ4
        simp_all
  have h321 : ι 𝓣ᶠ(ofCrAnListF (φs1 ++ φ3 :: φ2 :: φ1 :: φs2)) =
      crAnTimeOrderSign (φs1 ++ φ1 :: φ2 :: φ3 :: φs2)
      • (ι (ofCrAnListF l1) * ι (ofCrAnListF [φ3, φ2, φ1]) * ι (ofCrAnListF l2)) := by
    have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ1 φs1 [φ3, φ2, φ1] φs2
        (by simp_all)
    rw [timeOrderF_ofCrAnListF, show φs1 ++ φ3 :: φ2 :: φ1 :: φs2 = φs1 ++ [φ3, φ2, φ1] ++ φs2
      by simp, crAnTimeOrderList, h1]
    simp only [List.singleton_append, decide_not,
      Bool.decide_and, ofCrAnListF_append, map_smul, map_mul, l1, l2, mul_assoc]
    congr 1
    have hp : List.Perm [φ3, φ2, φ1] [φ1, φ2, φ3] := by
      refine List.Perm.trans ?_ hp231
      exact List.Perm.swap φ2 φ3 [φ1]
    rw [crAnTimeOrderSign, Wick.koszulSign_perm_eq _ _ φ1 _ _ _ _ _ hp, ← crAnTimeOrderSign]
    · simp
    · intro φ4 hφ4
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hφ4
      rcases hφ4 with hφ4 | hφ4 | hφ4
      all_goals
        subst hφ4
        simp_all
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rw [superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [List.singleton_append, instCommGroup.eq_1, ofList_singleton, map_sub, map_smul]
  rw [superCommuteF_ofCrAnListF_ofCrAnListF, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [List.cons_append, List.nil_append, instCommGroup.eq_1, ofList_singleton, mul_sub, ←
    ofCrAnListF_append, Algebra.mul_smul_comm, sub_mul, List.append_assoc, Algebra.smul_mul_assoc,
    map_sub, map_smul]
  rw [h123, h132, h231, h321]
  simp only [smul_smul]
  rw [mul_comm, ← smul_smul, mul_comm, ← smul_smul]
  rw [← smul_sub, ← smul_sub, smul_smul, mul_comm, ← smul_smul, ← smul_sub]
  simp only [smul_eq_zero]
  right
  rw [← smul_mul_assoc, ← mul_smul_comm, mul_assoc]
  rw [← smul_mul_assoc, ← mul_smul_comm]
  rw [smul_sub]
  rw [← smul_mul_assoc, ← mul_smul_comm]
  rw [← smul_mul_assoc, ← mul_smul_comm]
  repeat rw [mul_assoc]
  rw [← mul_sub, ← mul_sub, ← mul_sub]
  rw [← sub_mul, ← sub_mul, ← sub_mul]
  trans ι (ofCrAnListF l1) * ι [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca *
    ι (ofCrAnListF l2)
  rw [mul_assoc]
  congr
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rw [superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [List.singleton_append, instCommGroup.eq_1, ofList_singleton, map_sub, map_smul]
  rw [superCommuteF_ofCrAnListF_ofCrAnListF, superCommuteF_ofCrAnListF_ofCrAnListF]
  simp only [List.cons_append, List.nil_append, instCommGroup.eq_1, ofList_singleton, map_sub,
    map_smul, smul_sub]
  simp_all

lemma ι_timeOrderF_superCommuteF_superCommuteF_ofCrAnListF {φ1 φ2 φ3 : 𝓕.CrAnFieldOp}
    (φs1 φs2 : List 𝓕.CrAnFieldOp) :
    ι 𝓣ᶠ(ofCrAnListF φs1 * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca * ofCrAnListF φs2)
    = 0 := by
  by_cases h :
      crAnTimeOrderRel φ1 φ2 ∧ crAnTimeOrderRel φ1 φ3 ∧
      crAnTimeOrderRel φ2 φ1 ∧ crAnTimeOrderRel φ2 φ3 ∧
      crAnTimeOrderRel φ3 φ1 ∧ crAnTimeOrderRel φ3 φ2
  · exact ι_timeOrderF_superCommuteF_superCommuteF_eq_time_ofCrAnListF φs1 φs2 h
  · rw [timeOrderF_timeOrderF_mid]
    rw [timeOrderF_superCommuteF_ofCrAnOpF_superCommuteF_all_not_crAnTimeOrderRel _ _ _ h]
    simp

@[simp]
lemma ι_timeOrderF_superCommuteF_superCommuteF {φ1 φ2 φ3 : 𝓕.CrAnFieldOp}
    (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca * b) = 0 := by
  let pb (b : 𝓕.FieldOpFreeAlgebra) (hc : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
    Prop := ι 𝓣ᶠ(a * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca * b) = 0
  change pb b (Basis.mem_span _ b)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList, pb]
    let pa (a : 𝓕.FieldOpFreeAlgebra) (hc : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
      Prop := ι 𝓣ᶠ(a * [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca * ofCrAnListF φs) = 0
    change pa a (Basis.mem_span _ a)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp only [ofListBasis_eq_ofList, pa]
      exact ι_timeOrderF_superCommuteF_superCommuteF_ofCrAnListF φs' φs
    · simp [pa]
    · intro x y hx hy hpx hpy
      simp_all [pa,mul_add, add_mul]
    · intro x hx hpx
      simp_all [pa, hpx]
  · simp [pb]
  · intro x y hx hy hpx hpy
    simp_all [pb,mul_add, add_mul]
  · intro x hx hpx
    simp_all [pb, hpx]

lemma ι_timeOrderF_superCommuteF_eq_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : crAnTimeOrderRel φ ψ) (hψφ : crAnTimeOrderRel ψ φ) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * b) =
    ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * 𝓣ᶠ(a * b)) := by
  let pb (b : 𝓕.FieldOpFreeAlgebra) (hc : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
    Prop := ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * b) =
    ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * 𝓣ᶠ(a * b))
  change pb b (Basis.mem_span _ b)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList, map_mul, pb]
    let pa (a : 𝓕.FieldOpFreeAlgebra) (hc : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
      Prop := ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * ofCrAnListF φs) =
      ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * 𝓣ᶠ(a* ofCrAnListF φs))
    change pa a (Basis.mem_span _ a)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp only [ofListBasis_eq_ofList, map_mul, pa]
      conv_lhs =>
        rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF]
        simp [mul_sub, sub_mul, ← ofCrAnListF_append]
        rw [timeOrderF_ofCrAnListF, timeOrderF_ofCrAnListF]
      have h1 : crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) =
          crAnTimeOrderSign (φs' ++ ψ :: φ :: φs) := by
        trans crAnTimeOrderSign (φs' ++ [φ, ψ] ++ φs)
        simp only [List.append_assoc, List.cons_append, List.nil_append]
        rw [crAnTimeOrderSign]
        have hp : List.Perm [φ,ψ] [ψ,φ] := by exact List.Perm.swap ψ φ []
        rw [Wick.koszulSign_perm_eq _ _ φ _ _ _ _ _ hp]
        simp only [List.append_assoc, List.cons_append, List.singleton_append]
        rfl
        simp_all
      rw [h1]
      simp only [map_smul]
      have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [φ, ψ] φs
        (by simp_all)
      rw [crAnTimeOrderList, show φs' ++ φ :: ψ :: φs = φs' ++ [φ, ψ] ++ φs by simp, h1]
      have h2 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [ψ, φ] φs
        (by simp_all)
      rw [crAnTimeOrderList, show φs' ++ ψ :: φ :: φs = φs' ++ [ψ, φ] ++ φs by simp, h2]
      repeat rw [ofCrAnListF_append]
      rw [smul_smul, mul_comm, ← smul_smul, ← smul_sub]
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      rw [← mul_smul_comm]
      rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
      rw [← mul_sub, ← mul_sub, mul_smul_comm, mul_smul_comm, ← smul_mul_assoc,
        ← smul_mul_assoc]
      rw [← sub_mul]
      have h1 : (ι (ofCrAnListF [φ, ψ]) -
          (exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ) • ι (ofCrAnListF [ψ, φ])) =
        ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca := by
        rw [superCommuteF_ofCrAnOpF_ofCrAnOpF]
        rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_append]
        simp only [instCommGroup.eq_1, List.singleton_append, Algebra.smul_mul_assoc, map_sub,
          map_smul]
        rw [← ofCrAnListF_append]
        simp
      rw [h1]
      have hc : ι ((superCommuteF (ofCrAnOpF φ)) (ofCrAnOpF ψ)) ∈
          Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
        apply ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center
      rw [Subalgebra.mem_center_iff] at hc
      repeat rw [← mul_assoc]
      rw [hc]
      repeat rw [mul_assoc]
      rw [smul_mul_assoc]
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      rw [← ofCrAnListF_append, ← ofCrAnListF_append, ← ofCrAnListF_append, ← ofCrAnListF_append]
      have h1 := insertionSort_of_takeWhile_filter 𝓕.crAnTimeOrderRel φ φs' φs
      simp only [decide_not, Bool.decide_and, List.append_assoc, List.cons_append,
        List.singleton_append, Algebra.mul_smul_comm, map_mul] at h1 ⊢
      rw [← h1]
      rw [← crAnTimeOrderList]
      by_cases hq : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)
      · rw [ι_superCommuteF_of_diff_statistic hq]
        simp
      · rw [crAnTimeOrderSign, Wick.koszulSign_eq_rel_eq_stat _ _, ← crAnTimeOrderSign]
        rw [timeOrderF_ofCrAnListF]
        simp only [map_smul, Algebra.mul_smul_comm]
        simp only [List.nil_append]
        exact hψφ
        exact hφψ
        simpa using hq
    · simp only [map_mul, zero_mul, map_zero, mul_zero, pa]
    · intro x y hx hy hpx hpy
      simp_all [pa,mul_add, add_mul]
    · intro x hx hpx
      simp_all [pa, hpx]
  · simp only [map_mul, mul_zero, map_zero, pb]
  · intro x y hx hy hpx hpy
    simp_all [pb,mul_add, add_mul]
  · intro x hx hpx
    simp_all [pb, hpx]

lemma ι_timeOrderF_superCommuteF_neq_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : ¬ (crAnTimeOrderRel φ ψ ∧ crAnTimeOrderRel ψ φ)) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * b) = 0 := by
  rw [timeOrderF_timeOrderF_mid]
  have hφψ : ¬ (crAnTimeOrderRel φ ψ) ∨ ¬ (crAnTimeOrderRel ψ φ) := by
    exact Decidable.not_and_iff_or_not.mp hφψ
  rcases hφψ with hφψ | hφψ
  · rw [timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_not_crAnTimeOrderRel]
    simp_all only [false_and, not_false_eq_true, false_or, mul_zero, zero_mul, map_zero]
    simp_all
  · rw [superCommuteF_ofCrAnOpF_ofCrAnOpF_symm]
    simp only [instCommGroup.eq_1, neg_smul, map_neg, map_smul, mul_neg, Algebra.mul_smul_comm,
      neg_mul, Algebra.smul_mul_assoc, neg_eq_zero, smul_eq_zero]
    rw [timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_not_crAnTimeOrderRel]
    simp only [mul_zero, zero_mul, map_zero, or_true]
    simp_all

/-!

## Defining time order for `FiedOpAlgebra`.

-/

lemma ι_timeOrderF_zero_of_mem_ideal (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι 𝓣ᶠ(a) = 0 := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
  let p {k : Set 𝓕.FieldOpFreeAlgebra} (a : FieldOpFreeAlgebra 𝓕)
    (h : a ∈ AddSubgroup.closure k) := ι 𝓣ᶠ(a) = 0
  change p a h
  apply AddSubgroup.closure_induction
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨a, ha, c, hc, rfl⟩ := ha
    simp only [p]
    simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq] at hc
    match hc with
    | Or.inl hc =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      simp only [ι_timeOrderF_superCommuteF_superCommuteF]
    | Or.inr (Or.inl hc) =>
      obtain ⟨φa, hφa, φb, hφb, rfl⟩ := hc
      by_cases heqt : (crAnTimeOrderRel φa φb ∧ crAnTimeOrderRel φb φa)
      · rw [ι_timeOrderF_superCommuteF_eq_time]
        simp only [map_mul]
        rw [ι_superCommuteF_of_create_create]
        simp only [zero_mul]
        · exact hφa
        · exact hφb
        · exact heqt.1
        · exact heqt.2
      · rw [ι_timeOrderF_superCommuteF_neq_time heqt]
    | Or.inr (Or.inr (Or.inl hc)) =>
      obtain ⟨φa, hφa, φb, hφb, rfl⟩ := hc
      by_cases heqt : (crAnTimeOrderRel φa φb ∧ crAnTimeOrderRel φb φa)
      · rw [ι_timeOrderF_superCommuteF_eq_time]
        simp only [map_mul]
        rw [ι_superCommuteF_of_annihilate_annihilate]
        simp only [zero_mul]
        · exact hφa
        · exact hφb
        · exact heqt.1
        · exact heqt.2
      · rw [ι_timeOrderF_superCommuteF_neq_time heqt]
    | Or.inr (Or.inr (Or.inr hc)) =>
      obtain ⟨φa, φb, hdiff, rfl⟩ := hc
      by_cases heqt : (crAnTimeOrderRel φa φb ∧ crAnTimeOrderRel φb φa)
      · rw [ι_timeOrderF_superCommuteF_eq_time]
        simp only [map_mul]
        rw [ι_superCommuteF_of_diff_statistic]
        simp only [zero_mul]
        · exact hdiff
        · exact heqt.1
        · exact heqt.2
      · rw [ι_timeOrderF_superCommuteF_neq_time heqt]
  · simp [p]
  · intro x y hx hy
    simp only [map_add, p]
    intro h1 h2
    simp [h1, h2]
  · intro x hx
    simp [p]

lemma ι_timeOrderF_eq_of_equiv (a b : 𝓕.FieldOpFreeAlgebra) (h : a ≈ b) :
    ι 𝓣ᶠ(a) = ι 𝓣ᶠ(b) := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_timeOrderF_zero_of_mem_ideal (a - b) h

/-- For a field specification `𝓕`, `timeOrder` is the linear map

`FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕`

defined as the decent of `ι ∘ₗ timeOrderF : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕` from
`FieldOpFreeAlgebra 𝓕` to `FieldOpAlgebra 𝓕`.
This decent exists because `ι ∘ₗ timeOrderF` is well-defined on equivalence classes.

The notation `𝓣(a)` is used for `timeOrder a`. -/
noncomputable def timeOrder : FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ timeOrderF) ι_timeOrderF_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

@[inherit_doc timeOrder]
scoped[FieldSpecification.FieldOpAlgebra] notation "𝓣(" a ")" => timeOrder a

/-!

## Properties of time ordering

-/

lemma timeOrder_eq_ι_timeOrderF (a : 𝓕.FieldOpFreeAlgebra) :
    𝓣(ι a) = ι 𝓣ᶠ(a) := rfl

lemma timeOrder_ofFieldOp_ofFieldOp_ordered {φ ψ : 𝓕.FieldOp} (h : timeOrderRel φ ψ) :
    𝓣(ofFieldOp φ * ofFieldOp ψ) = ofFieldOp φ * ofFieldOp ψ := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, timeOrder_eq_ι_timeOrderF,
    timeOrderF_ofFieldOpF_ofFieldOpF_ordered h]

lemma timeOrder_ofFieldOp_ofFieldOp_not_ordered {φ ψ : 𝓕.FieldOp} (h : ¬ timeOrderRel φ ψ) :
    𝓣(ofFieldOp φ * ofFieldOp ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • ofFieldOp ψ * ofFieldOp φ := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, timeOrder_eq_ι_timeOrderF,
    timeOrderF_ofFieldOpF_ofFieldOpF_not_ordered h]
  simp

lemma timeOrder_ofFieldOp_ofFieldOp_not_ordered_eq_timeOrder {φ ψ : 𝓕.FieldOp}
    (h : ¬ timeOrderRel φ ψ) :
    𝓣(ofFieldOp φ * ofFieldOp ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • 𝓣(ofFieldOp ψ * ofFieldOp φ) := by
  rw [ofFieldOp, ofFieldOp, ← map_mul, timeOrder_eq_ι_timeOrderF,
    timeOrderF_ofFieldOpF_ofFieldOpF_not_ordered_eq_timeOrderF h]
  simp only [instCommGroup.eq_1, map_smul]
  rfl

lemma timeOrder_ofFieldOpList_nil : 𝓣(ofFieldOpList (𝓕 := 𝓕) []) = 1 := by
  rw [ofFieldOpList, timeOrder_eq_ι_timeOrderF, timeOrderF_ofFieldOpListF_nil]
  simp

/- Start of proof attempt -/
lemma round1_h1 (𝓕 : FieldSpecification)
  (φ : 𝓕.FieldOp):
  timeOrderF (ofFieldOpListF [φ]) = ofFieldOpListF [φ] := by
  exact timeOrderF_ofFieldOpListF_singleton φ

lemma round1_h2 (𝓕 : FieldSpecification)
  (φ : 𝓕.FieldOp)
  (h1 : timeOrderF (ofFieldOpListF [φ]) = ofFieldOpListF [φ]):
  𝓣(ι (ofFieldOpListF [φ])) = ι (ofFieldOpListF [φ]) := by
  have h21 : 𝓣(ι (ofFieldOpListF [φ])) = ι 𝓣ᶠ(ofFieldOpListF [φ]) := by
    rw [timeOrder_eq_ι_timeOrderF]
  have h22 : 𝓣ᶠ(ofFieldOpListF [φ]) = ofFieldOpListF [φ] := h1
  rw [h21, h22]
  <;> simp

lemma round1_h3 (𝓕 : FieldSpecification)
  (φ : 𝓕.FieldOp)
  (h2 : 𝓣(ι (ofFieldOpListF [φ])) = ι (ofFieldOpListF [φ])):
  𝓣(ofFieldOpList [φ]) = ofFieldOpList [φ] := by
  have h31 : ofFieldOpList [φ] = ι (ofFieldOpListF [φ]) := rfl
  rw [h31]
  exact h2

theorem timeOrder_ofFieldOpList_singleton (φ : 𝓕.FieldOp) :
    𝓣(ofFieldOpList [φ]) = ofFieldOpList [φ]  := by

  have h1 : timeOrderF (ofFieldOpListF [φ]) = ofFieldOpListF [φ] := by
    exact round1_h1 𝓕 φ
  have h2 : 𝓣(ι (ofFieldOpListF [φ])) = ι (ofFieldOpListF [φ]) := by
    exact round1_h2 𝓕 φ h1
  exact round1_h3 𝓕 φ h2
