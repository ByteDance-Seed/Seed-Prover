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

/- Start of proof attempt -/
lemma round1_ι_timeOrderF_superCommuteF_neq_time {𝓕 : FieldSpecification}
    {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : ¬ (crAnTimeOrderRel φ ψ ∧ crAnTimeOrderRel ψ φ)) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * b) = 0 := by
  have h1 : ¬ crAnTimeOrderRel φ ψ ∨ ¬ crAnTimeOrderRel ψ φ := by
    by_contra h
    have h2 : crAnTimeOrderRel φ ψ ∧ crAnTimeOrderRel ψ φ := by
      constructor <;> tauto
    exact hφψ h2
  cases h1 with
  | inl h1 =>
    have h3 : FieldSpecification.FieldOpFreeAlgebra.timeOrderF (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ) * b) = 0 := by
      exact FieldSpecification.FieldOpFreeAlgebra.timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_not_crAnTimeOrderRel_mid h1 a b
    exact?
  | inr h2 =>
    have h3 : FieldSpecification.FieldOpFreeAlgebra.timeOrderF (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ) * b) = 0 := by
      exact FieldSpecification.FieldOpFreeAlgebra.timeOrderF_superCommuteF_ofCrAnOpF_ofCrAnOpF_not_crAnTimeOrderRel_mid h2 a b
    have h4 : (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ) = -(FieldStatistic.exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ) • (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ) := by
      exact FieldSpecification.FieldOpFreeAlgebra.superCommuteF_ofCrAnOpF_ofCrAnOpF_symm φ ψ
    have h5 : FieldSpecification.FieldOpFreeAlgebra.timeOrderF (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ) * b) = 0 := by
      have h6 : a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ) * b = a * (-(FieldStatistic.exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ) • (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ)) * b := by
        rw [h4]
        <;> ring
      rw [h6]
      have h7 : a * (-(FieldStatistic.exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ) • (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ)) * b = (-(FieldStatistic.exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ)) • (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ) * b) := by
        simp [mul_smul_comm, smul_mul_assoc, mul_assoc]
        <;> ring
      rw [h7]
      have h8 : FieldSpecification.FieldOpFreeAlgebra.timeOrderF ((-(FieldStatistic.exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ)) • (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ) * b)) = (-(FieldStatistic.exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ)) • FieldSpecification.FieldOpFreeAlgebra.timeOrderF (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ) * b) := by
        simp [smul_eq_mul]
      rw [h8]
      have h9 : FieldSpecification.FieldOpFreeAlgebra.timeOrderF (a * (FieldSpecification.FieldOpFreeAlgebra.superCommuteF (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF ψ)) (FieldSpecification.FieldOpFreeAlgebra.ofCrAnOpF φ) * b) = 0 := h3
      rw [h9]
      simp
    exact?

theorem ι_timeOrderF_superCommuteF_neq_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : ¬ (crAnTimeOrderRel φ ψ ∧ crAnTimeOrderRel ψ φ)) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca * b) = 0  := by

  exact round1_ι_timeOrderF_superCommuteF_neq_time hφψ a b
