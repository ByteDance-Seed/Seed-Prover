-- In HepLean/HepLean/PerturbationTheory/FieldOpFreeAlgebra/NormalOrder.lean

/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.NormalOrder
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Normal Ordering in the FieldOpFreeAlgebra

In the module
`HepLean.PerturbationTheory.FieldSpecification.NormalOrder`
we defined the normal ordering of a list of `CrAnFieldOp`.
In this module we extend the normal ordering to a linear map on `FieldOpFreeAlgebra`.

We derive properties of this normal ordering.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section

/-- For a field specification `𝓕`, `normalOrderF` is the linear map

  `FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕`

  defined by its action on the basis `ofCrAnListF φs`, taking `ofCrAnListF φs` to

  `normalOrderSign φs • ofCrAnListF (normalOrderList φs)`.

  That is, `normalOrderF` normal-orders the field operators and multiplies by the sign of the
  normal order.

  The notation `𝓝ᶠ(a)` is used for `normalOrderF a` for `a` an element of
  `FieldOpFreeAlgebra 𝓕`. -/
def normalOrderF : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  normalOrderSign φs • ofCrAnListF (normalOrderList φs)

@[inherit_doc normalOrderF]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓝ᶠ(" a ")" => normalOrderF a

lemma normalOrderF_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF φs) = normalOrderSign φs • ofCrAnListF (normalOrderList φs) := by
  rw [← ofListBasis_eq_ofList, normalOrderF, Basis.constr_basis]

lemma ofCrAnListF_eq_normalOrderF (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListF (normalOrderList φs) = normalOrderSign φs • 𝓝ᶠ(ofCrAnListF φs) := by
  rw [normalOrderF_ofCrAnListF, normalOrderList, smul_smul, normalOrderSign,
    Wick.koszulSign_mul_self, one_smul]

lemma normalOrderF_one : normalOrderF (𝓕 := 𝓕) 1 = 1 := by
  rw [← ofCrAnListF_nil, normalOrderF_ofCrAnListF, normalOrderSign_nil, normalOrderList_nil,
    ofCrAnListF_nil, one_smul]

lemma normalOrderF_normalOrderF_mid (a b c : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * b * c) = 𝓝ᶠ(a * 𝓝ᶠ(b) * c) := by
  let pc (c : 𝓕.FieldOpFreeAlgebra) (hc : c ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
    Prop := 𝓝ᶠ(a * b * c) = 𝓝ᶠ(a * 𝓝ᶠ(b) * c)
  change pc c (Basis.mem_span _ c)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList, pc]
    let pb (b : 𝓕.FieldOpFreeAlgebra) (hb : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
      Prop := 𝓝ᶠ(a * b * ofCrAnListF φs) = 𝓝ᶠ(a * 𝓝ᶠ(b) * ofCrAnListF φs)
    change pb b (Basis.mem_span _ b)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp only [ofListBasis_eq_ofList, pb]
      let pa (a : 𝓕.FieldOpFreeAlgebra) (ha : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
        Prop := 𝓝ᶠ(a * ofCrAnListF φs' * ofCrAnListF φs) =
        𝓝ᶠ(a * 𝓝ᶠ(ofCrAnListF φs') * ofCrAnListF φs)
      change pa a (Basis.mem_span _ a)
      apply Submodule.span_induction
      · intro x hx
        obtain ⟨φs'', rfl⟩ := hx
        simp only [ofListBasis_eq_ofList, pa]
        rw [normalOrderF_ofCrAnListF]
        simp only [← ofCrAnListF_append, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, map_smul]
        rw [normalOrderF_ofCrAnListF, normalOrderF_ofCrAnListF, smul_smul]
        congr 1
        · simp only [normalOrderSign, normalOrderList]
          rw [Wick.koszulSign_of_append_eq_insertionSort, mul_comm]
        · congr 1
          simp only [normalOrderList]
          rw [HepLean.List.insertionSort_append_insertionSort_append]
      · simp [pa]
      · intro x y hx hy h1 h2
        simp_all [pa, add_mul]
      · intro x hx h
        simp_all [pa]
    · simp [pb]
    · intro x y hx hy h1 h2
      simp_all [pb, mul_add, add_mul]
    · intro x hx h
      simp_all [pb]
  · simp [pc]
  · intro x y hx hy h1 h2
    simp_all [pc, mul_add]
  · intro x hx h hp
    simp_all [pc]

lemma normalOrderF_normalOrderF_right (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * b) = 𝓝ᶠ(a * 𝓝ᶠ(b)) := by
  trans 𝓝ᶠ(a * b * 1)
  · simp
  · rw [normalOrderF_normalOrderF_mid]
    simp

lemma normalOrderF_normalOrderF_left (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * b) = 𝓝ᶠ(𝓝ᶠ(a) * b) := by
  trans 𝓝ᶠ(1 * a * b)
  · simp
  · rw [normalOrderF_normalOrderF_mid]
    simp

/-!

## Normal ordering with a creation operator on the left or annihilation on the right

-/

lemma normalOrderF_ofCrAnListF_cons_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF (φ :: φs)) = ofCrAnOpF φ * 𝓝ᶠ(ofCrAnListF φs) := by
  rw [normalOrderF_ofCrAnListF, normalOrderSign_cons_create φ hφ,
    normalOrderList_cons_create φ hφ φs]
  rw [ofCrAnListF_cons, normalOrderF_ofCrAnListF, mul_smul_comm]

lemma normalOrderF_create_mul (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (a : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(ofCrAnOpF φ * a) = ofCrAnOpF φ * 𝓝ᶠ(a) := by
  change (normalOrderF ∘ₗ mulLinearMap (ofCrAnOpF φ)) a =
    (mulLinearMap (ofCrAnOpF φ) ∘ₗ normalOrderF) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
    LinearMap.coe_comp, Function.comp_apply]
  rw [← ofCrAnListF_cons, normalOrderF_ofCrAnListF_cons_create φ hφ]

lemma normalOrderF_ofCrAnListF_append_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF (φs ++ [φ])) = 𝓝ᶠ(ofCrAnListF φs) * ofCrAnOpF φ := by
  rw [normalOrderF_ofCrAnListF, normalOrderSign_append_annihilate φ hφ φs,
    normalOrderList_append_annihilate φ hφ φs, ofCrAnListF_append, ofCrAnListF_singleton,
      normalOrderF_ofCrAnListF, smul_mul_assoc]

lemma normalOrderF_mul_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate)
    (a : FieldOpFreeAlgebra 𝓕) : 𝓝ᶠ(a * ofCrAnOpF φ) = 𝓝ᶠ(a) * ofCrAnOpF φ := by
  change (normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnOpF φ)) a =
    (mulLinearMap.flip (ofCrAnOpF φ) ∘ₗ normalOrderF) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_append, ofCrAnListF_singleton,
    normalOrderF_ofCrAnListF_append_annihilate φ hφ]

lemma normalOrderF_crPartF_mul (φ : 𝓕.FieldOp) (a : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(crPartF φ * a) =
    crPartF φ * 𝓝ᶠ(a) := by
  match φ with
  | .inAsymp φ =>
    rw [crPartF]
    exact normalOrderF_create_mul ⟨FieldOp.inAsymp φ, ()⟩ rfl a
  | .position φ =>
    rw [crPartF]
    exact normalOrderF_create_mul _ rfl _
  | .outAsymp φ => simp

lemma normalOrderF_mul_anPartF (φ : 𝓕.FieldOp) (a : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * anPartF φ) =
    𝓝ᶠ(a) * anPartF φ := by
  match φ with
  | .inAsymp φ => simp
  | .position φ =>
    rw [anPartF]
    exact normalOrderF_mul_annihilate _ rfl _
  | .outAsymp φ =>
    rw [anPartF]
    refine normalOrderF_mul_annihilate _ rfl _

/-!

## Normal ordering for an adjacent creation and annihliation state

The main result of this section is `normalOrderF_superCommuteF_annihilate_create`.
-/

lemma normalOrderF_swap_create_annihilate_ofCrAnListF_ofCrAnListF (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF φs' * ofCrAnOpF φc * ofCrAnOpF φa * ofCrAnListF φs) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(ofCrAnListF φs' * ofCrAnOpF φa * ofCrAnOpF φc * ofCrAnListF φs) := by
  rw [mul_assoc, mul_assoc, ← ofCrAnListF_cons, ← ofCrAnListF_cons, ← ofCrAnListF_append]
  rw [normalOrderF_ofCrAnListF, normalOrderSign_swap_create_annihilate φc φa hφc hφa]
  rw [normalOrderList_swap_create_annihilate φc φa hφc hφa, ← smul_smul, ← normalOrderF_ofCrAnListF]
  rw [ofCrAnListF_append, ofCrAnListF_cons, ofCrAnListF_cons]
  noncomm_ring

lemma normalOrderF_swap_create_annihilate_ofCrAnListF (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnFieldOp) (a : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(ofCrAnListF φs * ofCrAnOpF φc * ofCrAnOpF φa * a) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(ofCrAnListF φs * ofCrAnOpF φa * ofCrAnOpF φc * a) := by
  change (normalOrderF ∘ₗ mulLinearMap (ofCrAnListF φs * ofCrAnOpF φc * ofCrAnOpF φa)) a =
    (smulLinearMap _ ∘ₗ normalOrderF ∘ₗ
    mulLinearMap (ofCrAnListF φs * ofCrAnOpF φa * ofCrAnOpF φc)) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
    LinearMap.coe_comp, Function.comp_apply, instCommGroup.eq_1]
  rw [normalOrderF_swap_create_annihilate_ofCrAnListF_ofCrAnListF φc φa hφc hφa]
  rfl

lemma normalOrderF_swap_create_annihilate (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * ofCrAnOpF φc * ofCrAnOpF φa * b) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) := by
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  change (normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnOpF φc * (ofCrAnOpF φa * b))) a =
    (smulLinearMap (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa)) ∘ₗ
    normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnOpF φa * (ofCrAnOpF φc * b))) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) _
  simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, instCommGroup.eq_1, ← mul_assoc,
      normalOrderF_swap_create_annihilate_ofCrAnListF φc φa hφc hφa]
  rfl

lemma normalOrderF_superCommuteF_create_annihilate (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * [ofCrAnOpF φc, ofCrAnOpF φa]ₛca * b) = 0 := by
  simp only [superCommuteF_ofCrAnOpF_ofCrAnOpF, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [mul_sub, sub_mul, map_sub, ← smul_mul_assoc, ← mul_assoc, ← mul_assoc,
    normalOrderF_swap_create_annihilate φc φa hφc hφa]
  simp

lemma normalOrderF_superCommuteF_annihilate_create (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b) = 0 := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF_symm]
  simp only [instCommGroup.eq_1, neg_smul, mul_neg, Algebra.mul_smul_comm, neg_mul,
    Algebra.smul_mul_assoc, map_neg, map_smul, neg_eq_zero, smul_eq_zero]
  exact Or.inr (normalOrderF_superCommuteF_create_annihilate φc φa hφc hφa ..)

lemma normalOrderF_swap_crPartF_anPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * (crPartF φ) * (anPartF φ') * b) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓝ᶠ(a * (anPartF φ') * (crPartF φ) * b) := by
  match φ, φ' with
  | _, .inAsymp φ' => simp
  | .outAsymp φ, _ => simp
  | .position φ, .position φ' =>
    simp only [crPartF_position, anPartF_position, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihilate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl
  | .inAsymp φ, .outAsymp φ' =>
    simp only [crPartF_negAsymp, anPartF_posAsymp, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihilate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl
  | .inAsymp φ, .position φ' =>
    simp only [crPartF_negAsymp, anPartF_position, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihilate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl
  | .position φ, .outAsymp φ' =>
    simp only [crPartF_position, anPartF_posAsymp, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihilate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl

/-!

## Normal ordering for an anPartF and crPartF

Using the results from above.

-/

lemma normalOrderF_swap_anPartF_crPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * (anPartF φ) * (crPartF φ') * b) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝ᶠ(a * (crPartF φ') *
      (anPartF φ) * b) := by
  simp [normalOrderF_swap_crPartF_anPartF, smul_smul]

lemma normalOrderF_superCommuteF_crPartF_anPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * superCommuteF
      (crPartF φ) (anPartF φ') * b) = 0 := by
  match φ, φ' with
  | _, .inAsymp φ' => simp
  | .outAsymp φ', _ => simp
  | .position φ, .position φ' =>
    rw [crPartF_position, anPartF_position]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .inAsymp φ, .outAsymp φ' =>
    rw [crPartF_negAsymp, anPartF_posAsymp]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .inAsymp φ, .position φ' =>
    rw [crPartF_negAsymp, anPartF_position]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .position φ, .outAsymp φ' =>
    rw [crPartF_position, anPartF_posAsymp]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..

lemma normalOrderF_superCommuteF_anPartF_crPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * superCommuteF
    (anPartF φ) (crPartF φ') * b) = 0 := by
  match φ, φ' with
  | .inAsymp φ', _ => simp
  | _, .outAsymp φ' => simp
  | .position φ, .position φ' =>
    rw [anPartF_position, crPartF_position]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .outAsymp φ', .inAsymp φ =>
    simp only [anPartF_posAsymp, crPartF_negAsymp]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .position φ', .inAsymp φ =>
    simp only [anPartF_position, crPartF_negAsymp]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .outAsymp φ, .position φ' =>
    simp only [anPartF_posAsymp, crPartF_position]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..

/-!

## The normal ordering of a product of two states

-/

@[simp]
lemma normalOrderF_crPartF_mul_crPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(crPartF φ * crPartF φ') =
    crPartF φ * crPartF φ' := by
  rw [normalOrderF_crPartF_mul]
  conv_lhs => rw [← mul_one (crPartF φ')]
  rw [normalOrderF_crPartF_mul, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_anPartF_mul_anPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(anPartF φ * anPartF φ') =
    anPartF φ * anPartF φ' := by
  rw [normalOrderF_mul_anPartF]
  conv_lhs => rw [← one_mul (anPartF φ)]
  rw [normalOrderF_mul_anPartF, normalOrderF_one]
  simp

/- Start of proof attempt -/
lemma round1_normalOrderF_crPartF_mul_anPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(crPartF φ * anPartF φ') =
    crPartF φ * anPartF φ' := by
  have h1 : 𝓝ᶠ(crPartF φ * anPartF φ') = crPartF φ * 𝓝ᶠ(anPartF φ') := by
    exact normalOrderF_crPartF_mul φ (anPartF φ')
  have h2 : 𝓝ᶠ(1 * anPartF φ') = 𝓝ᶠ(1) * anPartF φ' := by
    exact normalOrderF_mul_anPartF φ' 1
  have h3 : 𝓝ᶠ(anPartF φ') = anPartF φ' := by
    have h21 : 𝓝ᶠ(1 * anPartF φ') = 𝓝ᶠ(1) * anPartF φ' := h2
    have h22 : (1 : FieldOpFreeAlgebra 𝓕) * anPartF φ' = anPartF φ' := by
      rw [one_mul]
    have h23 : 𝓝ᶠ(1) = 1 := @normalOrderF_one 𝓕
    rw [h22] at h21
    rw [h23] at h21
    rw [one_mul] at h21
    exact h21
  rw [h1, h3]
  <;> ring

theorem normalOrderF_crPartF_mul_anPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(crPartF φ * anPartF φ') =
    crPartF φ * anPartF φ'  := by

  exact round1_normalOrderF_crPartF_mul_anPartF φ φ'
