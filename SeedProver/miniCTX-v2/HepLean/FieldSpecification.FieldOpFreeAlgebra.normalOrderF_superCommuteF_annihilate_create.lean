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


/- Start of proof attempt -/
lemma round1_h3 (φc φa : 𝓕.CrAnFieldOp)
  (a b : 𝓕.FieldOpFreeAlgebra):
  a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b = (a * ofCrAnOpF φa * ofCrAnOpF φc * b) - 𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) • (a * ofCrAnOpF φc * ofCrAnOpF φa * b) := by
  simp [superCommuteF_ofCrAnOpF_ofCrAnOpF, mul_sub, sub_mul, mul_assoc, smul_mul_assoc, mul_smul_comm]
  <;> ring

theorem normalOrderF_superCommuteF_annihilate_create (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b) = 0  := by


  have h25 : (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) * 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa)) = 1 := by
    have h251 : (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) : ℂ) * (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) : ℂ) = 1 := by
      exact?
    have h252 : (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) : ℂ) * (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) : ℂ) = 1 := by
      have h253 : (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) : ℂ) * (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) : ℂ) = 1 := h251
      have h254 : (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) : ℂ) * (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) : ℂ) = (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) : ℂ) * (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) : ℂ) := by ring
      rw [h254, h253]
      <;> simp
    simpa using h252
  have h26 : 𝓝ᶠ(a * ofCrAnOpF φc * ofCrAnOpF φa * b) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) • 𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) := by
    exact normalOrderF_swap_create_annihilate φc φa hφc hφa a b
  have h3 : a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b = (a * ofCrAnOpF φa * ofCrAnOpF φc * b) - 𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) • (a * ofCrAnOpF φc * ofCrAnOpF φa * b) := by
    exact round1_h3 φc φa a b
  have h4 : 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b) = 𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) - 𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) • 𝓝ᶠ(a * ofCrAnOpF φc * ofCrAnOpF φa * b) := by
    rw [h3]
    rw [map_sub, map_smul]
    <;> simp
  have h5 : 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b) = 𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) - 𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) • (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) • 𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b)) := by
    rw [h4]
    rw [h26]
    <;> ring
  have h6 : 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b) = 𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) - (𝓢(𝓕 |>ₛ φa, 𝓕 |>ₛ φc) * 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa)) • 𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) := by
    rw [h5]
    simp [smul_smul]
    <;> ring
  rw [h6]
  rw [h25]
  simp
  <;> ring
