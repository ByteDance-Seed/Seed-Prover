-- In mathlib/Mathlib/Algebra/Module/ZLattice/Covolume.lean

/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite dimensional real vector space.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
value of the determinant of any `ℤ`-basis of `L`.

* `ZLattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
when `n : ℕ` tends to infinity. See also `ZLattice.covolume.tendsto_card_div_pow'` for a version
for `InnerProductSpace ℝ E` and `ZLattice.covolume.tendsto_card_div_pow''` for the general version.

* `ZLattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such that
`F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L` when `c : ℝ` tends to
infinity. See also `ZLattice.covolume.tendsto_card_le_div'` for a version for
`InnerProductSpace ℝ E` and `ZLattice.covolume.tendsto_card_le_div''` for the general version.

## Naming convention

Some results are true in the case where the ambient finite dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for eg. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for eg.
`volume_image_eq_volume_div_covolume'`. When the same result exists in the
general case, we had two primes, eg. `covolume.tendsto_card_div_pow''`.

-/

noncomputable section

namespace ZLattice

open Submodule MeasureTheory Module MeasureTheory Module ZSpan

section General

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] (L : Submodule ℤ E)

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = (μ F).toReal := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    ENNReal.toReal_ne_zero]
  refine ⟨measure_fundamentalDomain_ne_zero _, ne_of_lt ?_⟩
  exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[ℝ] E} (he : MeasurePreserving e ν μ) :
    covolume (ZLattice.comap ℝ L e.toLinearMap) ν = covolume L μ := by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeComap ℝ L e.toLinearEquiv) ν)), ← he.measure_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet, ← e.image_symm_eq_preimage,
    ← e.symm.coe_toLinearEquiv, map_fundamentalDomain]
  congr!
  ext; simp

theorem covolume_eq_det_mul_measure {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * (μ (fundamentalDomain b₀)).toReal := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    measure_fundamentalDomain _ _ b₀,
    measure_congr (fundamentalDomain_ae_parallelepiped b₀ μ), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  congr
  ext
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    volume_fundamentalDomain, ENNReal.toReal_ofReal (by positivity)]
  congr
  ext1
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(LinearEquiv.det (b.ofZLatticeBasis ℝ L).equivFun : ℝ)|⁻¹ := by
  rw [covolume_eq_det L b, ← Pi.basisFun_det_apply, show (((↑) : L → _) ∘ ⇑b) =
    (b.ofZLatticeBasis ℝ) by ext; simp, ← Basis.det_inv, ← abs_inv, Units.val_inv_eq_inv_val,
    IsUnit.unit_spec, ← Basis.det_basis, LinearEquiv.coe_det]
  rfl

theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L)
    {s : Set (ι → ℝ)} :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  rw [LinearEquiv.image_eq_preimage, Measure.addHaar_preimage_linearEquiv, LinearEquiv.symm_symm,
    covolume_eq_det_inv L b, ENNReal.div_eq_inv_mul, ENNReal.ofReal_inv_of_pos
    (abs_pos.mpr (LinearEquiv.det _).ne_zero), inv_inv, LinearEquiv.coe_det]

/-- A more general version of `ZLattice.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction. -/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) = volume s / ENNReal.ofReal (covolume L) := by
  classical
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis ℝ)])
  let f := (EuclideanSpace.equiv ι ℝ).symm.trans
    ((stdOrthonormalBasis ℝ E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr_symm.comp
      (EuclideanSpace.volume_preserving_measurableEquiv ι).symm
  rw [← hf.measure_preimage hs, ← (covolume_comap L volume volume hf),
    ← volume_image_eq_volume_div_covolume (ZLattice.comap ℝ L f.toLinearMap)
    (b.ofZLatticeComap ℝ L f.toLinearEquiv), Basis.ofZLatticeBasis_comap,
    ← f.image_symm_eq_preimage, ← Set.image_comp]
  simp only [Basis.equivFun_apply, ContinuousLinearEquiv.symm_toLinearEquiv, Basis.map_equivFun,
    LinearEquiv.symm_symm, Function.comp_apply, LinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.apply_symm_apply]

end Basic

namespace covolume

section General

open Filter Fintype Pointwise Topology BoxIntegral Bornology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the general case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_div_pow'' [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier ((b.ofZLatticeBasis ℝ).equivFun '' s)) = 0):
    Tendsto (fun n : ℕ ↦ (Nat.card (s ∩ (n : ℝ)⁻¹ • L : Set E) : ℝ) / n ^ card ι)
      atTop (𝓝 (volume ((b.ofZLatticeBasis ℝ).equivFun '' s)).toReal) := by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis ℝ).equivFun '' s) ?_ ?_ hs₃)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    congr
    refine Nat.card_congr <| ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.subtypeEquiv fun x ↦ ?_).symm
    simp_rw [Set.mem_inter_iff, ← b.ofZLatticeBasis_span ℝ, LinearEquiv.coe_toEquiv,
      Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, and_congr_right_iff, Set.mem_inv_smul_set_iff₀
      (mod_cast hn.ne' : (n : ℝ) ≠ 0), ← Finsupp.coe_smul, ← LinearEquiv.map_smul, SetLike.mem_coe,
      Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    exact Bornology.IsVonNBounded.image hs₁ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂

/- Start of proof attempt -/
lemma round1_tendsto_card_le_div''_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r:ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ Fintype.card ι * (F x))
    {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ Fintype.card ι} := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_setOf_eq]
  constructor
  · -- First direction: c • {x ∈ X | F x ≤ 1} ⊆ {x ∈ X | F x ≤ c ^ Fintype.card ι}
    rintro ⟨y, hy, rfl⟩
    have hy1 : y ∈ X := hy.1
    have hy2 : F y ≤ 1 := hy.2
    constructor
    · -- Show `c • y ∈ X`
      exact hX hy1 hc
    · -- Show `F (c • y) ≤ c ^ Fintype.card ι`
      have h1 : 0 ≤ c := by linarith
      have h2 : F (c • y) = c ^ Fintype.card ι * F y := hF₁ y h1
      have h3 : c ^ Fintype.card ι ≥ 0 := by positivity
      have h4 : F (c • y) ≤ c ^ Fintype.card ι := by
        rw [h2]
        have h41 : c ^ Fintype.card ι * F y ≤ c ^ Fintype.card ι * 1 := by
          nlinarith
        have h42 : c ^ Fintype.card ι * 1 = c ^ Fintype.card ι := by ring
        linarith
      linarith
  · -- Second direction: {x ∈ X | F x ≤ c ^ Fintype.card ι} ⊆ c • {x ∈ X | F x ≤ 1}
    rintro ⟨hx1, hx2⟩
    have h5 : 0 < c := hc
    have h51 : 0 < c⁻¹ := by positivity
    use c⁻¹ • x
    constructor
    · -- Show `c⁻¹ • x ∈ {x ∈ X | F x ≤ 1}`
      constructor
      · -- Show `c⁻¹ • x ∈ X`
        exact hX hx1 h51
      · -- Show `F (c⁻¹ • x) ≤ 1`
        have h6 : 0 ≤ (c⁻¹ : ℝ) := by positivity
        have h7 : F (c⁻¹ • x) = (c⁻¹ : ℝ) ^ Fintype.card ι * F x := hF₁ x h6
        have h8 : (c⁻¹ : ℝ) ^ Fintype.card ι * F x ≤ (c⁻¹ : ℝ) ^ Fintype.card ι * (c ^ Fintype.card ι) := by
          have h9 : F x ≤ c ^ Fintype.card ι := hx2
          have h10 : 0 ≤ (c⁻¹ : ℝ) ^ Fintype.card ι := by positivity
          nlinarith
        have h11 : (c⁻¹ : ℝ) ^ Fintype.card ι * (c ^ Fintype.card ι) = 1 := by
          have h12 : (c⁻¹ : ℝ) ^ Fintype.card ι * (c ^ Fintype.card ι) = ((c⁻¹ : ℝ) * c) ^ Fintype.card ι := by
            rw [mul_pow]
          rw [h12]
          have h13 : (c⁻¹ : ℝ) * c = 1 := by field_simp [h5.ne']
          rw [h13]
          norm_num
        linarith
    · -- Show `c • (c⁻¹ • x) = x`
      calc
        c • (c⁻¹ • x) = (c * c⁻¹) • x := by rw [smul_smul]
        _ = (1 : ℝ) • x := by
          field_simp [h5.ne']
          <;> ring
        _ = x := by simp

theorem tendsto_card_le_div''_aux {X : Set E} (hX : ∀ ⦃x⦄ ⦃r:ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x)) {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι}  := by

  exact round1_tendsto_card_le_div''_aux hX hF₁ hc
