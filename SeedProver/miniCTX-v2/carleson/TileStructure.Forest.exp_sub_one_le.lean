-- In carleson/Carleson/ForestOperator/PointwiseEstimate.lean

import Carleson.Forest
import Carleson.ToMathlib.HardyLittlewood
import Carleson.ToMathlib.BoundedCompactSupport
import Carleson.ToMathlib.Misc
import Carleson.Psi

open ShortVariables TileStructure
variable {X : Type*} {a : ℕ} {q : ℝ} {K : X → X → ℂ} {σ₁ σ₂ : X → ℤ} {F G : Set X}
  [MetricSpace X] [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]
  {n j j' : ℕ} {t : Forest X n} {u u₁ u₂ p : 𝔓 X} {x x' : X} {𝔖 : Set (𝔓 X)}
  {f f₁ f₂ g g₁ g₂ : X → ℂ} {I J J' L : Grid X}
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

noncomputable section

open Set MeasureTheory Metric Function Complex Bornology TileStructure Classical Filter
open scoped NNReal ENNReal ComplexConjugate

namespace TileStructure.Forest

/-! ## Section 7.1 and Lemma 7.1.3 -/

variable (t) in
/-- The definition `σ(u, x)` given in Section 7.1.
We may assume `u ∈ t` whenever proving things about this definition. -/
def σ (u : 𝔓 X) (x : X) : Finset ℤ := .image 𝔰 { p | p ∈ t u ∧ x ∈ E p }

variable (t) in
private lemma exists_p_of_mem_σ (u : 𝔓 X) (x : X) {s : ℤ} (hs : s ∈ t.σ u x) :
    ∃ p ∈ t.𝔗 u, x ∈ E p ∧ 𝔰 p = s := by
  have ⟨p, hp⟩ := Finset.mem_image.mp hs
  simp only [mem_𝔗, Finset.mem_filter] at hp
  use p, hp.1.2.1, hp.1.2.2, hp.2

/- \overline{σ} from the blueprint. -/
variable (t) in
def σMax (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : ℤ :=
  t.σ u x |>.max' hσ

/- \underline{σ} from the blueprint. -/
variable (t) in
def σMin (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : ℤ :=
  t.σ u x |>.min' hσ

variable (t) in
private lemma σMax_mem_σ (u : 𝔓 X) (x : X) (hσ : (t.σ u x).Nonempty) : σMax t u x hσ ∈ t.σ u x :=
  (t.σ u x).max'_mem hσ

/-- The definition of `𝓙₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓙₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {J : Grid X | s J = -S ∨ ∀ p ∈ 𝔖, ¬(𝓘 p : Set X) ⊆ ball (c J) (100 * D ^ (s J + 1))}

/-- The definition of `𝓙(𝔖), defined above Lemma 7.1.2 -/
def 𝓙 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓙₀ 𝔖) x}

lemma 𝓙_subset_𝓙₀ {𝔖 : Set (𝔓 X)} : 𝓙 𝔖 ⊆ 𝓙₀ 𝔖 := sep_subset ..

lemma pairwiseDisjoint_𝓙 : (𝓙 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := fun I mI J mJ hn ↦ by
  have : IsAntichain (· ≤ ·) (𝓙 𝔖) := setOf_maximal_antichain _
  exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

/-- The definition of `𝓛₀(𝔖), defined above Lemma 7.1.2 -/
def 𝓛₀ (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {L : Grid X | s L = -S ∨ (∃ p ∈ 𝔖, L ≤ 𝓘 p) ∧ ∀ p ∈ 𝔖, ¬𝓘 p ≤ L}

/-- The definition of `𝓛(𝔖), defined above Lemma 7.1.2 -/
def 𝓛 (𝔖 : Set (𝔓 X)) : Set (Grid X) :=
  {x | Maximal (· ∈ 𝓛₀ 𝔖) x}

lemma 𝓛_subset_𝓛₀ {𝔖 : Set (𝔓 X)} : 𝓛 𝔖 ⊆ 𝓛₀ 𝔖 := sep_subset ..

private lemma s_le_s_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖)
    {p : 𝔓 X} (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : s L ≤ s (𝓘 p) := by
  simp only [𝓛, 𝓛₀, Grid.le_def, not_and, not_le, and_imp] at hL
  rcases hL.1 with h | h
  · exact h ▸ (range_s_subset ⟨𝓘 p, rfl⟩).1
  · by_contra!
    exact lt_asymm this <| h.2 p hp <| (GridStructure.fundamental_dyadic' this.le).resolve_right hpL

private lemma subset_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖) {p : 𝔓 X}
    (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : (L : Set X) ⊆ (𝓘 p : Set X) :=
  GridStructure.fundamental_dyadic' (s_le_s_of_mem_𝓛 hL hp hpL) |>.resolve_right fun h ↦ hpL h.symm

/-- The projection operator `P_𝓒 f(x)`, given above Lemma 7.1.3.
In lemmas the `c` will be pairwise disjoint on `C`. -/
def approxOnCube (C : Set (Grid X)) (f : X → E') (x : X) : E' :=
  ∑ J ∈ { p | p ∈ C }, (J : Set X).indicator (fun _ ↦ ⨍ y in J, f y) x

lemma stronglyMeasurable_approxOnCube (C : Set (Grid X)) (f : X → E') :
    StronglyMeasurable (approxOnCube (X := X) (K := K) C f) :=
  Finset.stronglyMeasurable_sum _ (fun _ _ ↦ stronglyMeasurable_const.indicator coeGrid_measurable)

lemma integrable_approxOnCube (C : Set (Grid X)) {f : X → E'} : Integrable (approxOnCube C f) := by
  refine integrable_finset_sum _ (fun i hi ↦ ?_)
  constructor
  · exact (aestronglyMeasurable_indicator_iff coeGrid_measurable).mpr aestronglyMeasurable_const
  · simp_rw [hasFiniteIntegral_iff_enorm, enorm_indicator_eq_indicator_enorm]
    apply lt_of_le_of_lt <| lintegral_indicator_const_le (i : Set X) _
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top volume_coeGrid_lt_top

lemma approxOnCube_nonneg {C : Set (Grid X)} {f : X → ℝ} (hf : ∀ (y : X), f y ≥ 0) {x : X} :
    approxOnCube C f x ≥ 0 :=
  Finset.sum_nonneg' (fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ integral_nonneg hf) _)

lemma approxOnCube_apply {C : Set (Grid X)} (hC : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    (f : X → E') {x : X} {J : Grid X} (hJ : J ∈ C) (xJ : x ∈ J) :
    (approxOnCube C f) x = ⨍ y in J, f y := by
  rw [approxOnCube, ← Finset.sum_filter_not_add_sum_filter _ (J = ·)]
  have eq0 : ∑ i ∈ Finset.filter (¬ J = ·) (Finset.univ.filter (· ∈ C)),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 := by
    suffices ∀ i ∈ (Finset.univ.filter (· ∈ C)).filter (¬ J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = 0 by simp [Finset.sum_congr rfl this]
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply indicator_of_not_mem <|
      Set.disjoint_left.mp ((hC.eq_or_disjoint hJ hi.1).resolve_left hi.2) xJ
  have eq_ave : ∑ i ∈ (Finset.univ.filter (· ∈ C)).filter (J = ·),
      (i : Set X).indicator (fun _ ↦ ⨍ y in i, f y) x = ⨍ y in J, f y := by
    suffices (Finset.univ.filter (· ∈ C)).filter (J = ·) = {J} by simp [this, xJ, ← Grid.mem_def]
    exact subset_antisymm (fun _ h ↦ Finset.mem_singleton.mpr (Finset.mem_filter.mp h).2.symm)
      (fun _ h ↦ by simp [Finset.mem_singleton.mp h, hJ])
  rw [eq0, eq_ave, zero_add]

lemma boundedCompactSupport_approxOnCube {𝕜 : Type*} [RCLike 𝕜] {C : Set (Grid X)} {f : X → 𝕜} :
    BoundedCompactSupport (approxOnCube C f) :=
  BoundedCompactSupport.finset_sum fun J hJ ↦
    BoundedCompactSupport.indicator_of_isBounded_range (by simp) stronglyMeasurable_const
    ((isBounded_iff_subset_ball (c J)).mpr ⟨4 * D ^ s J, Grid_subset_ball⟩) coeGrid_measurable

-- Used in the proof of Lemma 7.1.6
lemma integral_eq_lintegral_approxOnCube {C : Set (Grid X)}
    (hC : C.PairwiseDisjoint fun I ↦ (I : Set X)) {J : Grid X} (hJ : J ∈ C) {f : X → ℂ}
    (hf : BoundedCompactSupport f) : ENNReal.ofReal (∫ y in J, ‖f y‖) =
    ∫⁻ (y : X) in J, ‖approxOnCube C (fun x ↦ (‖f x‖ : ℂ)) y‖₊ := by
  have nonneg : 0 ≤ᶠ[ae (volume.restrict J)] fun y ↦ ‖f y‖ := Filter.Eventually.of_forall (by simp)
  have vol_J_ne_zero := (volume_coeGrid_pos (X := X) (i := J) (defaultD_pos' a)).ne.symm
  have eq : ∫⁻ (y : X) in J, ‖approxOnCube C (fun x ↦ (‖f x‖ : ℂ)) y‖₊ =
      ∫⁻ y in (J : Set X), ENNReal.ofReal (⨍ z in J, ‖f z‖) := by
    refine setLIntegral_congr_fun coeGrid_measurable (Filter.Eventually.of_forall fun y hy ↦ ?_)
    rw [approxOnCube_apply hC _ hJ hy, ENNReal.ofReal]
    · apply congrArg
      have : ‖⨍ y in J, (‖f y‖ : ℂ)‖₊ = ‖⨍ y in J, ‖f y‖‖₊ := by
        convert congrArg (‖·‖₊) <| integral_ofReal (f := (‖f ·‖)) using 1
        simp [average]
      exact this ▸ (Real.toNNReal_eq_nnnorm_of_nonneg <| integral_nonneg (fun y ↦ by simp)).symm
  rw [ofReal_integral_eq_lintegral_ofReal hf.integrable.norm.restrict nonneg,
    eq, lintegral_const, average_eq, smul_eq_mul, ENNReal.ofReal_mul, ENNReal.ofReal_inv_of_pos,
    ENNReal.ofReal_toReal, ofReal_integral_eq_lintegral_ofReal hf.norm.integrable nonneg, mul_comm,
    ← mul_assoc, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    ENNReal.mul_inv_cancel vol_J_ne_zero volume_coeGrid_lt_top.ne, one_mul]
  · simp [volume_coeGrid_lt_top.ne]
  · simpa using ENNReal.toReal_pos vol_J_ne_zero volume_coeGrid_lt_top.ne
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg

lemma approxOnCube_ofReal (C : Set (Grid X)) (f : X → ℝ) (x : X) :
    approxOnCube C (Complex.ofReal <| f ·) x = Complex.ofReal (approxOnCube C f x) := by
  simp_rw [approxOnCube, ofReal_sum]
  refine Finset.sum_congr rfl (fun J _ ↦ ?_)
  by_cases hx : x ∈ (J : Set X)
  · simpa only [indicator_of_mem hx] using integral_ofReal
  · simp only [indicator_of_not_mem hx, ofReal_zero]

lemma norm_approxOnCube_le_approxOnCube_norm {C : Set (Grid X)} {f : X → E'} {x : X} :
    ‖approxOnCube C f x‖ ≤ approxOnCube C (‖f ·‖) x := by
  refine (norm_sum_le _ _).trans <| Finset.sum_le_sum (fun J hJ ↦ ?_)
  rw [norm_indicator_eq_indicator_norm]
  gcongr
  apply norm_integral_le_integral_norm

/-- The definition `I_i(x)`, given above Lemma 7.1.3.
The cube of scale `s` that contains `x`. There is at most 1 such cube, if it exists. -/
def cubeOf (i : ℤ) (x : X) : Grid X :=
  Classical.epsilon (fun I ↦ x ∈ I ∧ s I = i)

lemma cubeOf_spec {i : ℤ} (hi : i ∈ Icc (-S : ℤ) S) (I : Grid X) {x : X} (hx : x ∈ I) :
    x ∈ cubeOf i x ∧ s (cubeOf i x) = i := by
  apply epsilon_spec (p := fun I ↦ x ∈ I ∧ s I = i)
  by_cases hiS : i = S
  · use topCube, subset_topCube hx, hiS ▸ s_topCube
  simpa [and_comm] using Set.mem_iUnion₂.mp <| Grid_subset_biUnion i
    ⟨hi.1, s_topCube (X := X) ▸ lt_of_le_of_ne hi.2 hiS⟩ (subset_topCube hx)

/-- The definition `T_𝓝^θ f(x)`, given in (7.1.3).
For convenience, the suprema are written a bit differently than in the blueprint
(avoiding `cubeOf`), but this should be equivalent.
This is `0` if `x` doesn't lie in a cube. -/
def nontangentialMaximalFunction (θ : Θ X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ⨆ (I : Grid X) (_ : x ∈ I) (x' ∈ I) (s₂ ∈ Icc (s I) S)
  (_ : ENNReal.ofReal (D ^ (s₂ - 1)) ≤ upperRadius Q θ x'),
  ‖∑ i ∈ Icc (s I) s₂, ∫ y, Ks i x' y * f y‖₊

protected theorem MeasureTheory.Measurable.nontangentialMaximalFunction {θ : Θ X} {f : X → ℂ} :
    Measurable (nontangentialMaximalFunction θ f) := by
  refine Measurable.iSup (fun I ↦ ?_)
  let c := ⨆ x' ∈ I, ⨆ s₂ ∈ Icc (s I) S, ⨆ (_ : ENNReal.ofReal (D ^ (s₂ - 1)) ≤ upperRadius Q θ x'),
    (‖∑ i ∈ (Icc (s I) s₂), ∫ (y : X), Ks i x' y * f y‖₊ : ENNReal)
  have : (fun x ↦ ⨆ (_ : x ∈ I), c) = fun x ↦ ite (x ∈ I) c 0 := by
    ext x; by_cases hx : x ∈ I <;> simp [hx]
  convert (measurable_const.ite coeGrid_measurable measurable_const) using 1

-- Set used in definition of `boundaryOperator`
variable (t) (u) in private def 𝓙' (x : X) (i : ℤ) : Finset (Grid X) :=
  { J | J ∈ 𝓙 (t u) ∧ (J : Set X) ⊆ ball x (16 * D ^ i) ∧ s J ≤ i }

private lemma mem_𝓙_of_mem_𝓙' {x : X} {i : ℤ} {J : Grid X} : J ∈ 𝓙' t u x i → J ∈ 𝓙 (t u) := by
  intro hJ
  simp only [𝓙', Finset.mem_filter] at hJ
  exact hJ.2.1

variable (t) in
/-- The operator `S_{1,𝔲} f(x)`, given in (7.1.4). -/
def boundaryOperator (u : 𝔓 X) (f : X → ℂ) (x : X) : ℝ≥0∞ :=
  ∑ I : Grid X, (I : Set X).indicator (x := x) fun _ ↦ ∑ J ∈ 𝓙' t u (c I) (s I),
  D ^ ((s J - s I) / (a : ℝ)) / volume (ball (c I) (16 * D ^ (s I))) * ∫⁻ y in (J : Set X), ‖f y‖₊

protected theorem MeasureTheory.Measurable.boundaryOperator {u : 𝔓 X} {f : X → ℂ} :
    Measurable (t.boundaryOperator u f) := by
  refine Finset.measurable_sum _ (fun I _ ↦ ?_)
  exact (Finset.measurable_sum _ (fun J _ ↦ measurable_const)).indicator coeGrid_measurable

-- Currently unused; uncomment if needed.
/- lemma boundaryOperator_lt_top (hf : BoundedCompactSupport f) : t.boundaryOperator u f x < ⊤ := by
  refine ENNReal.sum_lt_top.mpr (fun I _ ↦ ?_)
  by_cases hx : x ∈ (I : Set X)
  · rw [indicator_of_mem hx]
    refine ENNReal.sum_lt_top.mpr (fun J hJ ↦ ENNReal.mul_lt_top ?_ hf.integrable.integrableOn.2)
    apply ENNReal.div_lt_top (by simp)
    exact ne_of_gt <| measure_ball_pos volume _ <| mul_pos (by norm_num) (defaultD_pow_pos a (s I))
  · simp [hx] -/

/-- The indexing set for the collection of balls 𝓑, defined above Lemma 7.1.3. -/
def 𝓑 : Set (ℕ × Grid X) := Icc 0 (S + 5) ×ˢ univ

/-- The center function for the collection of balls 𝓑. -/
def c𝓑 (z : ℕ × Grid X) : X := c z.2

/-- The radius function for the collection of balls 𝓑. -/
def r𝓑 (z : ℕ × Grid X) : ℝ := 2 ^ z.1 * D ^ s z.2

lemma 𝓑_finite : (𝓑 (X := X)).Finite :=
  finite_Icc .. |>.prod finite_univ

/-- Lemma 7.1.1, freely translated. -/
lemma convex_scales (hu : u ∈ t) : OrdConnected (t.σ u x : Set ℤ) := by
  rw [ordConnected_def]; intro i mi j mj k mk
  simp_rw [Finset.mem_coe, σ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and] at mi mj ⊢
  obtain ⟨p, ⟨mp, xp, Qxp, sxp⟩, sp⟩ := mi
  obtain ⟨p'', ⟨mp'', xp'', Qxp'', sxp''⟩, sp''⟩ := mj
  have ilj : i ≤ j := nonempty_Icc.mp ⟨k, mk⟩
  rw [← sp, ← sp''] at ilj mk
  obtain ⟨K, sK, lK, Kl⟩ := Grid.exists_sandwiched (le_of_mem_of_mem ilj xp xp'') k mk
  have := range_subset_iff.mp (biUnion_Ω (i := K)) x
  simp_rw [mem_preimage, mem_singleton_iff, mem_iUnion, exists_prop] at this
  obtain ⟨(p' : 𝔓 X), (𝓘p' : 𝓘 p' = K), Qxp'⟩ := this
  rw [← 𝓘p'] at lK Kl sK; refine ⟨p', ?_, sK⟩
  have l₁ : p ≤ p' := ⟨lK,
    (relative_fundamental_dyadic lK).resolve_left (not_disjoint_iff.mpr ⟨_, Qxp, Qxp'⟩)⟩
  have l₂ : p' ≤ p'' := ⟨Kl,
    (relative_fundamental_dyadic Kl).resolve_left (not_disjoint_iff.mpr ⟨_, Qxp', Qxp''⟩)⟩
  refine ⟨(t.ordConnected hu).out mp mp'' ⟨l₁, l₂⟩, ⟨(Grid.le_def.mp lK).1 xp, Qxp', ?_⟩⟩
  exact Icc_subset_Icc sxp.1 sxp''.2 ⟨(Grid.le_def.mp lK).2, (Grid.le_def.mp Kl).2⟩

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓙 : ⋃ J ∈ 𝓙 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  refine subset_antisymm (iUnion₂_subset_iUnion ..) fun x mx ↦ ?_
  simp_rw [mem_iUnion] at mx ⊢; obtain ⟨I, mI⟩ := mx
  obtain ⟨J, sJ, mJ⟩ :=
    Grid.exists_containing_subcube _ ⟨le_rfl, scale_mem_Icc.1⟩ mI
  have : J ∈ (𝓙₀ 𝔖).toFinset := by rw [mem_toFinset]; left; exact sJ
  obtain ⟨M, lM, maxM⟩ := (𝓙₀ 𝔖).toFinset.exists_le_maximal this
  simp_rw [mem_toFinset] at maxM
  use M, maxM, (Grid.le_def.mp lM).1 mJ

/-- Part of Lemma 7.1.2 -/
@[simp]
lemma biUnion_𝓛 : ⋃ J ∈ 𝓛 𝔖, J = ⋃ I : Grid X, (I : Set X) := by
  refine subset_antisymm (iUnion₂_subset_iUnion ..) fun x mx ↦ ?_
  simp_rw [mem_iUnion] at mx ⊢; obtain ⟨I, mI⟩ := mx
  obtain ⟨J, sJ, mJ⟩ :=
    Grid.exists_containing_subcube _ ⟨le_rfl, scale_mem_Icc.1⟩ mI
  have : J ∈ (𝓛₀ 𝔖).toFinset := by rw [mem_toFinset]; left; exact sJ
  obtain ⟨M, lM, maxM⟩ := (𝓛₀ 𝔖).toFinset.exists_le_maximal this
  simp_rw [mem_toFinset] at maxM
  use M, maxM, (Grid.le_def.mp lM).1 mJ

/-- Part of Lemma 7.1.2 -/
lemma pairwiseDisjoint_𝓛 : (𝓛 𝔖).PairwiseDisjoint (fun I ↦ (I : Set X)) := fun I mI J mJ hn ↦ by
  have : IsAntichain (· ≤ ·) (𝓛 𝔖) := setOf_maximal_antichain _
  exact (le_or_ge_or_disjoint.resolve_left (this mI mJ hn)).resolve_left (this mJ mI hn.symm)

/-- The constant used in `first_tree_pointwise`.
Has value `10 * 2 ^ (104 * a ^ 3)` in the blueprint. -/
-- Todo: define this recursively in terms of previous constants
irreducible_def C7_1_4 (a : ℕ) : ℝ≥0 := 10 * 2 ^ (104 * (a : ℝ) ^ 3)

-- Used in the proof of `exp_sub_one_le`, which is used to prove Lemma 7.1.4
private lemma exp_Lipschitz : LipschitzWith 1 (fun (t : ℝ) ↦ exp (.I * t)) := by
  have mul_I : Differentiable ℝ fun (t : ℝ) ↦ I * t := Complex.ofRealCLM.differentiable.const_mul I
  refine lipschitzWith_of_nnnorm_deriv_le mul_I.cexp (fun x ↦ ?_)
  have : (fun (t : ℝ) ↦ cexp (I * t)) = cexp ∘ (fun (t : ℝ) ↦ I * t) := rfl
  rw [this, deriv_comp x differentiableAt_exp (mul_I x), Complex.deriv_exp, deriv_const_mul_field']
  simp_rw [show deriv ofReal x = 1 from ofRealCLM.hasDerivAt.deriv, mul_one]
  rw [nnnorm_mul, nnnorm_I, mul_one, ← norm_toNNReal, mul_comm, Complex.norm_exp_ofReal_mul_I]
  exact Real.toNNReal_one.le

-- Used in the proof of Lemma 7.1.4

/- Start of proof attempt -/
lemma round1_exp_sub_one_le (t : ℝ) : ‖Complex.exp (.I * t) - 1‖ ≤ ‖t‖ := by
  have h1 : dist (Complex.exp (.I * t)) (Complex.exp (.I * (0 : ℝ))) ≤ dist t (0 : ℝ) := by
    have h11 := exp_Lipschitz.dist_le_mul t (0 : ℝ)
    norm_num at h11 ⊢
    <;> linarith
  have h2 : Complex.exp (.I * (0 : ℝ)) = (1 : ℂ) := by
    simp [Complex.exp_zero]
  have h3 : dist (Complex.exp (.I * t)) (Complex.exp (.I * (0 : ℝ))) = ‖Complex.exp (.I * t) - 1‖ := by
    rw [h2]
    simp [Complex.dist_eq]
  have h4 : dist t (0 : ℝ) = |t| := by
    simp [Real.dist_eq]
  have h5 : ‖(t : ℝ)‖ = |t| := by
    simp [Real.norm_eq_abs]
  have h6 : ‖Complex.exp (.I * t) - 1‖ ≤ |t| := by
    linarith [h1, h3, h4]
  have h7 : ‖(t : ℝ)‖ = |t| := by
    simp [Real.norm_eq_abs]
  have h8 : ‖Complex.exp (.I * t) - 1‖ ≤ ‖(t : ℝ)‖ := by
    linarith [h6, h7]
  simpa using h8

theorem exp_sub_one_le (t : ℝ) : ‖exp (.I * t) - 1‖ ≤ ‖t‖  := by

  exact round1_exp_sub_one_le t
