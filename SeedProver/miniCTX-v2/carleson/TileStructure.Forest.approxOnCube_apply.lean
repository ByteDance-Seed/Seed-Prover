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

/- Start of proof attempt -/
lemma round1_h1 (C : Set (Grid X))
  (hC : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
  (J : Grid X)
  (hJ : J ∈ C)
  (x : X)
  (xJ : x ∈ J):
  ∀ (J' : Grid X), J' ∈ C → J' ≠ J → x ∉ (J' : Set X) := by
  intro J' hJ' hne
  have h2 : Disjoint (J : Set X) (J' : Set X) := hC hJ hJ' (Ne.symm hne)
  by_contra h3
  have h4 : x ∈ (J : Set X) ∩ (J' : Set X) := ⟨xJ, h3⟩
  have h5 : (J : Set X) ∩ (J' : Set X) = ∅ := by simpa [Set.disjoint_iff] using h2
  rw [h5] at h4
  contradiction

lemma round1_h6 (C : Set (Grid X))
  (f : X → E')
  (x : X)
  (J : Grid X)
  (h1 : ∀ (J' : Grid X), J' ∈ C → J' ≠ J → x ∉ (J' : Set X)):
  ∀ (J' : Grid X), J' ∈ C → J' ≠ J → ((J' : Set X).indicator (fun _x ↦ ⨍ y in J', f y) x) = 0 := by
  intro J' hJ' hne
  have h7 : x ∉ (J' : Set X) := h1 J' hJ' hne
  simp [Set.indicator_apply, h7]
  <;> aesop

lemma round1_h9 (C : Set (Grid X))
  (f : X → E')
  (x : X)
  (J : Grid X)
  (xJ : x ∈ J):
  ((J : Set X).indicator (fun _x ↦ ⨍ y in J, f y) x) = ⨍ y in J, f y := by
  simp [Set.indicator_apply, xJ]
  <;> aesop

theorem approxOnCube_apply {C : Set (Grid X)} (hC : C.PairwiseDisjoint (fun I ↦ (I : Set X)))
    (f : X → E') {x : X} {J : Grid X} (hJ : J ∈ C) (xJ : x ∈ J) :
    (approxOnCube C f) x = ⨍ y in J, f y  := by

  have h1 : ∀ (J' : Grid X), J' ∈ C → J' ≠ J → x ∉ (J' : Set X) := by
    exact round1_h1 C hC J hJ x xJ

  have h6 : ∀ (J' : Grid X), J' ∈ C → J' ≠ J → ((J' : Set X).indicator (fun _x ↦ ⨍ y in J', f y) x) = 0 := by
    exact round1_h6 C f x J h1

  have h9 : ((J : Set X).indicator (fun _x ↦ ⨍ y in J, f y) x) = ⨍ y in J, f y := by
    exact round1_h9 C f x J xJ

  have h101 : Finset.filter (fun p => p ∈ C) Finset.univ = C.toFinset := by
    ext p
    simp

  have h10 : (approxOnCube C f) x = ∑ J' in C.toFinset, (J' : Set X).indicator (fun _x ↦ ⨍ y in J', f y) x := by
    have h102 : (approxOnCube C f) x = ∑ J' in Finset.filter (fun p => p ∈ C) Finset.univ, (J' : Set X).indicator (fun _x ↦ ⨍ y in J', f y) x := rfl
    rw [h102]
    rw [h101]

  have h11 : ∀ J' ∈ C.toFinset, J' ≠ J → ((J' : Set X).indicator (fun _x ↦ ⨍ y in J', f y) x) = 0 := by
    intro J' hJ' hne
    have h12 : J' ∈ C := by simpa using hJ'
    exact h6 J' h12 hne

  have h13 : J ∈ C.toFinset := by simpa using hJ

  have h14 : ∑ J' in C.toFinset, (J' : Set X).indicator (fun _x ↦ ⨍ y in J', f y) x = ((J : Set X).indicator (fun _x ↦ ⨍ y in J, f y) x) := by
    apply Finset.sum_eq_single_of_mem
    · exact h13
    · intro J' hJ' hne
      exact h11 J' hJ' hne

  rw [h10, h14, h9]
