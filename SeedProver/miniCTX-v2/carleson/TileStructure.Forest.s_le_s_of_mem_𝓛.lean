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

/- Start of proof attempt -/
lemma round1_h_fundamental :
  ∀ (i j : Grid X), s i ≤ s j → (i : Set X) ⊆ j ∨ Disjoint (i : Set X) (j : Set X) := by
  have h : ∀ (gs : GridStructure X (defaultD a) (defaultκ a) (defaultS X) (cancelPt X)), ∀ (i j : Grid X), s i ≤ s j → (i : Set X) ⊆ j ∨ Disjoint (i : Set X) (j : Set X) := by
    intro gs
    induction gs using GridStructure.recOn with
    | mk Grid fintype_Grid coeGrid s c inj range_s_subset topCube s_topCube c_topCube subset_topCube Grid_subset_biUnion fundamental_dyadic' ball_subset_Grid Grid_subset_ball small_boundary coeGrid_measurable =>
      intros i j h1
      exact fundamental_dyadic' h1
  exact h (inferInstance)

lemma round1_h_range_s :
  ∀ (g : Grid X), s g ∈ Set.Icc (-S : ℤ) (S : ℤ) := by
  intro g
  have h2 : Set.range (s : Grid X → ℤ) ⊆ Set.Icc (-S : ℤ) (S : ℤ) := range_s_subset
  have h4 : s g ∈ Set.range (s : Grid X → ℤ) := by
    refine' ⟨g, rfl⟩
  exact h2 h4

theorem s_le_s_of_mem_𝓛 {𝔖 : Set (𝔓 X)} {L : Grid X} (hL : L ∈ 𝓛 𝔖)
    {p : 𝔓 X} (hp : p ∈ 𝔖) (hpL : ¬ Disjoint (𝓘 p : Set X) (L : Set X)) : s L ≤ s (𝓘 p)  := by

  have h_fundamental : ∀ (i j : Grid X), s i ≤ s j → (i : Set X) ⊆ j ∨ Disjoint (i : Set X) (j : Set X) := by
    exact round1_h_fundamental
  have h_range_s : ∀ (g : Grid X), s g ∈ Set.Icc (-S : ℤ) (S : ℤ) := by
    exact round1_h_range_s
  by_cases h : s L ≤ s (𝓘 p)
  · -- Case 1: s L ≤ s (𝓘 p)
    linarith
  · -- Case 2: ¬(s L ≤ s (𝓘 p))
    have h1 : s (𝓘 p) < s L := by linarith
    have h2 : s (𝓘 p) ≤ s L := by linarith
    have h3 : (𝓘 p : Set X) ⊆ (L : Set X) ∨ Disjoint (𝓘 p : Set X) (L : Set X) := h_fundamental (𝓘 p) L h2
    have h4 : (𝓘 p : Set X) ⊆ (L : Set X) := by
      cases h3 with
      | inl h31 =>
        exact h31
      | inr h32 =>
        exfalso
        exact hpL h32
    have h5 : 𝓘 p ≤ L := by
      constructor
      · exact h4
      · exact h2
    have h6 : L ∈ 𝓛₀ 𝔖 := 𝓛_subset_𝓛₀ hL
    have h7 : s L = -S ∨ (∃ p' ∈ 𝔖, L ≤ 𝓘 p') ∧ ∀ p' ∈ 𝔖, ¬ 𝓘 p' ≤ L := by
      simpa [𝓛₀] using h6
    cases h7 with
    | inl h71 =>
      -- Case 1: s L = -S
      have h711 : s L = -S := h71
      have h9 : s (𝓘 p) ∈ Set.Icc (-S : ℤ) (S : ℤ) := h_range_s (𝓘 p)
      have h10 : -S ≤ s (𝓘 p) := h9.1
      linarith
    | inr h72 =>
      -- Case 2: (∃ p' ∈ 𝔖, L ≤ 𝓘 p') ∧ ∀ p' ∈ 𝔖, ¬ 𝓘 p' ≤ L
      have h722 : ∀ p' ∈ 𝔖, ¬ 𝓘 p' ≤ L := h72.2
      have h723 : ¬ 𝓘 p ≤ L := h722 p hp
      contradiction
