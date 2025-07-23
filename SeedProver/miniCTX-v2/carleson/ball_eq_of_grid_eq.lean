-- In carleson/Carleson/TileStructure.lean

import Carleson.GridStructure
import Carleson.Psi
import Carleson.ToMathlib.BoundedCompactSupport

open Set MeasureTheory Metric Function Complex Bornology
open scoped NNReal ENNReal ComplexConjugate
noncomputable section

section Generic
universe u
variable {𝕜 : Type*} [_root_.RCLike 𝕜]
variable {X : Type u} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

/- The data in a tile structure, and some basic properties.
This is mostly separated out so that we can nicely define the notation `d_𝔭`.
Note: compose `𝓘` with `Grid` to get the `𝓘` of the paper. -/
class PreTileStructure {A : outParam ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
  [FunctionDistances 𝕜 X] (Q : outParam (SimpleFunc X (Θ X)))
  (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X)
  extends GridStructure X D κ S o where
  protected 𝔓 : Type u
  fintype_𝔓 : Fintype 𝔓
  protected 𝓘 : 𝔓 → Grid
  surjective_𝓘 : Surjective 𝓘
  𝒬 : 𝔓 → Θ X
  range_𝒬 : range 𝒬 ⊆ range Q

export PreTileStructure (𝒬 range_𝒬)

variable {D : ℕ} {κ : ℝ} {S : ℕ} {o : X}
variable [FunctionDistances 𝕜 X]  {Q : SimpleFunc X (Θ X)} [PreTileStructure Q D κ S o]

variable (X) in
def 𝔓 := PreTileStructure.𝔓 𝕜 X
instance : Fintype (𝔓 X) := PreTileStructure.fintype_𝔓
def 𝓘 : 𝔓 X → Grid X := PreTileStructure.𝓘
lemma surjective_𝓘 : Surjective (𝓘 : 𝔓 X → Grid X) := PreTileStructure.surjective_𝓘
instance : Inhabited (𝔓 X) := ⟨(surjective_𝓘 default).choose⟩
def 𝔠 (p : 𝔓 X) : X := c (𝓘 p)
def 𝔰 (p : 𝔓 X) : ℤ := s (𝓘 p)

local notation "ball_(" D "," 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

/-- A tile structure. -/
-- note: we don't explicitly include injectivity of `Ω` on `𝔓(I)`, since it follows from these
-- axioms: see `toTileLike_injective`
class TileStructure {A : outParam ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
    [FunctionDistances ℝ X] (Q : outParam (SimpleFunc X (Θ X)))
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X)
    extends PreTileStructure Q D κ S o where
  Ω : 𝔓 → Set (Θ X)
  biUnion_Ω {i} : range Q ⊆ ⋃ p ∈ 𝓘 ⁻¹' {i}, Ω p -- 2.0.13, union contains `Q`
  disjoint_Ω {p p'} (h : p ≠ p') (hp : 𝓘 p = 𝓘 p') : -- 2.0.13, union is disjoint
    Disjoint (Ω p) (Ω p')
  relative_fundamental_dyadic {p p'} (h : 𝓘 p ≤ 𝓘 p') : -- 2.0.14
    Disjoint (Ω p) (Ω p') ∨ Ω p' ⊆ Ω p
  cball_subset {p} : ball_(D, p) (𝒬 p) 5⁻¹ ⊆ Ω p -- 2.0.15, first inclusion
  subset_cball {p} : Ω p ⊆ ball_(D, p) (𝒬 p) 1 -- 2.0.15, second inclusion

export TileStructure (Ω biUnion_Ω disjoint_Ω relative_fundamental_dyadic)

end Generic

open scoped ShortVariables
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]

section

variable [TileStructure Q D κ S o] {p p' : 𝔓 X} {f g : Θ X}

-- maybe we should delete the following three notations, and use `dist_{𝓘 p}` instead?
notation "dist_(" 𝔭 ")" => @dist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "nndist_(" 𝔭 ")" => @nndist (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _
notation "ball_(" 𝔭 ")" => @ball (WithFunctionDistance (𝔠 𝔭) (D ^ 𝔰 𝔭 / 4)) _

@[simp] lemma dist_𝓘 (p : 𝔓 X) : dist_{𝓘 p} f g = dist_(p) f g := rfl
@[simp] lemma nndist_𝓘 (p : 𝔓 X) : nndist_{𝓘 p} f g = nndist_(p) f g := rfl
@[simp] lemma ball_𝓘 (p : 𝔓 X) {r : ℝ} : ball_{𝓘 p} f r = ball_(p) f r := rfl

@[simp] lemma cball_subset {p : 𝔓 X} : ball_(p) (𝒬 p) 5⁻¹ ⊆ Ω p := TileStructure.cball_subset
@[simp] lemma subset_cball {p : 𝔓 X} : Ω p ⊆ ball_(p) (𝒬 p) 1 := TileStructure.subset_cball

/- Start of proof attempt -/
lemma round1_h1 (p q : 𝔓 X) (ϑ : Θ X) (r : ℝ):
  ball_(p) ϑ r = ball_{𝓘 p} ϑ r := by
  simp [ball_𝓘]

lemma round1_h2 (p q : 𝔓 X) (ϑ : Θ X) (r : ℝ):
  ball_{𝓘 q} ϑ r = ball_(q) ϑ r := by
  simp [ball_𝓘]

lemma round1_h3 (p q : 𝔓 X) (h : 𝓘 p = 𝓘 q) (ϑ : Θ X) (r : ℝ):
  ball_{𝓘 p} ϑ r = ball_{𝓘 q} ϑ r := by
  rw [h]

theorem ball_eq_of_grid_eq {p q : 𝔓 X} {ϑ : Θ X} {r : ℝ} (h : 𝓘 p = 𝓘 q) :
    ball_(p) ϑ r = ball_(q) ϑ r  := by

  have h1 := round1_h1 p q ϑ r
  have h2 := round1_h2 p q ϑ r
  have h3 := round1_h3 p q h ϑ r
  rw [h1, h3, h2]
  <;> rfl
