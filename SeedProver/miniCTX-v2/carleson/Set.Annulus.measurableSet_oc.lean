-- In carleson/Carleson/ToMathlib/Annulus.lean

/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Annulus

In this file we define an annulus in a pseudometric space `X` to be a set consisting of all `y`
such that `dist x y` lies in an interval between `r` and `R`. An annulus is defined for each type
of interval (`Ioo`, `Ioc`, etc.) with a parallel naming scheme, except that we do not define annuli
for `Iio` and `Ico`, as they would be balls.

We also define `EAnnulus` similarly using `edist` instead of `dist`.

## Tags

annulus, eannulus
-/

open Set Metric ENNReal

variable {X : Type*} [PseudoMetricSpace X]

namespace Set

namespace Annulus

def oo (x : X) (r R : ℝ) := {y | dist x y ∈ Ioo r R}
def oc (x : X) (r R : ℝ) := {y | dist x y ∈ Ioc r R}
def co (x : X) (r R : ℝ) := {y | dist x y ∈ Ico r R}
def cc (x : X) (r R : ℝ) := {y | dist x y ∈ Icc r R}
def oi (x : X) (r : ℝ) := {y | dist x y ∈ Ioi r}
def ci (x : X) (r : ℝ) := {y | dist x y ∈ Ici r}

lemma oo_eq {x : X} {r R : ℝ} : oo x r R = ball x R ∩ (closedBall x r)ᶜ := by
  ext; simp [oo, dist_comm, and_comm]

lemma oc_eq {x : X} {r R : ℝ} : oc x r R = closedBall x R ∩ (closedBall x r)ᶜ := by
  ext; simp [oc, dist_comm, and_comm]

lemma co_eq {x : X} {r R : ℝ} : co x r R = ball x R ∩ (ball x r)ᶜ := by
  ext; simp [co, dist_comm, and_comm]

lemma cc_eq {x : X} {r R : ℝ} : cc x r R = closedBall x R ∩ (ball x r)ᶜ := by
  ext; simp [cc, dist_comm, and_comm]

lemma oi_eq {x : X} {r : ℝ} : oi x r = (closedBall x r)ᶜ := by
  ext; simp [oi, dist_comm]

lemma ci_eq {x : X} {r : ℝ} : ci x r = (ball x r)ᶜ := by
  ext; simp [ci, dist_comm]

@[simp]
lemma oo_eq_empty {x : X} {r R : ℝ} (h : r ≥ R) : oo x r R = ∅ := by
  simp [oo, Ioo_eq_empty_of_le h]

@[simp]
lemma oc_eq_empty {x : X} {r R : ℝ} (h : r ≥ R) : oc x r R = ∅ := by
  simp [oc, Ioc_eq_empty_of_le h]

@[simp]
lemma co_eq_empty {x : X} {r R : ℝ} (h : r ≥ R) : co x r R = ∅ := by
  simp [co, Ico_eq_empty_of_le h]

@[simp]
lemma cc_eq_empty {x : X} {r R : ℝ} (h : r > R) : cc x r R = ∅ := by
  simp [cc, Icc_eq_empty_of_lt h]

lemma oo_subset_oo {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    oo x r₁ R₁ ⊆ oo x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_le_of_lt hr hr₁, lt_of_lt_of_le hR₁ hR⟩

lemma oo_subset_oc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    oo x r₁ R₁ ⊆ oc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_le_of_lt hr hr₁, hR₁.le.trans hR⟩

lemma oo_subset_co {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    oo x r₁ R₁ ⊆ co x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁.le, lt_of_lt_of_le hR₁ hR⟩

lemma oo_subset_cc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    oo x r₁ R₁ ⊆ cc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁.le, hR₁.le.trans hR⟩

lemma oo_subset_oi {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ ≤ r₁) : oo x r₁ R₁ ⊆ oi x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ lt_of_le_of_lt hr hr₁

lemma oo_subset_ci {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ ≤ r₁) : oo x r₁ R₁ ⊆ ci x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ hr.trans hr₁.le

lemma oc_subset_oo {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ < R₂) :
    oc x r₁ R₁ ⊆ oo x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_le_of_lt hr hr₁, lt_of_le_of_lt hR₁ hR⟩

lemma oc_subset_oc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    oc x r₁ R₁ ⊆ oc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_le_of_lt hr hr₁, hR₁.trans hR⟩

lemma oc_subset_co {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ < R₂) :
    oc x r₁ R₁ ⊆ co x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁.le, lt_of_le_of_lt hR₁ hR⟩

lemma oc_subset_cc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    oc x r₁ R₁ ⊆ cc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨(lt_of_le_of_lt hr hr₁).le, hR₁.trans hR⟩

lemma oc_subset_oi {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ ≤ r₁) : oo x r₁ R₁ ⊆ oi x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ lt_of_le_of_lt hr hr₁

lemma oc_subset_ci {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ ≤ r₁) : oc x r₁ R₁ ⊆ ci x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ hr.trans hr₁.le

lemma co_subset_oo {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ < r₁) (hR : R₁ ≤ R₂) :
    co x r₁ R₁ ⊆ oo x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_lt_of_le hr hr₁, lt_of_lt_of_le hR₁ hR⟩

lemma co_subset_oc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ < r₁) (hR : R₁ ≤ R₂) :
    co x r₁ R₁ ⊆ oc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_lt_of_le hr hr₁, hR₁.le.trans hR⟩

lemma co_subset_co {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    co x r₁ R₁ ⊆ co x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁, lt_of_lt_of_le hR₁ hR⟩

lemma co_subset_cc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    co x r₁ R₁ ⊆ cc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁, hR₁.le.trans hR⟩

lemma co_subset_oi {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ < r₁) : co x r₁ R₁ ⊆ oi x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ lt_of_lt_of_le hr hr₁

lemma co_subset_ci {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ ≤ r₁) : co x r₁ R₁ ⊆ ci x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ hr.trans hr₁

lemma cc_subset_oo {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ < r₁) (hR : R₁ < R₂) :
    cc x r₁ R₁ ⊆ oo x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_lt_of_le hr hr₁, lt_of_le_of_lt hR₁ hR⟩

lemma cc_subset_oc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ < r₁) (hR : R₁ ≤ R₂) :
    cc x r₁ R₁ ⊆ oc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨lt_of_lt_of_le hr hr₁, hR₁.trans hR⟩

lemma cc_subset_co {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ < R₂) :
    cc x r₁ R₁ ⊆ co x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁, lt_of_le_of_lt hR₁ hR⟩

lemma cc_subset_cc {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    cc x r₁ R₁ ⊆ cc x r₂ R₂ :=
  fun _ ⟨hr₁, hR₁⟩ ↦ ⟨hr.trans hr₁, hR₁.trans hR⟩

lemma cc_subset_oi {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ < r₁) : cc x r₁ R₁ ⊆ oi x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ lt_of_lt_of_le hr hr₁

lemma cc_subset_ci {x : X} {r₁ R₁ r₂ : ℝ} (hr : r₂ ≤ r₁) : cc x r₁ R₁ ⊆ ci x r₂ :=
  fun _ ⟨hr₁, _⟩ ↦ hr.trans hr₁

@[simp]
lemma oc_union_oo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    oc x r r' ∪ oo x r' R = oo x r R := by
  ext; simp_rw [oc, oo, mem_union, mem_setOf_eq, ← mem_union, Ioc_union_Ioo_eq_Ioo h₁ h₂]

@[simp]
lemma oc_union_oc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    oc x r r' ∪ oc x r' R = oc x r R := by
  ext; simp_rw [oc, mem_union, mem_setOf_eq, ← mem_union, Ioc_union_Ioc_eq_Ioc h₁ h₂]

@[simp]
lemma oo_union_co {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    oo x r r' ∪ co x r' R = oo x r R := by
  ext; simp_rw [oo, co, mem_union, mem_setOf_eq, ← mem_union, Ioo_union_Ico_eq_Ioo h₁ h₂]

@[simp]
lemma oo_union_cc {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    oo x r r' ∪ cc x r' R = oc x r R := by
  ext; simp_rw [oo, cc, oc, mem_union, mem_setOf_eq, ← mem_union, Ioo_union_Icc_eq_Ioc h₁ h₂]

@[simp]
lemma cc_union_oo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    cc x r r' ∪ oo x r' R = co x r R := by
  ext; simp_rw [cc, oo, co, mem_union, mem_setOf_eq, ← mem_union, Icc_union_Ioo_eq_Ico h₁ h₂]

@[simp]
lemma cc_union_oc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    cc x r r' ∪ oc x r' R = cc x r R := by
  ext; simp_rw [cc, oc, mem_union, mem_setOf_eq, ← mem_union, Icc_union_Ioc_eq_Icc h₁ h₂]

@[simp]
lemma co_union_co {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    co x r r' ∪ co x r' R = co x r R := by
  ext; simp_rw [co, mem_union, mem_setOf_eq, ← mem_union, Ico_union_Ico_eq_Ico h₁ h₂]

@[simp]
lemma co_union_cc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    co x r r' ∪ cc x r' R = cc x r R := by
  ext; simp_rw [co, cc, mem_union, mem_setOf_eq, ← mem_union, Ico_union_Icc_eq_Icc h₁ h₂]

@[simp]
lemma oc_union_oi {x : X} {r R : ℝ} (h : r ≤ R) : oc x r R ∪ oi x R = oi x r := by
  ext; simp_rw [oc, oi, mem_union, mem_setOf_eq, ← mem_union, Ioc_union_Ioi_eq_Ioi h]

@[simp]
lemma oo_union_ci {x : X} {r R : ℝ} (h : r < R) :
    oo x r R ∪ ci x R = oi x r := by
  ext; simp_rw [oo, ci, oi, mem_union, mem_setOf_eq, ← mem_union, Ioo_union_Ici_eq_Ioi h]

@[simp]
lemma cc_union_oi {x : X} {r R : ℝ} (h : r ≤ R) : cc x r R ∪ oi x R = ci x r := by
  ext; simp_rw [cc, oi, ci, mem_union, mem_setOf_eq, ← mem_union, Icc_union_Ioi_eq_Ici h]

@[simp]
lemma co_union_ci {x : X} {r R : ℝ} (h : r ≤ R) : co x r R ∪ ci x R = ci x r := by
  ext; simp_rw [co, ci, mem_union, mem_setOf_eq, ← mem_union, Ico_union_Ici_eq_Ici h]

variable [MeasurableSpace X] [OpensMeasurableSpace X]

@[measurability]
lemma measurableSet_oo {x : X} {r R : ℝ} : MeasurableSet (oo x r R) := by
  rw [oo_eq]; measurability

/- Start of proof attempt -/
lemma round1_measurableSet_oc {x : X} {r R : ℝ} : MeasurableSet (oc x r R) := by
  rw [oc_eq]
  apply MeasurableSet.inter
  · exact measurableSet_closedBall
  · apply MeasurableSet.compl
    exact measurableSet_closedBall

theorem measurableSet_oc {x : X} {r R : ℝ} : MeasurableSet (oc x r R)  := by

  exact round1_measurableSet_oc
