-- In mathlib/Mathlib/NumberTheory/Padics/PadicIntegers.lean

/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

open Padic Metric IsLocalRing

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
def PadicInt : Type := {x : ℚ_[p] // ‖x‖ ≤ 1}

/-- The ring of `p`-adic integers. -/
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt
variable {p} {x y : ℤ_[p]}

/-! ### Ring structure and coercion to `ℚ_[p]` -/

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext

variable (p)

/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by norm_num
  one_mem' := by norm_num
  add_mem' hx hy := (padicNormE.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]
theorem mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 := Iff.rfl

variable {p}

/-- Addition on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Add ℤ_[p] := (by infer_instance : Add (subring p))

/-- Multiplication on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Mul ℤ_[p] := (by infer_instance : Mul (subring p))

/-- Negation on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Neg ℤ_[p] := (by infer_instance : Neg (subring p))

/-- Subtraction on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Sub ℤ_[p] := (by infer_instance : Sub (subring p))

/-- Zero on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Zero ℤ_[p] := (by infer_instance : Zero (subring p))

instance : Inhabited ℤ_[p] := ⟨0⟩

/-- One on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : One ℤ_[p] := ⟨⟨1, by norm_num⟩⟩

@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp, norm_cast]
theorem coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 := rfl

@[simp, norm_cast]
theorem coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 := rfl

@[simp, norm_cast]
theorem coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 := rfl

@[simp, norm_cast]
theorem coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 := rfl

@[simp, norm_cast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

@[simp] lemma coe_eq_zero : (x : ℚ_[p]) = 0 ↔ x = 0 := by rw [← coe_zero, Subtype.coe_inj]

lemma coe_ne_zero : (x : ℚ_[p]) ≠ 0 ↔ x ≠ 0 := coe_eq_zero.not

instance : AddCommGroup ℤ_[p] := (by infer_instance : AddCommGroup (subring p))

instance instCommRing : CommRing ℤ_[p] := (by infer_instance : CommRing (subring p))

@[simp, norm_cast]
theorem coe_natCast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n := rfl

@[simp, norm_cast]
theorem coe_intCast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z := rfl

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype

@[simp, norm_cast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n := rfl

theorem mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k := by simp

/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0

instance : CharZero ℤ_[p] where
  cast_injective m n h :=
    Nat.cast_injective (R := ℚ_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]
theorem intCast_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 := by simp

/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm converges to a `p`-adic
integer. -/
def ofIntSeq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) ≤ (1 : ℝ) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      apply padicNorm.of_int⟩

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

variable (p)

instance : MetricSpace ℤ_[p] := Subtype.metricSpace

instance : IsUltrametricDist ℤ_[p] := IsUltrametricDist.subtype _

instance completeSpace : CompleteSpace ℤ_[p] :=
  have : IsClosed { x : ℚ_[p] | ‖x‖ ≤ 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe

instance : Norm ℤ_[p] := ⟨fun z => ‖(z : ℚ_[p])‖⟩

variable {p}

theorem norm_def {z : ℤ_[p]} : ‖z‖ = ‖(z : ℚ_[p])‖ := rfl

variable (p)

instance : NormedCommRing ℤ_[p] :=
  { PadicInt.instCommRing with
    dist_eq := fun ⟨_, _⟩ ⟨_, _⟩ => rfl
    norm_mul := by simp [norm_def]
    norm := norm }

instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩

instance isAbsoluteValue : IsAbsoluteValue fun z : ℤ_[p] => ‖z‖ where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := by simp [norm_eq_zero]
  abv_add' := fun ⟨_, _⟩ ⟨_, _⟩ => norm_add_le _ _
  abv_mul' _ _ := by simp only [norm_def, padicNormE.mul, PadicInt.coe_mul]

variable {p}

instance : IsDomain ℤ_[p] := Function.Injective.isDomain (subring p).subtype Subtype.coe_injective

/-! ### Norm -/

theorem norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 := z.2

@[simp]
theorem norm_mul (z1 z2 : ℤ_[p]) : ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp [norm_def]

@[simp]
theorem norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ‖z ^ n‖ = ‖z‖ ^ n
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ, norm_mul]
    congr
    apply norm_pow

theorem nonarchimedean (q r : ℤ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := padicNormE.nonarchimedean _ _

theorem norm_add_eq_max_of_ne {q r : ℤ_[p]} : ‖q‖ ≠ ‖r‖ → ‖q + r‖ = max ‖q‖ ‖r‖ :=
  padicNormE.add_eq_max_of_ne

theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h

theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h

@[simp]
theorem padic_norm_e_of_padicInt (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [norm_def]

theorem norm_intCast_eq_padic_norm (z : ℤ) : ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖ := by simp [norm_def]

@[simp]
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ‖q‖ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖ := rfl

@[simp]
theorem norm_p : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ := padicNormE.norm_p

theorem norm_p_pow (n : ℕ) : ‖(p : ℤ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) := by simp

private def cauSeq_to_rat_cauSeq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ‖a‖ :=
  ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩

variable (p)

instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ ≤ 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩

theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℝ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv₀ hε (zpow_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_natCast]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert Nat.lt_pow_self _ using 1
    exact hp.1.one_lt
  · exact mod_cast hp.1.pos

theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℚ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (mod_cast hε)
  use k
  rw [show (p : ℝ) = (p : ℚ) by simp] at hk
  exact mod_cast hk

variable {p}

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_intCast_eq_padic_norm]
  padicNormE.norm_int_lt_one_iff_dvd k

theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} :
    ‖(k : ℤ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k by
    simpa [norm_intCast_eq_padic_norm]
  padicNormE.norm_int_le_pow_iff_dvd _ _

/-! ### Valuation on `ℤ_[p]` -/

/- Start of proof attempt -/
lemma round1_valuation_coe_nonneg (x : ℤ_[p]) : 0 ≤ (x : ℚ_[p]).valuation := by
  by_cases h : (x : ℚ_[p]) = 0
  · -- Case 1: (x : ℚ_[p]) = 0
    have h2 : (x : ℚ_[p]).valuation = 0 := by
      simpa [h] using PadicNormE.valuation_zero
    linarith
  · -- Case 2: (x : ℚ_[p]) ≠ 0
    have h1 : ‖(x : ℚ_[p])‖ ≤ 1 := x.2
    have h3 : 0 ≤ (x : ℚ_[p]).valuation := by
      have h4 : ‖(x : ℚ_[p])‖ ≤ 1 := h1
      exact?
    exact h3

theorem valuation_coe_nonneg : 0 ≤ (x : ℚ_[p]).valuation  := by

  exact round1_valuation_coe_nonneg x
