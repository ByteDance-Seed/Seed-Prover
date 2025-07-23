-- In ConNF/ConNF/Strong/Strong.lean

import ConNF.Background.ReflTransGen
import ConNF.FOA.Inflexible

/-!
# Strong supports

In this file, we define strong supports.

## Main declarations

* `ConNF.Support.Strong`: The property that a support is strong.
-/

noncomputable section
universe u

open Cardinal Ordinal
open scoped symmDiff

namespace ConNF

variable [Params.{u}] {β : TypeIndex}

structure BaseSupport.Closed (S : BaseSupport) : Prop where
  interference_subset {N₁ N₂ : NearLitter} :
    N₁ ∈ Sᴺ → N₂ ∈ Sᴺ → ∀ a ∈ interference N₁ N₂, a ∈ Sᴬ

namespace Support

variable [Level] [CoherentData] [LeLevel β]

structure PreStrong (S : Support β) : Prop where
  support_le {A : β ↝ ⊥} {N : NearLitter} (h : N ∈ (S ⇘. A)ᴺ)
    (P : InflexiblePath β) (t : Tangle P.δ)
    (hA : A = P.A ↘ P.hε ↘.) (ht : Nᴸ = fuzz P.hδε t) :
    t.support ≤ S ⇘ (P.A ↘ P.hδ)

structure Closed (S : Support β) : Prop where
  closed : ∀ A, (S ⇘. A).Closed

structure Strong (S : Support β) extends S.PreStrong, S.Closed : Prop

theorem PreStrong.smul {S : Support β} (hS : S.PreStrong) (ρ : AllPerm β) : (ρᵁ • S).PreStrong := by
  constructor
  intro A N hN P t hA ht
  rw [smul_derivBot, BaseSupport.smul_nearLitters, Enumeration.mem_smul] at hN
  have := hS.support_le hN P (ρ⁻¹ ⇘ P.A ↘ P.hδ • t) hA ?_
  · convert smul_le_smul this (ρᵁ ⇘ P.A ↘ P.hδ) using 1
    · rw [Tangle.smul_support, smul_smul,
        allPermSderiv_forget, allPermDeriv_forget, allPermForget_inv,
        Tree.inv_deriv, Tree.inv_sderiv, mul_inv_cancel, one_smul]
    · ext B : 1
      rw [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv]
      rfl
  · rw [← smul_fuzz P.hδ P.hε P.hδε, allPermDeriv_forget, allPermForget_inv,
      BasePerm.smul_nearLitter_litter, ← Tree.inv_apply, hA, ht]
    rfl

theorem Closed.smul {S : Support β} (hS : S.Closed) (ρ : AllPerm β) : (ρᵁ • S).Closed := by
  constructor
  intro A
  constructor
  intro N₁ N₂ h₁ h₂
  simp only [smul_derivBot, BaseSupport.smul_nearLitters, BaseSupport.smul_atoms,
    Enumeration.mem_smul] at h₁ h₂ ⊢
  intro a ha
  apply (hS.closed A).interference_subset h₁ h₂
  rwa [← BasePerm.smul_interference, Set.smul_mem_smul_set_iff]

theorem Strong.smul {S : Support β} (hS : S.Strong) (ρ : AllPerm β) : (ρᵁ • S).Strong :=
  ⟨hS.toPreStrong.smul ρ, hS.toClosed.smul ρ⟩

theorem PreStrong.add {S T : Support β} (hS : S.PreStrong) (hT : T.PreStrong) :
    (S + T).PreStrong := by
  constructor
  intro A N hN P t hA ht
  simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff] at hN
  obtain hN | hN := hN
  · intro B
    simp only [deriv_derivBot, add_derivBot]
    exact (hS.support_le hN P t hA ht B).trans (BaseSupport.le_add_right)
  · intro B
    simp only [deriv_derivBot, add_derivBot]
    exact (hT.support_le hN P t hA ht B).trans (BaseSupport.le_add_left)

omit [Level] [CoherentData] [LeLevel β] in

/- Start of proof attempt -/
lemma round1_Closed_scoderiv {γ : TypeIndex} {S : Support γ} (hS : S.Closed) (hγ : γ < β) :
    (S ↗ hγ).Closed := by
  constructor
  intro A
  constructor
  intros N₁ N₂ hN₁ hN₂ a ha
  have h11 : ∃ (B : γ ↝ ⊥), A = B ↗ hγ := ConNF.Support.eq_of_nearLitter_mem_scoderiv_botDeriv hN₁
  obtain ⟨B, hB⟩ := h11
  have h3 : (S ↗ hγ) ⇘ A = S ⇘ B := by
    have h5 : (S ↗ hγ) ⇘ (B ↗ hγ) = S ⇘ B := ConNF.Support.scoderiv_deriv_eq S B hγ
    rw [hB]
    <;> tauto
  have h6 : (S ↗ hγ) ⇘. A = S ⇘. B := by
    ext1
    <;> simp_all
  have h7 : (S ⇘. B).Closed := hS.closed B
  have hN₁' : N₁ ∈ (S ⇘. B)ᴺ := by
    have hN₁1 : N₁ ∈ ((S ↗ hγ) ⇘. A)ᴺ := hN₁
    rw [h6] at hN₁1
    tauto
  have hN₂' : N₂ ∈ (S ⇘. B)ᴺ := by
    have hN₂1 : N₂ ∈ ((S ↗ hγ) ⇘. A)ᴺ := hN₂
    rw [h6] at hN₂1
    tauto
  have h12 : a ∈ (S ⇘. B)ᴬ := by
    exact h7.interference_subset hN₁' hN₂' a ha
  have h_final : a ∈ ((S ↗ hγ) ⇘. A)ᴬ := by
    rw [h6]
    exact h12
  exact h_final

theorem Closed.scoderiv {γ : TypeIndex} {S : Support γ} (hS : S.Closed) (hγ : γ < β) :
    (S ↗ hγ).Closed  := by

  exact round1_Closed_scoderiv hS hγ
