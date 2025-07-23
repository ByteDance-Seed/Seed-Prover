-- In ConNF/ConNF/Model/RaiseStrong.lean

import ConNF.Model.Externalise

/-!
# New file

In this file...

## Main declarations

* `ConNF.foo`: Something new.
-/

noncomputable section
universe u

open Cardinal Ordinal

namespace ConNF

variable [Params.{u}] {β γ : Λ} {hγ : (γ : TypeIndex) < β}

namespace Support

theorem not_mem_scoderiv_botDeriv (S : Support γ) (N : NearLitter) :
    N ∉ (S ↗ hγ ⇘. (Path.nil ↘.))ᴺ := by
  rintro ⟨i, ⟨A, N'⟩, h₁, h₂⟩
  simp only [Prod.mk.injEq] at h₂
  cases A
  case sderiv δ A hδ _ =>
    simp only [Path.deriv_sderiv] at h₂
    cases A
    case nil => cases h₂.1
    case sderiv ζ A hζ _ =>
      simp only [Path.deriv_sderiv] at h₂
      cases h₂.1

variable [Level] [LtLevel β]

theorem not_mem_strong_botDeriv (S : Support γ) (N : NearLitter) :
    N ∉ ((S ↗ hγ).strong ⇘. (Path.nil ↘.))ᴺ := by
  rintro h
  rw [strong, close_nearLitters, preStrong_nearLitters, Enumeration.mem_add_iff] at h
  obtain h | h := h
  · exact not_mem_scoderiv_botDeriv S N h
  · rw [mem_constrainsNearLitters_nearLitters] at h
    obtain ⟨B, N', hN', h⟩ := h
    cases h using Relation.ReflTransGen.head_induction_on
    case refl => exact not_mem_scoderiv_botDeriv S N hN'
    case head x hx₁ hx₂ _ =>
      obtain ⟨⟨γ, δ, ε, hδ, hε, hδε, A⟩, t, B, hB, hN, ht⟩ := hx₂
      simp only at hB
      cases B
      case nil =>
        cases hB
        obtain ⟨C, N''⟩ := x
        simp only at ht
        cases ht.1
        change _ ∈ t.supportᴺ at hN
        rw [t.support_supports.2 rfl] at hN
        obtain ⟨i, hN⟩ := hN
        cases hN
      case sderiv δ B hδ _ _ =>
        cases B
        case nil => cases hB
        case sderiv ζ B hζ _ _ => cases hB

theorem raise_preStrong' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).PreStrong := by
  apply hS.toPreStrong.add
  constructor
  intro A N hN P t hA ht
  obtain ⟨A, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv hN
  simp only [scoderiv_botDeriv_eq, add_derivBot, smul_derivBot,
    BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, interferenceSupport_nearLitters,
    Enumeration.mem_add_iff, Enumeration.mem_smul, Enumeration.not_mem_empty, or_false] at hN
  obtain ⟨δ, ε, ζ, hε, hζ, hεζ, B⟩ := P
  dsimp only at *
  cases A
  case sderiv ζ' A hζ' _ =>
    rw [← Path.coderiv_deriv] at hA
    cases Path.sderiv_index_injective hA
    apply Path.sderiv_left_inj.mp at hA
    cases A
    case nil =>
      cases hA
      cases not_mem_strong_botDeriv T _ hN
    case sderiv ι A hι _ _ =>
      rw [← Path.coderiv_deriv] at hA
      cases Path.sderiv_index_injective hA
      cases hA
      haveI : LtLevel δ := ⟨A.le.trans_lt LtLevel.elim⟩
      haveI : LtLevel ε := ⟨hε.trans LtLevel.elim⟩
      haveI : LtLevel ζ := ⟨hζ.trans LtLevel.elim⟩
      have := (T ↗ hγ).strong_strong.support_le hN ⟨δ, ε, ζ, hε, hζ, hεζ, A⟩
          (ρ⁻¹ ⇘ A ↘ hε • t) rfl ?_
      · simp only [Tangle.smul_support, allPermSderiv_forget, allPermDeriv_forget,
          allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv] at this
        have := smul_le_smul this (ρᵁ ⇘ A ↘ hε)
        simp only [smul_inv_smul] at this
        apply le_trans this
        intro B
        constructor
        · intro a ha
          simp only [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv,
            deriv_derivBot, Enumeration.mem_smul] at ha
          rw [deriv_derivBot, ← Path.deriv_scoderiv, Path.coderiv_deriv', scoderiv_botDeriv_eq,]
          simp only [Path.deriv_scoderiv, add_derivBot, smul_derivBot,
            BaseSupport.add_atoms, BaseSupport.smul_atoms, Enumeration.mem_add_iff,
            Enumeration.mem_smul]
          exact Or.inl ha
        · intro N hN
          simp only [smul_derivBot, Tree.sderiv_apply, Tree.deriv_apply, Path.deriv_scoderiv,
            deriv_derivBot, Enumeration.mem_smul] at hN
          rw [deriv_derivBot, ← Path.deriv_scoderiv, Path.coderiv_deriv', scoderiv_botDeriv_eq,]
          simp only [Path.deriv_scoderiv, add_derivBot, smul_derivBot,
            BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, Enumeration.mem_add_iff,
            Enumeration.mem_smul]
          exact Or.inl hN
      · rw [← smul_fuzz hε hζ hεζ, ← ht]
        simp only [Path.botSderiv_coe_eq, BasePerm.smul_nearLitter_litter, allPermDeriv_forget,
          allPermForget_inv, Tree.inv_deriv, Tree.inv_sderiv, Tree.inv_sderivBot]
        rfl

theorem raise_closed' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Closed := by
  constructor
  intro A
  constructor
  intro N₁ N₂ hN₁ hN₂ a ha
  simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff,
    BaseSupport.add_atoms] at hN₁ hN₂ ⊢
  obtain hN₁ | hN₁ := hN₁
  · obtain hN₂ | hN₂ := hN₂
    · exact Or.inl ((hS.closed A).interference_subset hN₁ hN₂ a ha)
    · obtain ⟨B, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv hN₂
      simp only [smul_add, scoderiv_botDeriv_eq, add_derivBot, smul_derivBot,
        BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, Enumeration.mem_add_iff,
        Enumeration.mem_smul, BaseSupport.add_atoms, BaseSupport.smul_atoms] at hN₁ hN₂ ⊢
      refine Or.inr (Or.inr ?_)
      rw [mem_interferenceSupport_atoms]
      refine ⟨(ρᵁ B)⁻¹ • N₁, ?_, (ρᵁ B)⁻¹ • N₂, ?_, ?_⟩
      · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
        rw [← Enumeration.mem_smul, ← BaseSupport.smul_nearLitters, ← smul_derivBot, hρ]
        exact Or.inl hN₁
      · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
        simp only [interferenceSupport_nearLitters, Enumeration.not_mem_empty, or_false] at hN₂
        exact Or.inr hN₂
      · rw [← BasePerm.smul_interference]
        exact Set.smul_mem_smul_set ha
  · obtain ⟨B, rfl⟩ := eq_of_nearLitter_mem_scoderiv_botDeriv hN₁
    simp only [smul_add, scoderiv_botDeriv_eq, add_derivBot, smul_derivBot,
      BaseSupport.add_nearLitters, BaseSupport.smul_nearLitters, Enumeration.mem_add_iff,
      Enumeration.mem_smul, BaseSupport.add_atoms, BaseSupport.smul_atoms] at hN₁ hN₂ ⊢
    refine Or.inr (Or.inr ?_)
    rw [mem_interferenceSupport_atoms]
    refine ⟨(ρᵁ B)⁻¹ • N₁, ?_, (ρᵁ B)⁻¹ • N₂, ?_, ?_⟩
    · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
      simp only [interferenceSupport_nearLitters, Enumeration.not_mem_empty, or_false] at hN₁
      exact Or.inr hN₁
    · simp only [add_derivBot, BaseSupport.add_nearLitters, Enumeration.mem_add_iff]
      simp only [interferenceSupport_nearLitters, Enumeration.not_mem_empty, or_false] at hN₂
      obtain hN₂ | hN₂ := hN₂
      · rw [← Enumeration.mem_smul, ← BaseSupport.smul_nearLitters, ← smul_derivBot, hρ]
        exact Or.inl hN₂
      · exact Or.inr hN₂
    · rw [← BasePerm.smul_interference]
      exact Set.smul_mem_smul_set ha

/- Start of proof attempt -/
lemma round1_h1 (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
  (hγ : (γ : TypeIndex) < β):
  (S + (ρᵁ • ((T ↗ hγ).strong +
    (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).PreStrong := by
  exact raise_preStrong' S hS T ρ hγ

lemma round1_h2 (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
  (hγ : (γ : TypeIndex) < β)
  (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim):
  (S + (ρᵁ • ((T ↗ hγ).strong +
    (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Closed := by
  exact raise_closed' S hS T ρ hγ hρ

theorem raise_strong' (S : Support α) (hS : S.Strong) (T : Support γ) (ρ : AllPerm β)
    (hγ : (γ : TypeIndex) < β)
    (hρ : ρᵁ • (S ↘ LtLevel.elim : Support β) = S ↘ LtLevel.elim) :
    (S + (ρᵁ • ((T ↗ hγ).strong +
      (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Strong  := by

  have h1 : (S + (ρᵁ • ((T ↗ hγ).strong +
    (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).PreStrong := by
    exact round1_h1 S hS T ρ hγ
  have h2 : (S + (ρᵁ • ((T ↗ hγ).strong +
    (S ↘ LtLevel.elim + (T ↗ hγ).strong).interferenceSupport)) ↗ LtLevel.elim).Closed := by
    exact round1_h2 S hS T ρ hγ hρ
  exact ⟨h1, h2⟩
