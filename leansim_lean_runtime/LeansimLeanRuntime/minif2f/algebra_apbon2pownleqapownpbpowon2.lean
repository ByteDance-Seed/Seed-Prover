import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators Complex ComplexConjugate

theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
 
    -- Define the function f(x) = x^n (as a real power). This is the function we will apply Jensen's inequality to.
    let f := fun x : ℝ => x^(n : ℝ)

    -- Get non-negativity of a and b from the hypothesis h₀ (0 < a and 0 < b).
    -- We need 0 <= a and 0 <= b for the points to be in the domain [0, \infty) (Set.Ici 0),
    -- on which the function f(x) = x^n is convex for n >= 1.
    have ha_in : 0 ≤ a := le_of_lt h₀.left
    have hb_in : 0 ≤ b := le_of_lt h₀.right

    -- Convert the hypothesis h₁ : 0 < n (n is a natural number) to the equivalent 1 ≤ n (Nat)
    -- and then to 1 ≤ (n : ℝ) (Real). The latter is needed for the convexity theorem `convexOn_rpow`.
    -- 0 < n is equivalent to n ≠ 0 for natural numbers.
    have hn_ne_zero : n ≠ 0 := Nat.pos_iff_ne_zero.mp h₁
    -- n ≠ 0 is equivalent to 1 ≤ n for natural numbers.
    have h_one_le_n : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne_zero
    -- 1 ≤ n (Nat) is equivalent to 1 ≤ (n : ℝ) (Real). This is the condition needed for `convexOn_rpow`.
    have hn_ge_one_real : 1 ≤ (n : ℝ) := Nat.one_le_cast.mpr h_one_le_n
    -- 0 ≤ (n : ℝ) follows from 1 ≤ (n : ℝ).
    have hn_ge_zero_real : 0 ≤ (n : ℝ) := by linarith [hn_ge_one_real]

    -- The function f(x) = x^(n:ℝ) is convex on [0, ∞) (Set.Ici 0) if (n:ℝ) ≥ 1.
    -- We prove this using `convexOn_rpow` and our lemma `hn_ge_one_real`.
    have h_convex : ConvexOn ℝ (Set.Ici 0) f := convexOn_rpow hn_ge_one_real

    -- Prove the base of the LHS term ((a + b) / 2) is non-negative.
    have h_base_nonneg : 0 ≤ (a + b) / (2 : ℝ) := by
      apply div_nonneg
      . exact add_nonneg ha_in hb_in
      . norm_num

    -- Rewrite the left side: ((a + b) / 2)^n to ((a + b) / 2)^(n : ℝ).
    have h_lhs_rpow_nat_eq_rpow_real : ((a + b) / 2)^n = ((a + b) / 2)^(n:ℝ) :=
      (Real.rpow_natCast ((a + b) / 2) n).symm

    -- Rewrite a^n and b^n on the right side to a^(n:ℝ) and b^(n:ℝ).
    have ha_rpow_nat_eq_rpow_real : a^n = a^(n:ℝ) :=
      (Real.rpow_natCast a n).symm
    -- Similarly, rewrite b^n on the right side to b^(n:ℝ).
    have hb_rpow_nat_eq_rpow_real : b^n = b^(n:ℝ) :=
      (Real.rpow_natCast b n).symm

    -- Create the equality for the numerator of the RHS: a^n + b^n = a^(n:ℝ) + b^(n:ℝ).
    have h_numerator_rpow_nat_eq_rpow_real : a^n + b^n = a^(n : ℝ) + b^(n : ℝ) := by
      rw [ha_rpow_nat_eq_rpow_real, hb_rpow_nat_eq_rpow_real]

    -- Now, rewrite the numerator on the RHS of the goal using the equality we just proved.
    conv =>
      rhs
      congr
      rw [h_numerator_rpow_nat_eq_rpow_real]

    -- Set up the finset, weights, and points for Jensen's inequality on two points.
    let t : Finset (Fin 2) := Finset.univ
    let w : Fin 2 → ℝ := fun _ => 1/2
    let p : Fin 2 → ℝ := ![a, b]

    -- Prove that centerMass t w p = (a + b) / 2.
    have h_cm_p : t.centerMass w p = (a + b) / (2 : ℝ) := by
      dsimp [Finset.centerMass, t, w, p]
      simp
      field_simp

    -- Prove that centerMass t w (f ∘ p) = (a^(n:ℝ) + b^(n:ℝ)) / 2.
    have h_cm_fp : t.centerMass w (f ∘ p) = (a ^ (n : ℝ) + b ^ (n : ℝ)) / (2 : ℝ) := by
      dsimp [Finset.centerMass, t, w, p, f]
      simp
      field_simp

    -- Rewrite the current goal to match the conclusion of Jensen's inequality.
    rw [h_lhs_rpow_nat_eq_rpow_real]
    rw [h_cm_p.symm]
    rw [h_cm_fp.symm]

    -- The goal is now (Finset.centerMass t w p)^(n:ℝ) ≤ Finset.centerMass w (f ∘ p).
    -- This is exactly: f (t.centerMass w p) ≤ Finset.centerMass w (f ∘ p).
    -- This matches the conclusion of ConvexOn.map_centerMass_le.

    -- Prove the points are in the convex set s = Set.Ici 0.
    -- For each i in t = Finset.univ (Fin 2), p i ∈ Set.Ici 0.
    -- p 0 = a, p 1 = b. We need 0 ≤ a and 0 ≤ b, which are ha_in and hb_in.
    have hp_in_s : ∀ (i : Fin 2), i ∈ t → p i ∈ Set.Ici 0 := by
      intro i _
      fin_cases i
      . exact ha_in
      . exact hb_in

    -- Prove the weights are non-negative.
    -- For each i in t = Finset.univ (Fin 2), w i ≥ 0.
    -- w i = 1/2. We need 1/2 ≥ 0.
    have hw_nonneg : ∀ (i : Fin 2), i ∈ t → 0 ≤ w i := by
      intro i hi
      norm_num

    -- Prove the sum of weights is positive.
    -- ∑ i in Finset.univ (Fin 2), (1/2 : ℝ) = 1/2 + 1/2 = 1.
    -- We need 0 < 1.
    have hw_pos : 0 < ∑ i in t, w i := by
      dsimp [t, w]
      simp

    -- Prove the fifth hypothesis for ConvexOn.map_centerMass_le_of_continuousOn: f is continuous on s.
    -- f(x) = x^(n:ℝ) is continuous on [0, ∞) (Set.Ici 0).
    -- We use `ContinuousAt.continuousOn` which requires proving `ContinuousAt f x` for every `x` in `Set.Ici (0 : ℝ)`.
    -- The theorem is `Real.continuousAt_rpow_const x q : x ≠ 0 ∨ 0 ≤ q → ContinuousAt (fun y => y ^ q) x`.
    -- Here, the function is `f = fun y => y^(n : ℝ)`, so `q = (n : ℝ)`.
    -- We need to prove `ContinuousAt f x` for `x ∈ Set.Ici (0 : ℝ)`.
    -- This requires proving `x ≠ 0 ∨ 0 ≤ (n : ℝ)`.
    -- We know `hn_ge_zero_real : 0 ≤ (n : ℝ)`. This is the second part of the disjunction.
    have h_continuous : ContinuousOn f (Set.Ici (0 : ℝ)) := by
      apply ContinuousAt.continuousOn
      intro x hx -- hx : x ∈ Set.Ici (0 : ℝ), i.e., 0 ≤ x
      -- We need to apply `Real.continuousAt_rpow_const x (n : ℝ)` with a proof of `x ≠ 0 ∨ 0 ≤ (n : ℝ)`.
      -- We know `0 ≤ (n : ℝ)` by `hn_ge_zero_real`.
      -- So we can prove the disjunction `x ≠ 0 ∨ 0 ≤ (n : ℝ)` using `Or.inr hn_ge_zero_real`.
      exact Real.continuousAt_rpow_const x (n : ℝ) (Or.inr hn_ge_zero_real)

    -- Now apply Jensen's inequality using all the proven hypotheses.
    -- The goal is already in the correct form: `f (t.centerMass w p) ≤ Finset.centerMass w (f ∘ p)`.
    -- The `ContinuousOn` instance `h_continuous` is required explicitly by the theorem `ConvexOn.map_centerMass_le_of_continuousOn`.
    -- -- The original code used the theorem `ConvexOn.map_centerMass_le` which does not require the continuity hypothesis `h_continuous`.
    -- -- Since we have proved `h_continuous`, we should use the theorem that requires it: `ConvexOn.map_centerMass_le_of_continuousOn`.
    -- -- The constant 'ConvexOn.map_centerMass_le_of_continuousOn' does not exist. The correct theorem is `ConvexOn.map_centerMass_le` which does not require the continuity hypothesis. We use that theorem instead.
    exact ConvexOn.map_centerMass_le h_convex hw_nonneg hw_pos hp_in_s


#print axioms algebra_apbon2pownleqapownpbpowon2
