import Mathlib
import LeansimLeanRuntime
open Classical
set_option linter.all false
set_option maxHeartbeats 0
noncomputable section
open Polynomial Nat Real Classical BigOperators

-- erroneous

theorem amc12a_2020_p4
  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n) :
  S.card = 100 := by sorry

#print axioms amc12a_2020_p4

/- Sketch
variable (S : Finset ℕ) (h₀ : ∀ (n : ℕ), n ∈ S ↔ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d) ∧ 5 ∣ n)
play
  -- Define the sets of allowed digits for each position
  D0_choices := ([ (0 : ℕ) ].toFinset : Finset ℕ)
  D1_choices := ([ (0 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ) ].toFinset : Finset ℕ)
  D2_choices := ([ (0 : ℕ), (2 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ) ].toFinset : Finset ℕ)
  D3_choices := ([ (2 : ℕ), (4 : ℕ), (6 : ℕ), (8 : ℕ) ].toFinset : Finset ℕ)

  -- Define a function that constructs a number from its digits (MSB first)
  num_from_digits := fun (d3 d2 d1 d0 : ℕ) => d3 * 1000 + d2 * 100 + d1 * 10 + d0

  -- Define the set of valid tuples of digits.
  ValidTuples := Finset.product D3_choices (Finset.product D2_choices (Finset.product D1_choices D0_choices))

  -- Define the mapping function for tuples
  map_fn := fun (t : ℕ × (ℕ × (ℕ × ℕ))) => num_from_digits t.1 t.2.1 t.2.2.1 t.2.2.2

  -- Define the set of numbers that can be constructed this way
  S_constructed := Finset.image map_fn ValidTuples

  -- Step 1: Show that any n in S has its digits constrained as per D0, D1, D2, D3_choices.
  -- This section proves S ⊆ S_constructed
  suppose (n : ℕ) (h_n_in_S : n ∈ S) then
    -- Extract properties of n from h_n_in_S using h₀. These are proof terms.
    h_n_props := (h₀ n).mp h_n_in_S
    h_range_proof := h_n_props.1
    h_all_digits_even_proof := h_n_props.2.1
    h_div_5_proof := h_n_props.2.2

    -- Define digits of n
    d0 := n % 10
    d1 := (n / 10) % 10
    d2 := (n / 100) % 10
    d3 := (n / 1000) % 10

    subprob_digits_eq_list :≡ Nat.digits 10 n = [d0, d1, d2, d3]
    subprob_digits_eq_list_proof ⇐ show subprob_digits_eq_list by sorry

    -- Constraints on d0
    subprob_d0_is_digit :≡ d0 ∈ Nat.digits 10 n
    subprob_d0_is_digit_proof ⇐ show subprob_d0_is_digit by sorry
    subprob_d0_even :≡ Even d0
    subprob_d0_even_proof ⇐ show subprob_d0_even by sorry
    subprob_d0_is_0_or_5 :≡ d0 = 0 ∨ d0 = 5
    subprob_d0_is_0_or_5_proof ⇐ show subprob_d0_is_0_or_5 by sorry
    subprob_d0_in_D0 :≡ d0 ∈ D0_choices
    subprob_d0_in_D0_proof ⇐ show subprob_d0_in_D0 by sorry

    -- Constraints on d1
    subprob_d1_is_digit :≡ d1 ∈ Nat.digits 10 n
    subprob_d1_is_digit_proof ⇐ show subprob_d1_is_digit by sorry
    subprob_d1_even :≡ Even d1
    subprob_d1_even_proof ⇐ show subprob_d1_even by sorry
    subprob_d1_lt_10 :≡ d1 < 10
    subprob_d1_lt_10_proof ⇐ show subprob_d1_lt_10 by sorry
    subprob_d1_in_D1 :≡ d1 ∈ D1_choices
    subprob_d1_in_D1_proof ⇐ show subprob_d1_in_D1 by sorry

    -- Constraints on d2
    subprob_d2_is_digit :≡ d2 ∈ Nat.digits 10 n
    subprob_d2_is_digit_proof ⇐ show subprob_d2_is_digit by sorry
    subprob_d2_even :≡ Even d2
    subprob_d2_even_proof ⇐ show subprob_d2_even by sorry
    subprob_d2_lt_10 :≡ d2 < 10
    subprob_d2_lt_10_proof ⇐ show subprob_d2_lt_10 by sorry
    subprob_d2_in_D2 :≡ d2 ∈ D2_choices
    subprob_d2_in_D2_proof ⇐ show subprob_d2_in_D2 by sorry

    -- Constraints on d3
    subprob_d3_is_digit :≡ d3 ∈ Nat.digits 10 n
    subprob_d3_is_digit_proof ⇐ show subprob_d3_is_digit by sorry
    subprob_d3_even :≡ Even d3
    subprob_d3_even_proof ⇐ show subprob_d3_even by sorry
    subprob_d3_not_zero :≡ d3 ≠ 0
    subprob_d3_not_zero_proof ⇐ show subprob_d3_not_zero by sorry
    subprob_d3_lt_10 :≡ d3 < 10
    subprob_d3_lt_10_proof ⇐ show subprob_d3_lt_10 by sorry
    subprob_d3_in_D3 :≡ d3 ∈ D3_choices
    subprob_d3_in_D3_proof ⇐ show subprob_d3_in_D3 by sorry

    subprob_n_eq_num_from_digits :≡ n = num_from_digits d3 d2 d1 d0
    subprob_n_eq_num_from_digits_proof ⇐ show subprob_n_eq_num_from_digits by sorry

    n_tuple_created := (d3, (d2, (d1, d0)))
    subprob_n_tuple_in_ValidTuples :≡ n_tuple_created ∈ ValidTuples
    subprob_n_tuple_in_ValidTuples_proof ⇐ show subprob_n_tuple_in_ValidTuples by sorry
    subprob_n_in_S_constructed :≡ n ∈ S_constructed
    subprob_n_in_S_constructed_proof ⇐ show subprob_n_in_S_constructed by sorry
  subprob_S_subset_S_constructed :≡ S ⊆ S_constructed
  subprob_S_subset_S_constructed_proof ⇐ show subprob_S_subset_S_constructed by sorry

  -- Step 2: Show that any n in S_constructed is in S.
  -- This section proves S_constructed ⊆ S
  suppose (n : ℕ) (h_n_in_S_constructed : n ∈ S_constructed) then
    h_n_in_S_constructed_expanded :≡ ∃ (existing_tuple : ℕ × (ℕ × (ℕ × ℕ))), existing_tuple ∈ ValidTuples ∧ map_fn existing_tuple = n
    h_n_in_S_constructed_expanded_proof ⇐ show h_n_in_S_constructed_expanded by sorry

    ⟨extracted_tuple, h_extracted_tuple_props_proof⟩ := h_n_in_S_constructed_expanded_proof
    -- extracted_tuple is the witness: ℕ × (ℕ × (ℕ × ℕ))
    -- h_extracted_tuple_props_proof is a proof of: extracted_tuple ∈ ValidTuples ∧ map_fn extracted_tuple = n

    subprob_extracted_tuple_in_ValidTuples :≡ extracted_tuple ∈ ValidTuples
    subprob_extracted_tuple_in_ValidTuples_proof ⇐ show subprob_extracted_tuple_in_ValidTuples by sorry

    subprob_map_fn_extracted_tuple_eq_n :≡ map_fn extracted_tuple = n
    subprob_map_fn_extracted_tuple_eq_n_proof ⇐ show subprob_map_fn_extracted_tuple_eq_n by sorry

    d3_ext := extracted_tuple.1
    d2_ext := extracted_tuple.2.1
    d1_ext := extracted_tuple.2.2.1
    d0_ext := extracted_tuple.2.2.2

    subprob_n_eq_num_digits_ext :≡ n = num_from_digits d3_ext d2_ext d1_ext d0_ext
    subprob_n_eq_num_digits_ext_proof ⇐ show subprob_n_eq_num_digits_ext by sorry

    subprob_digits_ext_in_choices :≡ d3_ext ∈ D3_choices ∧ d2_ext ∈ D2_choices ∧ d1_ext ∈ D1_choices ∧ d0_ext ∈ D0_choices
    subprob_digits_ext_in_choices_proof ⇐ show subprob_digits_ext_in_choices by sorry

    subprob_n_ge_1000 :≡ 1000 ≤ n
    subprob_n_ge_1000_proof ⇐ show subprob_n_ge_1000 by sorry
    subprob_n_le_9999 :≡ n ≤ 9999
    subprob_n_le_9999_proof ⇐ show subprob_n_le_9999 by sorry
    h_n_in_range_ext :≡ 1000 ≤ n ∧ n ≤ 9999
    h_n_in_range_ext_proof ⇐ show h_n_in_range_ext by sorry

    subprob_constructed_digits_are_d0123_ext :≡ Nat.digits 10 n = [d0_ext, d1_ext, d2_ext, d3_ext]
    subprob_constructed_digits_are_d0123_ext_proof ⇐ show subprob_constructed_digits_are_d0123_ext by sorry
    subprob_all_digits_even_of_n_ext :≡ ∀ (d : ℕ), d ∈ Nat.digits 10 n → Even d
    subprob_all_digits_even_of_n_ext_proof ⇐ show subprob_all_digits_even_of_n_ext by sorry

    subprob_n_divisible_by_5_ext :≡ 5 ∣ n
    subprob_n_divisible_by_5_ext_proof ⇐ show subprob_n_divisible_by_5_ext by sorry

    subprob_n_in_S_from_constructed :≡ n ∈ S
    subprob_n_in_S_from_constructed_proof ⇐ show subprob_n_in_S_from_constructed by sorry
  subprob_S_constructed_subset_S :≡ S_constructed ⊆ S
  subprob_S_constructed_subset_S_proof ⇐ show subprob_S_constructed_subset_S by sorry

  -- Step 3: S = S_constructed
  subprob_S_eq_S_constructed :≡ S = S_constructed
  subprob_S_eq_S_constructed_proof ⇐ show subprob_S_eq_S_constructed by sorry

  -- Step 4: Calculate card S_constructed
  subprob_card_D0 :≡ D0_choices.card = 1
  subprob_card_D0_proof ⇐ show subprob_card_D0 by sorry
  subprob_card_D1 :≡ D1_choices.card = 5
  subprob_card_D1_proof ⇐ show subprob_card_D1 by sorry
  subprob_card_D2 :≡ D2_choices.card = 5
  subprob_card_D2_proof ⇐ show subprob_card_D2 by sorry
  subprob_card_D3 :≡ D3_choices.card = 4
  subprob_card_D3_proof ⇐ show subprob_card_D3 by sorry

  subprob_card_ValidTuples_calc :≡ ValidTuples.card = D3_choices.card * D2_choices.card * D1_choices.card * D0_choices.card
  subprob_card_ValidTuples_calc_proof ⇐ show subprob_card_ValidTuples_calc by sorry
  subprob_card_ValidTuples_val :≡ ValidTuples.card = 4 * 5 * 5 * 1
  subprob_card_ValidTuples_val_proof ⇐ show subprob_card_ValidTuples_val by sorry
  subprob_mult_val :≡ 4 * 5 * 5 * 1 = 100
  subprob_mult_val_proof ⇐ show subprob_mult_val by sorry

  subprob_map_fn_inj :≡ Set.InjOn map_fn ValidTuples
  subprob_map_fn_inj_proof ⇐ show subprob_map_fn_inj by sorry

  subprob_card_S_constructed_eq_card_ValidTuples :≡ S_constructed.card = ValidTuples.card
  subprob_card_S_constructed_eq_card_ValidTuples_proof ⇐ show subprob_card_S_constructed_eq_card_ValidTuples by sorry
  subprob_card_S_constructed_val :≡ S_constructed.card = 100
  subprob_card_S_constructed_val_proof ⇐ show subprob_card_S_constructed_val by sorry

  -- Final step
  subprob_final_goal :≡ S.card = 100
  subprob_final_goal_proof ⇐ show subprob_final_goal by sorry
-/
