import Mathlib
import BigNum.Basic
import BigNum.Utils

/-- Convenient lemma for the term used in the definition of `natToStr_aux`. -/
lemma bitVal_of_mod_two (n : Nat) :
  bitVal (if n % 2 = 1 then '1' else '0') = n % 2 := by
  by_cases h : n % 2 = 1
  · simp [h, bitVal]
  · have : n % 2 = 0 := (Nat.mod_two_eq_zero_or_one n).resolve_right h
    simp [this, bitVal]

/-- Convenient lemma for the term used in the definition of `strToNat_aux`. -/
lemma strToNat_aux_cons (h : Char) (t : List Char) :
  strToNat_aux (h :: t) = 2 * strToNat_aux t + bitVal h := rfl

/-- Converting a `Nat` to a `List Char` and then back is the identity. -/
lemma strToNat_natToStr_aux (n : Nat) : strToNat_aux (natToStr_aux n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 0
    · simp [h, natToStr_aux, strToNat_aux]
    · suffices
          2 * strToNat_aux (natToStr_aux (n / 2)) + bitVal (if n % 2 = 1 then '1' else '0') = n by
        unfold natToStr_aux; simpa [h, strToNat_aux_cons]
      have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
      rw [ih (n / 2) div_lt, bitVal_of_mod_two]
      omega

/-- Converting a `Nat` to a string and then back is the identity. -/
lemma strToNat_natToStr_id n : strToNat (natToStr n) = n := by
  simp [strToNat, natToStr, strToNat_natToStr_aux]

/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct (a b : String) : strToNat (add a b) = strToNat a + strToNat b := by

  sorry

-- theorem add_correct m n : strToNat (add (natToStr n) (natToStr m)) = n + m := by
--   sorry
