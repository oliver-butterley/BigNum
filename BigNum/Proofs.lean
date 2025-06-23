import Mathlib
import BigNum.Basic
import BigNum.Utils

/-! # Proofs of correctness of the definitions. -/


/-! ## List Char -/

/-- Convenient lemma for the term used in the definition of `natToListChar`. -/
lemma bitVal_of_mod_two (n : Nat) : bitVal (if n % 2 = 1 then '1' else '0') = n % 2 := by
  by_cases h : n % 2 = 1
  · simp [h, bitVal]
  · have : n % 2 = 0 := (Nat.mod_two_eq_zero_or_one n).resolve_right h
    simp [this, bitVal]

/-- Convenient lemma for the term used in the definition of `listCharToNat`. -/
lemma listCharToNat_cons (h : Char) (t : List Char) :
  listCharToNat (h :: t) = 2 * listCharToNat t + bitVal h := rfl

/-- Converting a `Nat` to a `List Char` and then back is the identity. -/
lemma natToStr_listCharToNat (n : Nat) : listCharToNat (natToListChar n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 0
    · simp [h, natToListChar, listCharToNat]
    · suffices
          2 * listCharToNat (natToListChar (n / 2)) + bitVal (if n % 2 = 1 then '1' else '0') = n by
        unfold natToListChar; simpa [h, listCharToNat_cons]
      have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
      rw [ih (n / 2) div_lt, bitVal_of_mod_two]
      omega

/-! ## List Bool -/

/-- Convenient lemma for the term used in the definition of `listCharToNat`. -/
lemma listBoolToNat_cons (h : Bool) (t : List Bool) :
  listBoolToNat (h :: t) = 2 * listBoolToNat t + (if h then 1 else 0) := rfl

/-- Converting a `Nat` to a `List Char` and then back is the identity. -/
lemma natToListBool_listBoolToNat (n : Nat) : listBoolToNat (natToListBool n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 0
    · simp [h, natToListBool, listBoolToNat]
    · suffices
          (2 * listBoolToNat (natToListBool (n / 2)) + if n % 2 = 1 then 1 else 0) = n by
        unfold natToListBool
        simpa [h, listBoolToNat_cons]
      have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
      rw [ih (n / 2) div_lt]
      by_cases hc : n % 2 = 1
      all_goals
      · simp only [hc, reduceIte]; omega

lemma addBitsWithCarry_correct (a b carry : Bool) :
  let (sum, carryOut) := addBitsWithCarry a b carry
  (if sum then 1 else 0) + 2 * (if carryOut then 1 else 0) =
  (if a then 1 else 0) + (if b then 1 else 0) + (if carry then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : carry <;>
    simp [ha, hb, hc, addBitsWithCarry]

/-- BigNum addition on `List Bool` agress with `Nat` addition. -/
theorem addBoolList_correct (a b : List Bool) (carry : Bool) :
    listBoolToNat (addBoolList a b carry) = listBoolToNat a + listBoolToNat b +
    (if carry then 1 else 0) := by
  induction a, b, carry using addBoolList.induct with
  | case1 =>
    simp [listBoolToNat, addBoolList]
  | case2 carry h =>
    simp [listBoolToNat, addBoolList, h]
  | case3 carry b bs sum newCarry h ih =>
    -- proof for `[], b::bs`
    rw [show listBoolToNat [] = 0 by rfl, zero_add] at ⊢ ih
    -- unfold listBoolToNat at ⊢ ih
    have : addBoolList [] (b::bs) carry = sum :: addBoolList [] bs newCarry := by
      sorry
    rw [this]
    have h' := addBitsWithCarry_correct false b carry
    simp at h'
    by_cases hcarry : carry
    · simp_all [hcarry]

      sorry
    · simp_all [hcarry]

      sorry

  | case4 carry a as sum newCarry h ih =>
    -- proof for `a::as, []`
    sorry
  | case5 carry a as b bs sum newCarry h ih =>
    -- proof for `a::as, b::bs`, with induction hypothesis `ih`
    sorry

/-! ## String -/

/-- Converting a `Nat` to a string and then back is the identity. -/
lemma strToNat_natToStr_id n : strToNat (natToStr n) = n := by
  simp [strToNat, natToStr, natToStr_listCharToNat]


/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct (a b : String) : strToNat (add a b) = strToNat a + strToNat b := by

  sorry

-- theorem add_correct m n : strToNat (add (natToStr n) (natToStr m)) = n + m := by
--   sorry
