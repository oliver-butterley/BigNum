import Mathlib
import BigNum.Defs

/-! # Proofs of correctness of the definitions.

Main results:

* `natToStr_strToNat`: converting a natural number to a BigNum string and then back is the identity,
  i.e., `strToNat (natToStr n) = n`.
* `add_correct`: addition of BigNums corresponds to addition of the natural numbers, i.e., given
  strings `a`, `b`, `strToNat (add a b) = strToNat a + strToNat b`.

-/

/-! ## Conversion between `List Bool` and `Nat`. -/

/-- Convenient lemma for the term which occurs in `listBoolToNat`. -/
@[simp]
lemma listBoolToNat_cons (h : Bool) (t : List Bool) :
  listBoolToNat (h :: t) = 2 * listBoolToNat t + (if h then 1 else 0) := rfl

/-- Converting a `Nat` to a `List Bool` and then back is the identity. -/
@[simp]
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

/-! ## Conversion between strings, `List Bool` and `Nat`. -/

@[simp]
theorem boolToChar_charToBool_id (b : Bool) : charToBool (boolToChar b) = b := by
  by_cases hb : b
  all_goals
  · simp [hb, charToBool, boolToChar]

/-- Converting from `List Bool` to `String` and back again is the identity. -/
@[simp]
theorem listBoolToStr_strToListBool_id (bools : List Bool) :
    strToListBool (listBoolToStr bools) = bools := by
  induction bools with
  | nil =>
    simp [strToListBool, listBoolToStr]
  | cons bh bt ih =>
    suffices h : List.map (charToBool ∘ boolToChar) bt = bt by
      simpa [strToListBool, listBoolToStr]
    refine List.map_id'' (fun a ↦ ?_) bt
    exact boolToChar_charToBool_id a

/-- Converting a `Nat` to a string and then back is the identity. -/
@[simp]
lemma natToStr_strToNat (n : Nat) : strToNat (natToStr n) = n := by
  simp [strToNat, natToStr]


/-! ## Correctness of addition -/

@[simp]
lemma addBitsWithCarry_of_FXF (b : Bool) : addBitsWithCarry false b false = (b, false) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_XFF (b : Bool) : addBitsWithCarry  b false false = (b, false) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_FFT : addBitsWithCarry false false true = (true, false) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_TFT : addBitsWithCarry true false true = (false, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_FTT : addBitsWithCarry false true true = (false, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_TTF : addBitsWithCarry true true false = (false, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addBitsWithCarry_of_TTT : addBitsWithCarry true true true  = (true, true) := by
  simp [addBitsWithCarry]

@[simp]
lemma addListBool_of_empty_left (bs : List Bool) : addListBool [] bs = bs := by
  induction bs with
  | nil => simp [addListBool]
  | cons h t ih => simpa [addListBool, addBitsWithCarry_of_FXF]

@[simp]
lemma addListBool_of_empty_right (bs : List Bool) : addListBool bs [] = bs := by
  induction bs with
  | nil => simp [addListBool]
  | cons h t ih =>
    simpa [addListBool]

@[simp]
lemma addListBool_of_empty_left_of_carry (bs : List Bool) :
    listBoolToNat (addListBool [] bs true) = listBoolToNat bs + 1 := by
  induction bs with
  | nil => simp [listBoolToNat, addListBool]
  | cons h t ih =>
    by_cases hh : h
    · have : 2 * (listBoolToNat t + 1) = 2 * listBoolToNat t + 1 + 1 := by ring
      simpa [hh, addListBool, listBoolToNat, ih]
    · simp [hh, addListBool, listBoolToNat, ih]

@[simp]
lemma addListBool_of_empty_right_of_carry (bs : List Bool) :
    listBoolToNat (addListBool  bs [] true) = listBoolToNat bs + 1 := by
  induction bs with
  | nil => simp [listBoolToNat, addListBool]
  | cons h t ih =>
    by_cases hh : h
    · have : 2 * (listBoolToNat t + 1) = 2 * listBoolToNat t + 1 + 1 := by ring
      simpa [hh, addListBool, listBoolToNat, ih]
    · simp [hh, addListBool, listBoolToNat, ih]

@[simp]
lemma listBoolToNat_of_empty : listBoolToNat [] = 0 := by rfl

/-- BigNum addition on `List Bool` agress with `Nat` addition. -/
theorem addListBool_correct (a b : List Bool) (carry : Bool) :
    listBoolToNat (addListBool a b carry) = listBoolToNat a + listBoolToNat b +
    (if carry then 1 else 0) := by
  induction a, b, carry using addListBool.induct with
  | case1 =>
    simp [listBoolToNat, addListBool]
  | case2 carry h =>
    simp [listBoolToNat, addListBool, h]
  | case3 carry b =>
    -- Case: `[], b::bs`
    by_cases carry <;> by_cases b <;> simp_all
  | case4 carry a =>
    -- Case: `a::as, []`
    by_cases carry <;> by_cases a <;> simp_all
  | case5 carry a _ b _ =>
    -- Case: `a::as, b::bs`
    by_cases carry <;> by_cases ha : a <;> by_cases hb : b <;> simp_all [addListBool] <;> ring

/-! ## Addition of BigNum strings -/

/-- BigNum addition agress with `Nat` addition. -/
theorem add_correct (a b : String) : strToNat (add a b) = strToNat a + strToNat b := by
  unfold add
  have A : listBoolToNat (addListBool (strToListBool a) (strToListBool b)) =
      listBoolToNat (strToListBool a) + listBoolToNat (strToListBool b) := by
    simp [addListBool_correct]
  have B bs : strToNat (listBoolToStr bs) = listBoolToNat bs := by
    unfold strToNat
    rw [listBoolToStr_strToListBool_id bs]
  rw [B, A]
  exact rfl

/-! ## Correctness of subtraction -/

#eval subBitsWithBorrow false false false
#eval subBitsWithBorrow true false false
#eval subBitsWithBorrow false true false
#eval subBitsWithBorrow true true false
#eval subBitsWithBorrow false false true
#eval subBitsWithBorrow true false true
#eval subBitsWithBorrow false true true
#eval subBitsWithBorrow true true true



-- DEPRECATED

-- /-! ## List Char -/

-- /-- Convenient lemma for the term used in the definition of `natToListChar`. -/
-- lemma bitVal_of_mod_two (n : Nat) : bitVal (if n % 2 = 1 then '1' else '0') = n % 2 := by
--   by_cases h : n % 2 = 1
--   · simp [h, bitVal]
--   · have : n % 2 = 0 := (Nat.mod_two_eq_zero_or_one n).resolve_right h
--     simp [this, bitVal]

-- /-- Convenient lemma for the term used in the definition of `listCharToNat`. -/
-- lemma listCharToNat_cons (h : Char) (t : List Char) :
--   listCharToNat (h :: t) = 2 * listCharToNat t + bitVal h := rfl

-- /-- Converting a `Nat` to a `List Char` and then back is the identity. -/
-- lemma natToStr_listCharToNat (n : Nat) : listCharToNat (natToListChar n) = n := by
--   induction n using Nat.strong_induction_on with
--   | h n ih =>
--     by_cases h : n = 0
--     · simp [h, natToListChar, listCharToNat]
--     · suffices
--           2 * listCharToNat (natToListChar (n / 2)) + bitVal (if n % 2 = 1 then '1' else '0') = n by
--         unfold natToListChar; simpa [h, listCharToNat_cons]
--       have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)
--       rw [ih (n / 2) div_lt, bitVal_of_mod_two]
--       omega


-- /-- Converting a `Nat` to a string and then back is the identity. -/
-- @[simp]
-- lemma strToNat_natToStr_id n : strToNat' (natToStr' n) = n := by
--   simp [strToNat', natToStr', natToStr_listCharToNat]

-- /-- Altenatively `strToNat` could be defined using this equality. -/
-- @[simp]
-- lemma strToListBool_listBoolToNat (a : String) : listBoolToNat (strToListBool a) = strToNat' a := by
--   sorry

-- @[simp]
-- lemma listBoolStr_strToNat (bs : List Bool) : strToNat' (listBoolToStr bs) = listBoolToNat bs := by
--   rw [← strToListBool_listBoolToNat, listBoolToStr_strToListBool_id]
