import Mathlib
import BigNum.Defs
import BigNum.Convert

/-! # Proofs of correctness of the definitions.

Subtraction of BigNums corresponds to subtraction of the natural numbers.

Main results:

* `sub_correct`: `strToNat (sub a b) = strToNat a - strToNat b`;
* `sub_correct'`: `strToNat (sub (natToStr m) (natToStr n)) = m - n`.

Remark: if `m < n` then `m - n = 0`.
-/

#eval subBitsWithBorrow false false false
#eval subBitsWithBorrow true false false
#eval subBitsWithBorrow false true false
#eval subBitsWithBorrow true true false
#eval subBitsWithBorrow false false true
#eval subBitsWithBorrow true false true
#eval subBitsWithBorrow false true true
#eval subBitsWithBorrow true true true

@[simp]
lemma subListBool_of_empty_of_empty : subListBool [] [] = ([], false) := by
  unfold subListBool
  exact rfl

/-- BigNum subtraction on `List Bool` agress with `Nat` subtraction. -/
theorem subListBool_no_underflow (a b : List Bool) (borrow : Bool)
    (h : listBoolToNat a ≥ listBoolToNat b + (if borrow then 1 else 0)) :
    let (result, borrowOut) := subListBool a b borrow
    borrowOut = false ∧
    listBoolToNat result = listBoolToNat a - listBoolToNat b - (if borrow then 1 else 0) := by
  induction a, b, borrow using subListBool.induct with
  | case1 borrow =>
    simp [show borrow = false by simp_all]
  | case2 borrow b bs sum newCarry hsn rest finalBorrow hrf hge =>
    sorry
  | case3 borrow a as sum newCarry hsn rest finalBorrow hrf hge =>
    sorry
  | case4 borrow a as b bs sum newCarry hsn rest finalBorrow hrf hge =>
    sorry

/-- BigNum subtraction agress with `Nat` subtraction. -/
theorem sub_correct (a b : String) : strToNat (sub a b) = strToNat a - strToNat b := by
  by_cases hc : strToNat a ≥ strToNat b
  ·
    sorry
  ·
    sorry

/-- BigNum subtraction agress with `Nat` subtraction. -/
theorem sub_correct' (m n : Nat) : strToNat (sub (natToStr m) (natToStr n)) = m - n := by
  simp [sub_correct]
