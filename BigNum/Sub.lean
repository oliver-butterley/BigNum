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

lemma subBitsWithBorrow_correct (a b borrow : Bool) :
  let (diff, borrowOut) := subBitsWithBorrow a b borrow
  a.toNat + (if borrowOut then 2 else 0) = b.toNat + borrow.toNat + diff.toNat := by
  simp only [subBitsWithBorrow]
  -- Mechanically check all 8 cases
  cases a <;> cases b <;> cases borrow <;> simp [Bool.toNat]

lemma subListBoolAux_correct (a b : List Bool) (borrow : Bool) (acc : List Bool) :
    let (result, finalBorrow) := subListBoolAux a b borrow acc
    listBoolToNat a + borrow.toNat + listBoolToNat (acc.reverse) * 2 ^ a.length =
    listBoolToNat b + listBoolToNat result + (if finalBorrow then 2 ^ (max a.length b.length + acc.length) else 0) := by
  sorry
  -- induction a with
  -- | nil =>
  --   induction b with
  --   | nil =>
  --     -- Base case: both lists empty
  --     simp only [subListBoolAux, listBoolToNat_nil, List.length_nil, max_zero_left,
  --                 zero_add, mul_zero, add_zero, pow_zero, List.reverse_reverse]
  --     cases borrow <;> simp [Bool.toNat]
  --   | cons b bs =>
  --     -- Case: a empty, b non-empty (always underflows)
  --     simp only [subListBoolAux]
  --     -- Result is [], finalBorrow is true
  --     simp [listBoolToNat_nil, List.length_nil, zero_add]
  --     -- This case needs careful handling of the underflow
  --     sorry
  -- | cons a as =>
  --   induction b with
  --   | nil =>
  --     -- Case: a non-empty, b empty
  --     let (diff, newBorrow) := subBitsWithBorrow a false borrow
  --     -- Apply subBitsWithBorrow_correct
  --     have bit_correct := subBitsWithBorrow_correct a false borrow
  --     simp only [Bool.toNat_false, add_zero] at bit_correct
  --     -- Use inductive hypothesis on the tail
  --     sorry
  --   | cons b bs =>
  --     -- Main inductive case: both lists non-empty
  --     let (diff, newBorrow) := subBitsWithBorrow a b borrow
  --     -- Apply subBitsWithBorrow_correct
  --     have bit_correct := subBitsWithBorrow_correct a b borrow
  --     -- The result is diff :: (result of recursive call)
  --     simp only [subListBoolAux]
  --     -- Use inductive hypothesis
  --     have ih_applied := (subListBoolAux_correct as bs newBorrow (diff :: acc))
  --     -- Combine bit_correct with ih_applied using properties of listBoolToNat
  --     -- Key insight: listBoolToNat (a::as) = 2 * listBoolToNat as + a.toNat
  --     simp only [listBoolToNat_cons, List.length_cons] at ih_applied ⊢
  --     -- Algebraic manipulation to combine the equations
  --     sorry

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
