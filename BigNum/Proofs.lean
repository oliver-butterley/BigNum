import Mathlib
-- import BigNum.Basic
import BigNum.Utils

/-! Proofs of the correctness of the definitions. -/

/-
theorem str2int_int2str_id : ∀ n : Nat, str2int (int2str n) = n := by
  intro n
  unfold int2str
  unfold str2int
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [int2strAux, str2intAux]
    | succ n' =>
      let rec go : Nat → List Char
        | 0 => []
        | k => (if k % 2 = 0 then '0' else '1') :: go (k / 2)
      have : str2intAux (List.reverse (go n)) = n := by
        induction n using Nat.strong_induction_on with
        | h n ih =>
          cases n with
          | zero => simp [go, str2intAux]
          | succ n' =>
            have q := n / 2
            have r := n % 2
            have E : n = 2 * q + r := Nat.div_add_mod n 2
            simp [go, str2intAux, List.reverse, List.foldr]
            rw [Nat.mod_two_eq_zero_or_one] at r
            cases r
            case zero =>
              simp [bitVal, E]; rw [ih q (Nat.div_lt_self (Nat.zero_lt_succ _) (by decide))]
            case succ r' =>
              have : r' = 0 := by decide
              simp [bitVal, E, this]; rw [ih q (Nat.div_lt_self (Nat.zero_lt_succ _) (by decide))]
      exact this

theorem addBitsRev_correct :
  ∀ (l1 l2 : List Char) (c : Char),
    str2intAux (addBitsRev l1 l2 c) =
      str2intAux l1 + str2intAux l2 + (if c = '1' then 1 else 0)
  := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 c
    cases l2 with
    | nil =>
      simp [addBitsRev, str2intAux]
      split <;> simp [str2intAux, bitVal]
    | cons b bs =>
      simp [addBitsRev]
      exact addBitsRev_correct [] bs c
  | cons a as ih =>
    intro l2 c
    cases l2 with
    | nil =>
      simp [addBitsRev]
      exact ih ['0'] c
    | cons b bs =>
      simp [addBitsRev]
      let (sbit, newCarry) := fullAdder a b c
      let sval := bitVal sbit
      have : str2intAux (sbit :: addBitsRev as bs newCarry) =
                sval + 2 * (str2intAux as + str2intAux bs + (if newCarry = '1' then 1 else 0)) := by
        simp [str2intAux, bitVal]
        rw [ih bs newCarry]; ring
      cases a <;> cases b <;> cases c <;> simp [fullAdder, bitVal] at * <;> assumption

theorem add_correct (a b : String) :
  str2int (add a b) = str2int a + str2int b := by
  let (a', b') := pad a b
  have : str2intAux (addBitsRev a'.reverse.toList b'.reverse.toList '0') =
           str2intAux (a'.reverse.toList) + str2intAux (b'.reverse.toList) :=
    by rw [addBitsRev_correct]; simp
  simp [add, str2int, this]
-/
