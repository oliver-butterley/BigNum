import Mathlib
import BigNum.Defs
import BigNum.Add
import BigNum.Mul
import BigNum.Convert

/-! # Modular Exponentiation for Power-of-2 Modulus

Implementation of (a^b) mod c when c = 2^n. In this case we can use simple bitwise operations.
For c = 2^n, taking mod c is equivalent to keeping only the lowest n bits.
-/

/-! ## Helper functions -/

/-- Check if a List Bool has no bits set. -/
def isZero (bs : List Bool) : Prop := match bs with
  | [] => True
  | true :: _ => False
  | false :: tail => isZero tail

/-- Check if a List Bool has exactly one bit set. -/
def isPowTwo (bs : List Bool) : Prop := match bs with
  | [] => False
  | true :: tail => isZero tail
  | false :: tail => isPowTwo tail

/-- Check if a number is one -/
def isOne (bs : List Bool) : Prop :=
  match bs with
  | [true] => True
  | true :: t => isZero t
  | _ => False

/-- Remove leading falses. -/
def removeLeadingZeros (bs : List Bool) : List Bool :=
  match bs with
  | [] => []
  | false :: tail => removeLeadingZeros tail -- remove false and continue
  | true :: _ => bs  -- begins with true, don't remove anything

/-- Remove trailing zeros. -/
def removeTrailingZeros (bs : List Bool) : List Bool :=
  (removeLeadingZeros bs.reverse).reverse

/-- Use a list `bs` as a counter to remove bits from `as`. -/
def modPowTwoListBool (as counter : List Bool) : List Bool :=
  match as, counter with
  | [], _ => []
  | as, [] => as
  | h :: t, false :: tc => h :: modPowTwoListBool t tc -- remove one bit from the counter and repeat
  | _, true :: _ => []

def modPowTwo (a b : String) : String :=
  listBoolToStr <| removeTrailingZeros <| modPowTwoListBool (strToListBool a) (strToListBool b)

#eval modPowTwo "1100" "100"
#eval modPowTwo "001100" "100"
#eval modPowTwo "110110" "100"
#eval modPowTwo "110110" "0"
#eval strToNat <| modPowTwo (natToStr 13) (natToStr 4)
#eval strToNat <| modPowTwo (natToStr 13) (natToStr 1)
#eval strToNat <| modPowTwo (natToStr 13) (natToStr 0)
#eval 13 % 4
#eval 13 % 1
#eval 13 % 0

-- /-- Multiply two numbers modulo 2^n -/
-- def mulModPowerOfTwo (a b : List Bool) (n : Nat) : List Bool :=
--   let product := mulListBool a b
--   modPowerOfTwo product n
