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
def isPowerOfTwo (bs : List Bool) : Prop := match bs with
  | [] => False
  | true :: tail => isZero tail
  | false :: tail => isPowerOfTwo tail

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

-- TO DO: modify this to use another `List Bool` for counting, not `remaining : Nat`
/-- Take modulo 2^n by keeping only the first n bits (least significant) -/
def modPowTwo (a : List Bool) (n : Nat) : List Bool :=
  let rec takeFirstN (bits : List Bool) (remaining : Nat) : List Bool :=
    match bits, remaining with
    | [], _ => []
    | _, 0 => []
    | h :: t, Nat.succ r => h :: takeFirstN t r
  takeFirstN a n

-- /-- Multiply two numbers modulo 2^n -/
-- def mulModPowerOfTwo (a b : List Bool) (n : Nat) : List Bool :=
--   let product := mulListBool a b
--   modPowerOfTwo product n
