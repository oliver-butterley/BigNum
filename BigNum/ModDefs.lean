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
def isPowerOfTwo (c : List Bool) : Prop := match c with
  | [] => False
  | true :: tail => isZero tail
  | false :: tail => isPowerOfTwo tail

/-- Check if a number is one -/
def isOne (a : List Bool) : Prop :=
  match a with
  | [true] => True
  | true :: t => isZero t
  | _ => False

/-- Take modulo 2^n by keeping only the first n bits (least significant) -/
def modPowerOfTwo (a : List Bool) (n : Nat) : List Bool :=
  let rec takeFirstN (bits : List Bool) (remaining : Nat) : List Bool :=
    match bits, remaining with
    | [], _ => []
    | _, 0 => []
    | h :: t, Nat.succ r => h :: takeFirstN t r
  takeFirstN a n

/-- Multiply two numbers modulo 2^n -/
def mulModPowerOfTwo (a b : List Bool) (n : Nat) : List Bool :=
  let product := mulListBool a b
  modPowerOfTwo product n
