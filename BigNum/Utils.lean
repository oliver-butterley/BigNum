/-! Utilities for converting between bignum strings and `Nat`. -/

/-- Every character is interpreted as `0` or `1`: both `0` and ` ` are interpreted as `0`, anything
else is interpreted as `1`. -/
def bitVal : Char → Nat
  | '0' => 0
  | ' ' => 0
  | _   => 1

#eval bitVal '0'
#eval bitVal ' '
#eval bitVal '1'
#eval bitVal 'x'

/-- Evaluate reversed bitstring to `Nat`. -/
def strToNat_aux : List Char → Nat
  | [] => 0
  | h::t => 2 * strToNat_aux t + bitVal h

/-- Convert `Nat` to binary string - reversed. -/
def natToStr_aux (n : Nat) : List Char :=
  if n = 0 then []
  else (if n % 2 = 1 then '1' else '0') :: natToStr_aux (n / 2)

/-- Convert any string to a `Nat` by interpreting the characters as bit values.
- Zerosy values are `0` or ` `;
- Onesy values are `1` and any other character.
Most significant digit first as with standard written binary. -/
def strToNat (s : String) : Nat := strToNat_aux s.toList.reverse

def natToStr (n : Nat) : String := String.mk (natToStr_aux n).reverse

-- /-- Convert `Nat` to binary string. Direct version. -/
-- def natToStr (n : Nat) : String :=
--   if n = 0 then ""
--   else natToStr (n / 2) ++ (if n % 2 = 1 then "1" else "0")

#eval natToStr 5
#eval natToStr 0
#eval strToNat <| natToStr 12
