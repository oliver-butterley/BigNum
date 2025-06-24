-- import BigNum.Defs
/-! Utilities for converting between bignum strings and `Nat`. -/

-- DEPRECATED

/-- Every character is interpreted as `0` or `1`: both `0` and ` ` are interpreted as `0`, anything
else is interpreted as `1`. -/
-- def bitVal : Char → Nat
--   | '0' => 0
--   | ' ' => 0
--   | _   => 1

-- #eval bitVal '0'
-- #eval bitVal ' '
-- #eval bitVal '1'
-- #eval bitVal 'x'

-- /-- Evaluate reversed bitstring to `Nat`. -/
-- def listCharToNat : List Char → Nat
--   | [] => 0
--   | h::t => 2 * listCharToNat t + bitVal h

-- /-- Convert `Nat` to binary string - reversed. -/
-- def natToListChar (n : Nat) : List Char :=
--   if n = 0 then []
--   else (if n % 2 = 1 then '1' else '0') :: natToListChar (n / 2)

-- /-- Convert any string to a `Nat` by interpreting the characters as bit values.
-- - Zerosy values are `0` or ` `;
-- - Onesy values are `1` and any other character.
-- Most significant digit first as with standard written binary. -/
-- def strToNat' (s : String) : Nat := listCharToNat s.toList.reverse

-- def natToStr' (n : Nat) : String := String.mk (natToListChar n).reverse

-- #eval natToStr' 5
-- #eval natToStr' 0
-- #eval strToNat' <| natToStr' 12
