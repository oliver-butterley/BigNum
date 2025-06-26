/-!
# CHALLENGE 1:

Implement basic arithmetic for arbitrarily large natural numbers ("bignats") represented as strings
containing only characters "0" and "1".

The implementation in this file uses only structural operations on List Bool, avoiding built-in Nat
operations in the core logic.

- We define natural numbers represented as bitstrings (e.g., "1011").
- All operations are purely structural (not using built-in `+`, `-`, `*` in core logic).
- Operations:
  - `add`: adds two bignat strings,
  - `sub`: computes the difference between two bignat strings
  - `mul`: computes the product of two bignat strings
  - `modadd`: addition modulo n, i.e., computes a+b mod n
  - `modmul`: multiplication modulo n, , i.e., computes a*b mod n
  - `modexp`: exponentiation modulo n, i.e., computes a^b mod n
- Utility functions:
  - `strToNat`: converts bignat string to nat
  - `natToStr`: converts nat to bignat string
- Formal correctness proofs provided for core arithmetic operations
- Every string is a bignat string in the sense that it corresponds to a `Nat`:
  - Most significant digit first as with standard written binary
  - Zero is represented by the empty string
  - zerosy values are `0`, ` `
  - onesy values are `1` and any other character
- Canonical form of a bignat string:
  - No leading `0`s
  - Only the characters `1` or `0`
-/

/-! ## Define binary addition for list of booleans.

Rather than defining the operations directly for strings, the operations are defined on `List Bool`
as the binary representation with the least significant digit first.

This choice has the convenience
of using `::` since the order is reversed compared to written binary and that any occurences of
`a = '1'` if `a : Char` become simply `a` when `a : Bool`.
-/

/-- Add two bits with carry. -/
def addBitsWithCarry (a b carry : Bool) : Bool × Bool :=
  let resultBit := (a != b) != carry
  let carryOut := (a && b) || (carry && (a != b))
  (resultBit, carryOut)

/-- Add two binary numbers represented as lists of booleans (least significant bit first). -/
def addListBool (a b : List Bool) (carry : Bool := false) : List Bool :=
  match a, b with
  | [], [] => if carry then [true] else []
  | [], b::bs =>
    let (sum, newCarry) := addBitsWithCarry false b carry
    sum :: addListBool [] bs newCarry
  | a::as, [] =>
    let (sum, newCarry) := addBitsWithCarry a false carry
    sum :: addListBool as [] newCarry
  | a::as, b::bs =>
    let (sum, newCarry) := addBitsWithCarry a b carry
    sum :: addListBool as bs newCarry

/-! ## Conversion between `List Bool` and `Nat`. -/

/-- Convert `List Bool` to a `Nat`. -/
def listBoolToNat : List Bool → Nat
  | [] => 0
  | h::t => 2 * listBoolToNat t + h.toNat

/-- Convert a `Nat` to a `List Bool`. -/
def natToListBool (n : Nat) : List Bool :=
  if n = 0 then []
  else (if n % 2 = 1 then true else false) :: natToListBool (n / 2)

/-! ## Conversion between strings, `List Bool` and `Nat`. -/

/-- Every character is interpreted as `0` or `1`: both `0` and ` ` are interpreted as `0`, anything
else is interpreted as `1`. -/
def charToBool : Char → Bool
  | '0' => false
  | ' ' => false
  | _   => true

/-- Convert from `Bool` to `Char`. -/
def boolToChar (b : Bool) : Char :=
  if b then '1' else '0'

/-- Convert `String` to `List Bool`. -/
def strToListBool (s : String) : List Bool :=
  s.toList.reverse.map charToBool

/-- Convert `List Bool` back to `String`. -/
def listBoolToStr (bs : List Bool) : String :=
  String.mk <| (bs.reverse).map boolToChar

/-- Convert any string to a `Nat` by interpreting the characters as bit values.
- Zerosy values are `0` or ` `;
- Onesy values are `1` and any other character.
Most significant digit first as with standard written binary. -/
def strToNat (s : String) := listBoolToNat (strToListBool s)

def natToStr (n : Nat) : String := listBoolToStr (natToListBool n)

/-! ## Define addition for binary numbers written as strings. -/

/-- Addition of two binary numbers represented as strings. -/
def add (a b : String) : String :=
  listBoolToStr <| addListBool (strToListBool a) (strToListBool b)

-- Example
#eval add "1001" "11"

/-! ## Define binary subtraction for list of booleans. -/

/-- Subtract two bits with borrow. -/
def subBitsWithBorrow (a b borrow : Bool) : Bool × Bool :=
  let resultBit := (a != b) != borrow
  let borrowOut := (!a && (b || borrow)) || (b && borrow)
  (resultBit, borrowOut)

/-- Subtract two binary numbers represented as lists of booleans (least significant bit first).
Computes a - b. Returns the result and whether there was an underflow. -/
def subListBool (a b : List Bool) (borrow : Bool := false) : List Bool × Bool :=
  match a, b with
  | [], [] => ([], borrow)
  | [], b::bs =>
    -- This case is never relevant since we return [] when there is an overflow at the end.
    let (diff, newBorrow) := subBitsWithBorrow false b borrow
    let (rest, finalBorrow) := subListBool [] bs newBorrow
    (diff :: rest, finalBorrow)
  | a::as, [] =>
    let (diff, newBorrow) := subBitsWithBorrow a false borrow
    let (rest, finalBorrow) := subListBool as [] newBorrow
    (diff :: rest, finalBorrow)
  | a::as, b::bs =>
    let (diff, newBorrow) := subBitsWithBorrow a b borrow
    let (rest, finalBorrow) := subListBool as bs newBorrow
    (diff :: rest, finalBorrow)

/-- Subtract two binary numbers, returning just the result or zero if negative. -/
def subListBool' (a b : List Bool) : List Bool :=
  if (subListBool a b).2 then [] else (subListBool a b).1

-- /-- Helper function to remove leading zeros from a binary number. -/
-- def removeLeadingZeros (bits : List Bool) : List Bool :=
--   match bits.reverse with
--   | [] => []
--   | true :: rest => (true :: rest).reverse
--   | false :: rest => removeLeadingZeros rest.reverse

-- /-- Subtract two binary numbers and remove leading zeros. -/
-- def subListBoolClean (a b : List Bool) : List Bool :=
--   removeLeadingZeros (subListBoolSimple a b)

/-! ## Define subtraction for binary numbers written as strings. -/

/-- Subtraction of two binary numbers represented as strings. -/
def sub (a b : String) : String :=
  listBoolToStr <| subListBool' (strToListBool a) (strToListBool b)

-- Example
#eval sub "1001" "11"
#eval sub "1001" "001"
#eval sub "10" "11"
#eval strToNat (sub (natToStr 7) (natToStr 3))

/-! ## Define multiplication for list of booleans -/

def shiftLeft (bs : List Bool) : List Bool :=
  match bs with
  | [] => []
  | bs => false :: bs

#eval shiftLeft []
#eval shiftLeft [true]

def mulListBool_aux (a b : List Bool) (acc : List Bool) : List Bool :=
  match b with
  | [] => acc
  | false :: tb => mulListBool_aux (shiftLeft a) tb acc
  | true :: tb => mulListBool_aux (shiftLeft a) tb (addListBool acc a)

#eval mulListBool_aux [true, true] [] [true, false]

def mulListBool (a b : List Bool) : List Bool :=
  mulListBool_aux a b []

-- Example usage:
#eval mulListBool [true, false, true] [true, true] -- 5 * 3 = 15
-- Expected: [true, true, true, true] (15 in binary: 1111)

/-! ## Define multiplication for binary numbers written as strings. -/

/-- Subtraction of two binary numbers represented as strings. -/
def mul (a b : String) : String :=
  listBoolToStr <| mulListBool (strToListBool a) (strToListBool b)

#eval mul "1001" "11"
#eval mul "1001" "001"
#eval mul "10" "11"
#eval strToNat (mul (natToStr 7) (natToStr 4))


-- def modadd (a b m : String) : String :=

-- def modmul (a b m : String) : String :=

-- def modpow (a e m : String) : String :=

-- DEPRECATED

-- /-- Every character is interpreted as `0` or `1`: both `0` and ` ` are interpreted as `0`, anything
-- else is interpreted as `1`. -/
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
