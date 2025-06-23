/-!
# CHALLENGE 1:

Implement basic arithmetic for arbitrarily large natural numbers ("bignats") represented as strings
containing only characters "0" and "1".

- We define natural numbers represented as bitstrings (e.g., "1011").
- All operations are purely structural (not using built-in `+`, `-`, `*` in core logic).
- Operations (`BigNum/Basic.lean`):
  - `add`: adds two bignat strings,
  - `sub`: computes the difference between two bignat strings
  - `mul`: computes the product of two bignat strings
  - `modadd`: addition modulo n, i.e., computes a+b mod n
  - `modmul`: multiplication modulo n, , i.e., computes a*b mod n
  - `modexp`: exponentiation modulo n, i.e., computes a^b mod n
- Utility functions (`BigNum/Utils.lean`):
  - `int2str`: converts bignat string to nat
  - `str2int`: converts nat to bignat string
- Formal correctness proofs provided for core arithmetic operations (`BigNum/Proofs.lean`)
- Every string is a bignat string in the sense that it corresponds to a `Nat`:
  - Most significant digit first as with standard written binary
  - Zero is represented by the empty string
  - zerosy values are `0`, ` `
  - onesy values are `1` and any other character
- Canonical form of a bignat string:
  - No leading `0`s
  - Only the characters `1` or `0`
-/

/-! ## Define binary addition for list of booleans. -/

/-- Add two bits with carry. -/
def addBitsWithCarry (a b carry : Bool) : Bool × Bool :=
  let resultBit := (a != b) != carry
  let carryOut := (a && b) || (carry && (a != b))
  (resultBit, carryOut)

#eval addBitsWithCarry true false false
#eval addBitsWithCarry true true false
#eval addBitsWithCarry true true true
#eval addBitsWithCarry false true true

-- Possible alternative: normalize and pad both strings and so avoid the matching in the following.

/-- Add two binary numbers represented as lists of booleans (least significant bit first). -/
def addBoolList (a b : List Bool) (carry : Bool := false) : List Bool :=
  match a, b with
  | [], [] => if carry then [true] else []
  | [], b::bs =>
      let (sum, newCarry) := addBitsWithCarry false b carry
      sum :: addBoolList [] bs newCarry
  | a::as, [] =>
      let (sum, newCarry) := addBitsWithCarry a false carry
      sum :: addBoolList as [] newCarry
  | a::as, b::bs =>
      let (sum, newCarry) := addBitsWithCarry a b carry
      sum :: addBoolList as bs newCarry

/-! ## Define addition for binary numbers written as strings. -/

/-- Every character is interpreted as `0` or `1`: both `0` and ` ` are interpreted as `0`, anything
else is interpreted as `1`. -/
def charToBool : Char → Bool
  | '0' => false
  | ' ' => false
  | _   => true

#eval charToBool '0'
#eval charToBool ' '
#eval charToBool '1'
#eval charToBool 'x'

/-- Convert from `Bool` to `Char`. -/
def boolToChar (b : Bool) : Char :=
  if b then '1' else '0'

/-- Convert list of chars to list of bools. -/
def toBoolList (chars : List Char) : List Bool :=
  (chars.reverse.map charToBool)

/-- Convert list of bools back to chars. -/
def toCharList (bools : List Bool) : List Char :=
  (bools.reverse.map boolToChar)

-- Main addition function for binary numbers as character lists
def addBinary (a b : List Char) : List Char :=
  let aBools := toBoolList a
  let bBools := toBoolList b
  let resultBools := addBoolList aBools bBools
  toCharList resultBools

#eval addBinary ['1', '0', '1'] ['1', '0']
#eval String.mk <| addBinary "1001".toList "1".toList

/-- Addition of two binary numbers represented as strings. -/
def add (a b : String) : String :=
  String.mk <| addBinary a.toList b.toList

#eval add "1001" "11"

-- Subtraction and multiplication

-- def sub (a b : String) : Option String :=
--   let x := str2int a
--   let y := str2int b
--   if x ≥ y then some (int2str (x - y)) else none

-- def mul (a b : String) : String :=
--   int2str (str2int a * str2int b)

-- Modular operations

-- def modadd (a b m : String) : String :=
--   int2str ((str2int a + str2int b) % str2int m)

-- def modmul (a b m : String) : String :=
--   int2str ((str2int a * str2int b) % str2int m)

-- def modpow (a e m : String) : String :=
--   int2str (Nat.powMod (str2int a) (str2int e) (str2int m))
