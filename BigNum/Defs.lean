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

/-! ## Define binary addition for list of booleans.

Rather than defining the operations directly for strings, the operations are defined on `List Bool`
as the binary representation with the least significant digit first. This choice has the convenience
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
  | h::t => 2 * listBoolToNat t + (if h then 1 else 0)

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

@[simp]
theorem boolToChar_charToBool_id (b : Bool) : charToBool (boolToChar b) = b := by
  by_cases hb : b
  all_goals
  · simp [hb, charToBool, boolToChar]

/-- Convert `String` to `List Bool`. -/
def strToListBool (s : String) : List Bool :=
  s.toList.reverse.map charToBool

/-- Convert `List Bool` back to `String`. -/
def listBoolToStr (bs : List Bool) : String :=
  String.mk <| (bs.reverse).map boolToChar

/-- Converting from `List Bool` to `String` and back again is the identity. -/
@[simp]
theorem listBoolToStr_strToListBool_id (bools : List Bool) :
    strToListBool (listBoolToStr bools) = bools := by
  induction bools with
  | nil =>
    simp [strToListBool, listBoolToStr]
  | cons bh bt ih =>
    suffices h : List.map (charToBool ∘ boolToChar) bt = bt by
      simpa [strToListBool, listBoolToStr]
    refine List.map_id'' (fun a ↦ ?_) bt
    exact boolToChar_charToBool_id a

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

#eval add "1001" "11"

-- def sub (a b : String) : Option String :=

-- def mul (a b : String) : String :=

-- def modadd (a b m : String) : String :=

-- def modmul (a b m : String) : String :=

-- def modpow (a e m : String) : String :=
