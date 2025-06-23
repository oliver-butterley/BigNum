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


-- -- Normalize (remove leading zeros)
-- def normalize (s : String) : String :=
--   let trimmed := s.dropWhile (· = '0')
--   if trimmed.isEmpty then "0" else trimmed

-- Pad with zeros to equal length

-- def pad (a b : String) : (String × String) :=
--   let len := max a.length b.length
--   ("0".repeat (len - a.length) ++ a, "0".repeat (len - b.length) ++ b)

-- Full adder
-- def fullAdder (a b c : Char) : Char × Char :=
--   match (bitVal a + bitVal b + bitVal c) with
--   | 0 => ('0', '0')
--   | 1 => ('1', '0')
--   | 2 => ('0', '1')
--   | 3 => ('1', '1')
--   | _ => ('0', '0')

-- Bitwise addition

-- def addBitsRev : List Char → List Char → Char → List Char
--   | [], [], '0' => []
--   | [], [], c   => [c]
--   | ah::at, bh::bt, carry =>
--     let (sum, newCarry) := fullAdder ah bh carry
--     sum :: addBitsRev at bt newCarry
--   | [], bh::bt, c => addBitsRev ['0'] (bh::bt) c
--   | ah::at, [], c => addBitsRev (ah::at) ['0'] c

-- def add (a b : String) : String :=
--   let (a', b') := pad a b
--   String.mk (addBitsRev a'.reverse.toList b'.reverse.toList '0').reverse |> normalize

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
