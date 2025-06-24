# BigNum

# CHALLENGE 1:

Implement basic arithmetic for arbitrarily large natural numbers ("bignats") represented as strings
containing only characters "0" and "1".

- We define natural numbers represented as bitstrings (e.g., "1011").
- All operations are purely structural (not using built-in `+`, `-`, `*` in core logic).
- Operations (`BigNum/Defs.lean`):
  - `add`: adds two bignat strings, (*complete with correctness proof*)
  - `sub`: computes the difference between two bignat strings (*in progress*)
  - `mul`: computes the product of two bignat strings (*to do*)
  - `modadd`: addition modulo n, i.e., computes $$a+b mod n$$ (*to do*)
  - `modmul`: multiplication modulo n, , i.e., computes $$a*b mod n$$ (*to do*)
  - `modexp`: exponentiation modulo n, i.e., computes $$a^b mod n$$ (*to do*)
- Utility functions (`BigNum/Defs.lean`):
  - `strToNat`: converts bignat string to nat (*complete with correctness proof*)
  - `natToStr`: converts nat to bignat string (*complete with correctness proof*)
- Formal correctness proofs provided for core arithmetic operations
- Every string is a bignat string in the sense that it corresponds to a `Nat`:
  - Most significant digit first as with standard written binary
  - Zero is represented by the empty string
  - zerosy values are `0`, ` `
  - onesy values are `1` and any other character
- Canonical form of a bignat string:
  - No leading `0`s
  - Only the characters `1` or `0`
