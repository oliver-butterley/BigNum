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
def str2int_aux : List Char → Nat
  | [] => 0
  | h::t => 2 * str2int_aux t + bitVal h

#eval str2int_aux "01".toList

/-- Convert any string to a `Nat` by interpreting the characters as bit values.
- Zerosy values are `0` or ` `;
- Onesy values are `1` and any other character.
Most significant digit first as with standard written binary. -/
def str2int (s : String) : Nat := str2int_aux s.toList.reverse

/-- Convert `Nat` to bitstring but in reverse order, . -/
partial def int2str_aux : Nat → List Char
  | 0 => ['0']
  | n =>
    let rec go : Nat → List Char
      | 0 => []
      | n => (if n % 2 = 0 then '0' else '1') :: go (n / 2)
    go n

def int2str (n : Nat) : String := String.mk (int2str_aux n).reverse
