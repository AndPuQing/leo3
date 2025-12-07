-- Basic Lean functions for testing Leo3 integration
--
-- These functions are marked for export and can be called from Rust

namespace Leo3Tests

-- Simple arithmetic operations
@[export lean_test_add]
def add (a b : Nat) : Nat := a + b

@[export lean_test_multiply]
def multiply (a b : Nat) : Nat := a * b

@[export lean_test_factorial]
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- String operations
@[export lean_test_string_length]
def stringLength (s : String) : Nat := s.length

@[export lean_test_string_concat]
def stringConcat (s1 s2 : String) : String := s1 ++ s2

-- Array operations
@[export lean_test_array_sum]
def arraySum (arr : Array Nat) : Nat :=
  arr.foldl (· + ·) 0

@[export lean_test_array_length]
def arrayLength (arr : Array α) : Nat := arr.size

-- Boolean operations
@[export lean_test_is_even]
def isEven (n : Nat) : Bool := n % 2 == 0

@[export lean_test_is_prime]
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    let rec check (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d == 0 then false
      else check (d + 1)
    check 2

end Leo3Tests
