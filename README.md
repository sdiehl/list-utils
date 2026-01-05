# list-utils

Additional `List` lemmas for Lean 4 that complement Mathlib.

Mathlib provides comprehensive lemmas for `Multiset` and `Finset` sum operations,
but the `List` module has some gaps particularly around negation and subtraction.
This library fills those gaps.

## Installation

Add to your `lakefile.lean`:

```lean
require «list-utils» from git
  "https://github.com/sdiehl/list-utils.git" @ "v1.2.0"
```

Then run:

```bash
lake update
lake build
```

## Available Lemmas

### Negation
- `List.sum_map_neg` - Sum of negated elements (ℚ version)
- `List.sum_map_neg'` - Sum of negated elements (general `AddCommGroup`)

### Subtraction
- `List.sum_map_sub` - Sum distributes over subtraction (ℚ version)
- `List.sum_map_sub'` - Sum distributes over subtraction (general `AddCommGroup`)

### Scalar Multiplication
- `List.sum_mul_left` - Left scalar multiplication into sum
- `List.sum_mul_right` - Right scalar multiplication into sum

### Utilities
- `List.sum_map_const` - Sum of constant function
- `List.sum_map_append` - Sum over appended lists

### Existence Lemmas
- `List.exists_pos_of_sum_pos` - If sum of non-negative values is positive, some element is positive
- `List.exists_neg_of_sum_neg` - If sum of non-positive values is negative, some element is negative
- `List.exists_ne_zero_of_sum_ne_zero` - If sum is nonzero with same-sign elements, some element is nonzero

### Key-Based Operations
Operations for lists where elements have a key accessor, supporting the common "upsert" pattern.

- `List.upsertBy` - Update element matching key, or append default if not found
- `List.updateBy` - Update element matching key (no-op if not found)
- `List.findBy?` - Find element by key accessor
- `List.containsBy` - Check if element with key exists
- `List.removeBy` - Remove all elements where key matches

Example:
```lean
structure User where
  id : Nat
  name : String

def users : List User := [{ id := 1, name := "Alice" }]

-- Update user 1's name, or add new user if not found
let updated := users.upsertBy (·.id) 1
  (fun u => { u with name := "Alicia" })
  { id := 1, name := "Default" }
```

## License

Apache 2.0
