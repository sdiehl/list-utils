# list-utils

Additional `List` lemmas for Lean 4 that complement Mathlib.

Mathlib provides comprehensive lemmas for `Multiset` and `Finset` sum operations,
but the `List` module has some gaps particularly around negation and subtraction.
This library fills those gaps.

## Installation

Add to your `lakefile.lean`:

```lean
require «list-utils» from git
  "https://github.com/yourusername/list-utils.git" @ "main"
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

## License

Apache 2.0
