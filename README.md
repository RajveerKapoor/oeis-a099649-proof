# OEIS A099649 is finite

This repository proves that [OEIS A099649](https://oeis.org/A099649) has exactly 130 terms and that its final term is 144.

Let `S(n)` be the sum of the squares of the decimal digits of `n`. A positive integer `n` belongs to A099649 when some iterate of `S`, starting at `n`, is strictly larger than `n`.

The proof has three parts:

1. `S(n) < n` for every `n >= 145`. Lean proves the finite base interval `145 <= n < 1450` by kernel-checked native decision, then proves the rest by strong induction after splitting off the final decimal digit.
2. For `145 <= n < 164`, a finite certificate shows that no iterate exceeds `n`. For `n >= 164`, strong induction reduces every orbit to a smaller starting value; the orbit is globally bounded by `max(n,163)`.
3. The orbit of 144 reaches 145 after eight iterations: `144, 33, 18, 65, 61, 37, 58, 89, 145`.

The Lean theorem is `finality (n k : Nat) (hn : 145 ≤ n) : iter k n ≤ n`. A separate Python verifier enumerates the 130 terms through 144.

## Verification

With Lean 4.33.1:

```sh
lean A099649Proof.lean
python3 verify.py
```

The Lean file imports only tactics shipped with Lean itself (`native_decide` and `omega`); Mathlib is not required.
