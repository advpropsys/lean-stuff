# Nested-floor error bound (A341239)

For a(n)=⌊(1+√2)⌊√2 n⌋⌋, **1 < (2+√2)n−a(n) < 3 for every positive integer n**.

This is the inequality listed in [OEIS A341239](https://oeis.org/A341239). The complete Lean proof uses the stated nested real-floor definition. The inequality bounds the error of this Beatty-type approximation; no broader algorithmic improvement is established.

[Proof](https://github.com/advpropsys/lean-stuff/blob/main/nested-floor-bound/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/nested-floor-bound/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/nested-floor-bound/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/nested-floor-bound/example.py)

## Conjecture and source

**Kimberling's nested-floor inequality, OEIS A341239.** Clark Kimberling, [*a(n) = floor(r*floor(s*n)), where r = 1 + sqrt(2) and s = sqrt(2)*](https://oeis.org/A341239), The On-Line Encyclopedia of Integer Sequences, entry authored February 7, 2021. The **Comments** section states the conjecture 1 < r·s·n − a(n) < 3 for n≥1.

The cited source is an OEIS entry, with no numbered paper conjecture. The Lean theorem proves this exact inequality.
