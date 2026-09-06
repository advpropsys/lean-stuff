# Nested-floor error bound (A341239)

For a(n)=⌊(1+√2)⌊√2 n⌋⌋, we prove **1 < (2+√2)n−a(n) < 3 for every positive integer n**.

This is the inequality listed in [OEIS A341239](https://oeis.org/A341239). The complete Lean proof uses the literal nested real-floor definition. It is an elementary identity useful for bounding this particular Beatty-type approximation; no broader algorithmic improvement is claimed.

The September 5, 2026 exact-ID search found no prior explicit proof. Closely related classical Beatty identities may imply it; historical originality is unverified.
[Proof](proof.md) · [Lean sources](Research/) · [Build and audit](REPRODUCE.md) · [Executable example](example.py)
