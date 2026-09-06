# Odd positions in the add-two/double sequence

Start with the ordered generation (1,2). Process each generation from left to right, proposing x+2 then 2x, and retain only first occurrences. In the concatenated sequence, the **one-based position of 2n−1 is n−1+Fₙ₊₁ for every n≥1**.

The operational sequence and its stable prefix positions are formalized directly in `OddPositions.lean`. Source: [A232895](https://oeis.org/A232895), [A232896](https://oeis.org/A232896).

The central Fibonacci tree count and binary characterization were already proved by [Kimberling–Moses (2014)](https://www.mathstat.dal.ca/FQ/Papers1/52-5/Kimberling.pdf). This exact position formula is a short corollary after reducing the seeds/parity. No originality claim is made for the underlying tree theorem. The formula lets one locate odd entries without generating the preceding exponentially growing generations.

[Proof](proof.md) · [Lean sources](Research/) · [Build and audit](REPRODUCE.md) · [Executable example](example.py)
