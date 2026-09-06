# A seven-vertex counterexample to literal integer-budget wording

Take P₇, the path 1–2–3–4–5–6–7, with parts A={2,4,6}, B={1}, C={3,5,7}.
No independent set S admits integer budgets bᵢ≤1 with sum at most 3/2 and |S∩Vᵢ|≥|Vᵢ|/2−bᵢ.

This refutes the literal integer-budget Conjecture 1.6 in [arXiv:1611.03196v1](https://arxiv.org/abs/1611.03196v1) and the inspected [author manuscript](https://web.math.princeton.edu/~nalon/PDFS/fairrep5.pdf). It does **not** refute the different formulation proved by [Alishahi–Meunier (2017)](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i3p41/pdf/).

The final publisher wording and historical priority were not verified. This is a correction to a literal formulation, not an asserted resolution of the intended open problem. The finite P₇ statement, including arbitrary negative integer budgets, is fully proved in Lean.
[Proof](proof.md) · [Lean sources](Research/) · [Build and audit](REPRODUCE.md) · [Executable example](example.py)
