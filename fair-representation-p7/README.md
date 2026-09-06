# A seven-vertex counterexample to literal integer-budget wording

Take P₇, the path 1–2–3–4–5–6–7, and partition its vertices into V₁={2,4,6}, V₂={1}, V₃={3,5,7}. An independent set contains no adjacent pair of vertices.

There is **no independent set S and no triple of integer budgets b₁,b₂,b₃** satisfying all of

- bᵢ≤1 for i=1,2,3;
- b₁+b₂+b₃≤3/2;
- |S∩Vᵢ|≥|Vᵢ|/2−bᵢ for i=1,2,3.

Negative integer budgets are allowed in this statement.

This refutes the literal integer-budget Conjecture 1.6 in [arXiv:1611.03196v1](https://arxiv.org/abs/1611.03196v1) and the inspected [author manuscript](https://web.math.princeton.edu/~nalon/PDFS/fairrep5.pdf). It does **not** refute the different formulation proved by [Alishahi–Meunier (2017)](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v24i3p41/pdf/).

The cited preprint and author manuscript define the scope of this correction. The final publisher wording has not been verified. The finite P₇ statement, including arbitrary negative integer budgets, is fully proved in Lean.
[Proof](https://github.com/advpropsys/lean-stuff/blob/main/fair-representation-p7/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/fair-representation-p7/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/fair-representation-p7/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/fair-representation-p7/example.py)
