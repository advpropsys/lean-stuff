# P₄ refutes a printed spectral-energy bound

For a graph G with n vertices, m edges and adjacency eigenvalues λ₁≥⋯≥λₙ, its energy is E(G)=∑ᵢ|λᵢ|. The bound printed in Remark 1 of Jahanbani–Gutman (2025) is

E(G)≥√(2mn−n²(λ₁−|λₙ|)²/4).

The path P₄, with vertices 1–2–3–4 and three edges, has eigenvalues a,b,−b,−a, where a=(√5+1)/2 and b=(√5−1)/2. Its energy is 2√5, so its energy squared is **20**. The printed bound requires at least **24**, since λ₁=|λ₄|. This is a counterexample even among connected graphs with nonsingular adjacency matrices.

This is a correction to the bound **as printed**, not a disproof of the correctly ordered classical bound or the paper's separate conjecture. The defect is using the smallest signed eigenvalue where the classical bound uses the smallest absolute eigenvalue. The repaired inequality is exact on P₄.

Lean verifies the graph, adjacency matrix, characteristic polynomial, full root multiset and contradiction. Source: [DOI 10.30538/oms2025.0261](https://doi.org/10.30538/oms2025.0261).
[Proof](https://github.com/advpropsys/lean-stuff/blob/main/graph-energy-p4/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/graph-energy-p4/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/graph-energy-p4/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/graph-energy-p4/example.py)
