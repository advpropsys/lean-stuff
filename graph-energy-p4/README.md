# P₄ refutes a printed spectral-energy bound

The four-vertex path has energy squared **20**, while Remark 1 in Jahanbani–Gutman (2025) demands at least **24** under the paper's signed eigenvalue order.

This is a correction to the bound **as printed**, not a disproof of the correctly ordered classical bound or the paper's separate conjecture. The defect is using the smallest signed eigenvalue where the classical bound uses the smallest absolute eigenvalue. The repaired inequality is exact on P₄.

Lean verifies the actual graph, adjacency matrix, characteristic polynomial, full root multiset and contradiction. Source: [DOI 10.30538/oms2025.0261](https://doi.org/10.30538/oms2025.0261). No priority is certified for this correction.
[Proof](proof.md) · [Lean sources](Research/) · [Build and audit](REPRODUCE.md) · [Executable example](example.py)
