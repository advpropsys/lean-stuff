# A four-vertex counterexample to a published bound as written

Jahanbani and Gutman, *Exact variance-energy relations and optimal spectral bounds for graphs*, Open Journal of Mathematical Sciences 9 (2025), 301–307, DOI [10.30538/oms2025.0261](https://doi.org/10.30538/oms2025.0261), order adjacency eigenvalues as λ₁ ≥ ⋯ ≥ λₙ. Their Remark 1, p.302, asserts

\[
 E(G)\ge\sqrt{2mn-\frac{n^2}{4}(\lambda_1-|\lambda_n|)^2}.
\]

This statement is false for the connected nonsingular path P₄. Its adjacency matrix is

\[
 A=\begin{pmatrix}0&1&0&0\\1&0&1&0\\0&1&0&1\\0&0&1&0\end{pmatrix}.
\]

Its characteristic polynomial factors as

\[
 \det(xI-A)=x^4-3x^2+1=(x^2-x-1)(x^2+x-1).
\]

Let a=(√5+1)/2 and b=(√5−1)/2. Both are positive and a>b. The complete spectrum is a,b,−b,−a. Consequently E(P₄)=2(a+b)=2√5 and λ₁=|λ₄|=a. Since n=4 and m=3, the displayed claim would require

\[
 2\sqrt5\ge\sqrt{24},
\]

which is impossible because 20<24. Also det(A)=1, so nonsingularity does not repair this example.

The defect is an eigenvalue-ordering error. The paper's cited [2014 source](https://match.pmf.kg.ac.rs/electronic_versions/Match72/n1/match72n1_179-182.pdf) orders **absolute** eigenvalues, and proves the corresponding valid inequality. The correct range is λ₁−minᵢ|λᵢ|, which equals 1 for P₄ and makes the repaired bound exact. Thus this is an error in the 2025 statement, not a disproof of the correctly formulated classical bound.

The separate Conjecture 1 in the 2025 paper is unaffected; [arXiv:2608.22139](https://arxiv.org/abs/2608.22139) supplies a recent proof. Targeted searches located no prior correction of Remark 1, but that does not establish novelty.

The Lean certificate [P4EnergyCounterexample.lean](Research/P4EnergyCounterexample.lean) verifies the graph, connectivity, edge count, adjacency matrix, characteristic polynomial, complete root multiset, root extrema, determinant, energy, and failure of the graph-level bound. Its only axioms are Lean's standard propext, Classical.choice, and Quot.sound.
