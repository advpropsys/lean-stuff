# Lean proofs and mathematical examples

Each result in [advpropsys/lean-stuff](https://github.com/advpropsys/lean-stuff) has its own folder with a mathematical statement, proof sources,
an executable example, and a pinned Lean project. The table distinguishes
complete theorems, corrections to printed statements, and supporting lemmas.
Each result README gives the authors, source title, and exact conjecture or problem location.

| Result | What is established | Source | Folder |
|---|---|---|---|
| Cubic homogeneous coloring | Known K₃,₃ and Heawood examples; a conditional triangle lemma. No general bound for arbitrary cubic graphs is established. | [Lužar–Soták, Problem 5.1 (2025)](https://arxiv.org/html/2511.02892v1#S5) | [cubic-coloring-examples](https://github.com/advpropsys/lean-stuff/tree/main/cubic-coloring-examples) |
| Domination-polynomial unimodality | A connected simple-graph counterexample, with a complete Lean proof. Includes an explicit adjacency rule and plots of certified bounds and exact toy coefficients. | [Alikhani–Peng, unnumbered conjecture (2009; journal 2014)](https://arxiv.org/pdf/0905.2251v1#page=7) | [domination-polynomial](https://github.com/advpropsys/lean-stuff/tree/main/domination-polynomial) |
| Fair representation with integer budgets | A P₇ counterexample to the literal printed integer-budget formulation. The different formulation proved in 2017 is unaffected. | [Aharoni et al., Conjecture 1.6 (2016 preprint)](https://arxiv.org/pdf/1611.03196v1#page=3) | [fair-representation-p7](https://github.com/advpropsys/lean-stuff/tree/main/fair-representation-p7) |
| Graph-energy bound | A P₄ counterexample to a printed eigenvalue-ordering bound. The correctly ordered classical bound is unaffected. | [Jahanbani–Gutman, Remark 1 (2025)](https://pisrt.org/psrpress/j/oms/2025/exact-variance-energy-relations-and-optimal-spectral-bounds-for-graphs.pdf#page=2) | [graph-energy-p4](https://github.com/advpropsys/lean-stuff/tree/main/graph-energy-p4) |
| Alternating Motzkin roots | Strict root log-concavity from index 5, with a counterexample to starting at index 4. Includes the sharp threshold proof and a sequence plot. | [Zhao, Conjecture 1 (2026)](https://math.colgate.edu/~integers/aa55/aa55.pdf#page=8) | [motzkin-root-log-concavity](https://github.com/advpropsys/lean-stuff/tree/main/motzkin-root-log-concavity) |
| Nested-floor inequality | The A341239 error lies strictly between 1 and 3 for every positive index. | [Kimberling, OEIS A341239 (2021)](https://oeis.org/A341239) | [nested-floor-bound](https://github.com/advpropsys/lean-stuff/tree/main/nested-floor-bound) |
| Odd-position formula | The A232895 position formula for every positive index; a corollary of [Kimberling–Moses's tree theorem](https://www.mathstat.dal.ca/FQ/Papers1/52-5/Kimberling.pdf). | [Kimberling, OEIS A232896 (2013)](https://oeis.org/A232896) | [odd-position-formula](https://github.com/advpropsys/lean-stuff/tree/main/odd-position-formula) |
| Šoltés family obstructions | Two explicit polynomials have no positive integer root. The graph-to-polynomial reduction is not formalized. | [Šoltés, unnumbered problem (1991)](https://dml.cz/handle/10338.dmlcz/132387) | [soltes-polynomial-obstructions](https://github.com/advpropsys/lean-stuff/tree/main/soltes-polynomial-obstructions) |

## Build and reproduce

Every folder is an independent Lake project. All pin Lean **4.29.0** and mathlib
commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. With that toolchain and the
pinned dependencies installed, enter any result folder and run:

```sh
lake build Research
lake env lean Audit.lean
```

[Audit.lean](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Audit.lean) prints the theorem statements or axiom dependencies. Compiler
transcripts in each result folder record successful compilation and axiom checks.

Each folder explains how to run its examples. Plot scripts include dependency
requirements and use bundled Inter fonts with sentence-case labels. Figures
are exported as 600-dpi PNGs and vector SVG/PDF files. Keep the full repository
checkout to regenerate plots, which share [plot_style.py](https://github.com/advpropsys/lean-stuff/blob/main/plot_style.py) and `assets/fonts/`.
Plots illustrate the results; the Lean theorems establish the stated conclusions.
The domination plot displays certified coefficient bounds and separately labeled
exact coefficients for a small example.

## Scope and provenance

These artifacts were developed with AI assistance and Lean verification. They
have not undergone external peer review. Each result includes source attribution
and verification scope. A successful formal proof establishes its stated
mathematics, not its novelty. None of these results settles an unresolved Erdős
problem.

## Citation

Konstantin Korolev (Whitecircle).

```bibtex
@misc{korolev2026leanstuff,
  author = {Korolev, Konstantin},
  title = {Lean proofs and mathematical examples},
  year = {2026},
  note = {Affiliation: Whitecircle},
  url = {https://github.com/advpropsys/lean-stuff}
}
```
