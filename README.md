# Lean proofs and mathematical examples

Each result has its own folder with a mathematical statement, proof sources,
an executable example, and a pinned Lean project. The status column distinguishes
complete theorems, corrections to printed statements, and supporting lemmas.

| Result | What is established | Folder |
|---|---|---|
| Cubic homogeneous coloring | Known K₃,₃ and Heawood examples; a conditional triangle lemma. The general conjecture remains unresolved here. | [cubic-coloring-examples](cubic-coloring-examples/) |
| Domination-polynomial unimodality | A connected simple-graph counterexample, with a complete Lean proof. Includes an explicit adjacency rule and plots of certified bounds and exact toy coefficients. | [domination-polynomial](domination-polynomial/) |
| Fair representation with integer budgets | A P₇ counterexample to the literal printed integer-budget formulation. The different formulation proved in 2017 is unaffected. | [fair-representation-p7](fair-representation-p7/) |
| Graph-energy bound | A P₄ counterexample to a printed eigenvalue-ordering bound. The correctly ordered classical bound is unaffected. | [graph-energy-p4](graph-energy-p4/) |
| Alternating Motzkin roots | Strict root log-concavity from index 5, with a counterexample to starting at index 4. Includes the sharp threshold proof and a sequence plot. | [motzkin-root-log-concavity](motzkin-root-log-concavity/) |
| Nested-floor inequality | The A341239 error lies strictly between 1 and 3 for every positive index. | [nested-floor-bound](nested-floor-bound/) |
| Odd-position formula | The A232895 position formula for every positive index; a short corollary of earlier tree results. | [odd-position-formula](odd-position-formula/) |
| Šoltés family obstructions | Two explicit polynomials have no positive integer root. The graph-to-polynomial reduction is not formalized. | [soltes-polynomial-obstructions](soltes-polynomial-obstructions/) |

## Build and reproduce

Every folder is an independent Lake project. All pin Lean **4.29.0** and mathlib
commit `8a178386ffc0f5fef0b77738bb5449d50efeea95`. With that toolchain and the
pinned dependencies installed, enter any result folder and run:

```sh
lake build Research
lake env lean Audit.lean
```

`Audit.lean` prints the theorem statements or axiom dependencies. Compiler
transcripts record verification from the repository copies. The local builds
reuse pinned external dependency caches; local proof modules are compiled in
their individual projects. The caches are not committed.

Each folder explains how to run its examples. Plot scripts include dependency
requirements. An illustrative numerical plot is not a substitute for the
all-index Lean theorem. The domination plot explicitly displays certified
inequalities instead of inventing an exact coefficient curve for a huge graph.

## Scope and provenance

These artifacts were developed with AI assistance and Lean verification. They
have not undergone external peer review. References and antecedents are credited
in the result folders. The dated searches do not certify historical priority,
and known results are labeled accordingly. A successful formal proof establishes
its stated mathematics, not its novelty. No folder claims to settle an unresolved
Erdős problem.
