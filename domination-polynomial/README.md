# A Lean-verified domination-polynomial counterexample

A dominating set of a graph G is a vertex subset such that every vertex outside
it has a neighbor in it. Let d_k(G) count dominating sets of size k. The
Alikhani–Peng conjecture asserts that these counts weakly increase to a mode
and then weakly decrease.

The connected simple graph defined here has indices i<j<k with
**d_i(G)>d_j(G)<d_k(G)**, which disproves the conjecture.
The Lean proof includes the graph definition, exact counting identities,
concentration estimates, and coefficient inequalities.

The canonical graph has **15,211,807,199,220,036,387,538,871,517,957 vertices**.
Adjacency is defined by arithmetic over a finite field. The proof does not
enumerate the graph or its coefficients.

## Conjecture and source

**Alikhani–Peng domination-polynomial unimodality conjecture.** For every finite simple graph, the coefficients of its domination polynomial form a unimodal sequence.

Saeid Alikhani and Yee-hock Peng, [*Introduction to Domination Polynomial of a Graph*](https://arxiv.org/abs/0905.2251), arXiv:0905.2251v1 (2009), Section 3, **unnumbered conjecture on page 7** ([PDF](https://arxiv.org/pdf/0905.2251v1#page=7)). Journal reference: [Ars Combinatoria 114 (2014), 257–266](https://combinatorialpress.com/ars-articles/volume-114-ars-articles/introduction-to-domination-polynomial-of-a-graph/). The quoted formulation is verified against the preprint.

## Theorems

- `Research.DominationCounterexample.canonical_not_unimodal`
- `Research.DominationCounterexample.canonical_connected_counterexample`

Both are closed theorems. Their axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`, the standard Lean foundations used by
mathlib. There are no `sorry` terms or additional research axioms.

The counted objects are all ordinary dominating vertex subsets. Coefficients
include every size from zero through the graph order. Unimodality means weak
increase followed by weak decrease, matching the Alikhani–Peng conjecture.

## Example and plots

![Small graphs from the construction](https://raw.githubusercontent.com/advpropsys/lean-stuff/main/domination-polynomial/figures/graph_example.svg)

The [examples](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/examples/README.md) include the adjacency definition, a plot of
the coefficient bounds, and exact counts for a 14-vertex graph.

## Proof and references

- [Construction and applications](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_package_explanation.md)
- [Complete ordinary proof](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_projective_counterexample_proof.md)
- [Semantic audit of the formal theorem](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_formal_semantic_audit.md)
- [Sources and statement scope](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_novelty_refresh_2026-09-06.md)
- [General transfer argument](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_general_transfer.md)

The [source review](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_novelty_refresh_2026-09-06.md) records the
conjecture's formulation, related constructions, and sufficient theorems.
Publication priority is not certified. The sources have not undergone
external peer review.

## Verify

The project pins Lean **4.29.0** and mathlib commit
`8a178386ffc0f5fef0b77738bb5449d50efeea95` in the included project files.
With the matching Lean/Lake toolchain and pinned dependencies available, run
from this directory:

```sh
lake build Research
lake env lean Audit.lean
python3 verification/check_sources.py
```

[fresh_build.log](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/fresh_build.log)
records successful compilation of every proof module against the pinned dependencies.

[Audit.lean](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Audit.lean) prints the final theorem statements and their axiom dependencies.
The source-check script checks hashes against the recorded source manifest;
hashes alone are not a substitute for the Lean build.

## Smaller constructions and reuse

| Result | Size | Verification scope |
|---|---:|---|
| Canonical projective graph | 15,211,807,199,220,036,387,538,871,517,957 | Complete graph-level Lean proof |
| Smaller projective member | 44,272,117,255,374,666,459,015 | Audited ordinary argument; scalar and analytic bounds also proved in Lean |
| Permutation-based family | At most 7,776,066,000,000,000,000 | Audited existence proof and exact scalar certificate; no qualifying tuple generated |

See the [smaller projective study](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_simplification_study.md) and
[permutation extension](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_permutation_extension.md). Their scripts
are in `experiments/`. They check exact scalar inequalities, not graph searches.
The smaller graph theorems are not fully formalized.

A separate [independence-polynomial corollary](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_independence_reuse.md)
uses the same counting lemmas for the auxiliary graph. Nonunimodal independence examples include
[Bhattacharyya–Kahn's construction](https://arxiv.org/abs/1301.1752).

No faster domination algorithm or engineering application has been established.
