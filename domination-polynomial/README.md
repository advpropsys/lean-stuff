# A Lean-verified domination-polynomial counterexample

The explicitly defined connected simple graph in this package has an ordinary
domination sequence that is not unimodal. The complete proof compiles in Lean;
it does not assume the coefficient valley, projective geometry, counting
identities, concentration estimates, or numerical inequalities.

The canonical graph has **15,211,807,199,220,036,387,538,871,517,957 vertices**.
Its finite-field adjacency rule is succinct. No full graph or coefficient list
was enumerated.

## Main results

- `Research.DominationCounterexample.canonical_not_unimodal`
- `Research.DominationCounterexample.canonical_connected_counterexample`

Both are closed theorems. Their axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`, the standard Lean foundations used by
mathlib. There are no `sorry` terms or additional research axioms.

The counted objects are all ordinary dominating vertex subsets. Coefficients
include every size from zero through the graph order. Unimodality means weak
increase followed by weak decrease, matching the Alikhani–Peng conjecture.

## Example and plots

See [the reproducible examples](examples/README.md) for the finite-field
construction, the certified bounds for the actual counterexample, and a
computable small illustration.

## Read the argument

- [Accessible explanation and usefulness assessment](docs/domination_package_explanation.md)
- [Complete ordinary proof](docs/domination_projective_counterexample_proof.md)
- [Semantic audit of the formal theorem](docs/domination_formal_semantic_audit.md)
- [Current literature and novelty audit](docs/domination_novelty_refresh_2026-09-06.md)
- [General transfer argument](docs/domination_general_transfer.md)

The source search found no earlier ordinary-domination disproof. It does not
certify publication priority or rule out unpublished work. The broader idea of
balanced coefficient phases has prior literature, explicitly credited in the
novelty audit. This repository publishes the proof artifacts; no journal submission or external
peer review is claimed.

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

The project was also tested from a separate copied source
directory with no pre-existing local Research build artifacts. That test reused
the pinned external dependency caches, compiled all local proof modules, and
passed. The transcript is in `verification/fresh_build.log`.

`Audit.lean` prints the final theorem statements and their axiom dependencies.
The source-check script checks hashes against the recorded source manifest;
hashes alone are not a substitute for the Lean build.

## Smaller constructions and reuse

| Result | Size | Verification scope |
|---|---:|---|
| Canonical projective graph | 15,211,807,199,220,036,387,538,871,517,957 | Complete graph-level Lean proof |
| Smaller projective member | 44,272,117,255,374,666,459,015 | Audited ordinary argument; scalar and analytic bounds also proved in Lean |
| Permutation-based family | At most 7,776,066,000,000,000,000 | Audited existence proof and exact scalar certificate; no qualifying tuple generated |

See the [smaller projective study](docs/domination_simplification_study.md) and
[permutation extension](docs/domination_permutation_extension.md). Their scripts
are in `experiments/`. They check exact scalar inequalities, not graph searches.
The smaller graph theorems are not claimed as fully formalized.

A separate [independence-polynomial corollary](docs/domination_independence_reuse.md)
tests reuse of the proof components on a second ordinary graph statistic.
That phenomenon is already known in the literature; this is a verified reuse
demonstration, not a claim to resolve another open conjecture.

The principal demonstrated value is mathematical and formal: an exact
counterexample, a reproducible proof, and reusable counting components.
No faster practical domination algorithm or engineering application is claimed.
