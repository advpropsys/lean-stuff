# Verification

The [connected-counterexample theorem](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Research/DominationCounterexample.lean)
has no research hypotheses. Its [axiom report](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/repository_axioms.log)
contains only `propext`, `Classical.choice`, and `Quot.sound`.

The [build transcript](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/repository_build.log) records compilation
of the graph, counting, concentration, and coefficient-comparison modules.
The [source manifest](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/source_manifest.json) contains the source
hashes. The [requirement table](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/completion_audit.md) states the
verification scope for each result.

The smaller projective and permutation constructions have ordinary proofs
and exact scalar checks. Their graph-level theorems are not formalized in Lean.
