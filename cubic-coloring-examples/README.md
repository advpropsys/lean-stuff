# Supporting examples for homogeneous graph coloring

A proper coloring is 2-homogeneous when each vertex sees exactly two colors among its neighbors. This folder proves:

- K₃,₃ requires four colors and has an explicit valid four-coloring.
- The Heawood (Fano incidence) graph has a valid three-coloring, even though the Fano hypergraph has no property-B coloring.
- If every vertex has two adjacent neighbors, any **given** proper three-coloring is 2-homogeneous.

These are known/supporting examples and a conditional lemma. They do not solve the general cubic-graph coloring conjecture. The Heawood example shows why failure of a restricted palette method cannot be treated as a graph counterexample.
[Proof](proof.md) · [Lean sources](Research/) · [Build and audit](REPRODUCE.md) · [Executable example](example.py)
