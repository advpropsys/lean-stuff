# Supporting examples for homogeneous graph coloring

For a finite simple graph, a proper coloring assigns different colors to adjacent vertices. It is 2-homogeneous when each vertex's neighbors have exactly two colors. The proved statements are:

- The complete bipartite graph K₃,₃, with three vertices on each side, requires four colors for a 2-homogeneous coloring. Assigning colors [0,0,1] to one side and [2,2,3] to the other gives such a coloring.
- The Heawood graph, whose vertices are the seven points and seven lines of the Fano plane with edges for incidence, has a proper 2-homogeneous three-coloring. The Fano hypergraph has no property-B coloring: every two-coloring of its points has a monochromatic line.
- If every vertex has two adjacent neighbors, any **given** proper three-coloring is 2-homogeneous.

All three statements are proved in Lean. These are known examples and a conditional lemma; they establish no general coloring bound for arbitrary cubic graphs (graphs with degree three at every vertex). The Heawood example establishes that a monochromatic line in every two-coloring of the Fano points does not prevent a proper 2-homogeneous coloring of its incidence graph.
[Proof](https://github.com/advpropsys/lean-stuff/blob/main/cubic-coloring-examples/proof.md) · [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/cubic-coloring-examples/Research) · [Build and audit](https://github.com/advpropsys/lean-stuff/blob/main/cubic-coloring-examples/REPRODUCE.md) · [Executable example](https://github.com/advpropsys/lean-stuff/blob/main/cubic-coloring-examples/example.py)
