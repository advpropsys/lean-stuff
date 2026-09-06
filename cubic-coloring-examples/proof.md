# Proof explanations

For K₃,₃, properness forces the palettes of the two sides to be disjoint. Every vertex sees the entire opposite side, so each side must use exactly two colors. Four colors are necessary; assigning [0,0,1] on one side and [2,2,3] on the other suffices.

For the Heawood graph, the Lean source lists all fourteen neighborhoods and the coloring [0,0,2,0,2,1,0,1,1,2,2,1,1,0]. The kernel checks properness, degree three and exactly two neighbor colors at each vertex. It separately checks all two-colorings of the seven-point Fano plane and finds a monochromatic line in each.

For the triangle lemma, two adjacent neighbors have different colors by properness, giving at least two neighbor colors. All neighbor colors differ from the vertex's own color. A three-color palette therefore allows at most two. The proper coloring is an explicit input hypothesis; its existence is not asserted.
