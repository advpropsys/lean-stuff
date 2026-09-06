# Proof explanations

In a finite simple graph, a proper coloring assigns different colors to adjacent vertices. A proper coloring is 2-homogeneous if each vertex's neighbors have exactly two colors.

For K₃,₃, properness requires disjoint palettes on the two sides. Each vertex is adjacent to every vertex on the opposite side, so 2-homogeneity requires exactly two colors on each side. Four colors are necessary; assigning [0,0,1] on one side and [2,2,3] on the other suffices.

For the Heawood graph, the Lean source lists all fourteen neighborhoods and the coloring [0,0,2,0,2,1,0,1,1,2,2,1,1,0]. The kernel checks properness, degree three and exactly two neighbor colors at each vertex. Exhaustive kernel-checked enumeration establishes that every two-coloring of the seven-point Fano plane has a monochromatic line.

For the triangle lemma, two adjacent neighbors have different colors by properness, giving at least two neighbor colors. All neighbor colors differ from the vertex's own color. A three-color palette therefore allows at most two. The proper coloring is an explicit input hypothesis; its existence is not asserted.
