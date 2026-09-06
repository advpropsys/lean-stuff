# Construction and applications

The canonical connected-graph counterexample has a complete Lean proof.
The graph, counting identities, and numerical estimates were verified in a
separate build of the copied sources on 2026-09-06. Historical priority remains
unverified.

## Construction

A dominating set is a vertex subset such that every vertex outside it has a
neighbor in it. Let d_k count dominating sets of size k. The Alikhani–Peng
conjecture asserts that d_0,d_1,...,d_n weakly increases to a mode and then
weakly decreases. Indices i<j<k with d_i>d_j<d_k refute the conjecture.

The proof bounds the sizes of two classes of dominating sets. Both classes
contain a substantial fraction of all dominating sets, while few dominating
sets have sizes between the two classes.

The auxiliary graph uses two kinds of cells. An independent pair has four
independent subsets: one empty, two of size one, and one of size two. A
triangle also has four independent subsets: one empty and three of size one.
The mean sizes of uniformly chosen independent subsets are therefore one
and three quarters, respectively.

Cross edges between cells are determined by projective-plane incidence.
Expansion bounds the number of configurations with many occupied cells on
both sides. Each occupied cell has three possible nonempty independent
subsets. Swapping the two sides preserves the number of configurations but
changes their size distribution.

The final graph has a complete subgraph on the auxiliary vertices, called
controls. For every auxiliary edge, it has a group of new vertices, each
adjacent only to the edge's endpoints. These new vertices are called clones.
If both endpoints are omitted from a dominating set, every clone in that
group must be selected. The number of completions decreases accordingly.
A finite counting bound controls the total contribution from omitted-control
sets containing auxiliary edges.

For an independent omitted-control set, clone selections are unrestricted.
Their total size has a binomial distribution. The parameters ensure that its
deviations are small relative to the separation of the two size classes.
Bounds on these deviations and the exceptional configurations imply a strict
valley in the domination coefficients.

## Graph sizes and verification

The canonical example has about 1.52×10^31 vertices. The complete graph-level
Lean proof applies to this example.

A [smaller projective member](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_simplification_study.md) has
44,272,117,255,374,666,459,015 vertices, over 343 million times fewer. Its
ordinary proof and 33 scalar checks passed. The scalar and analytic bounds
are also formalized; the full graph-level theorem is not.

A [permutation construction](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_permutation_extension.md) proves
existence of a counterexample with at most 7,776,066,000,000,000,000 vertices.
All 36 scalar checks passed. No qualifying permutation tuple was generated,
and this graph theorem is not formalized in Lean. Neither construction
establishes a minimum counterexample order.

## Consequences and references

The counterexample is a connected split graph. It therefore rules out the
extension of universal unimodality to split graphs proposed in
[Omar, Section 6](https://arxiv.org/html/2601.14494v1#S6). The narrower
threshold-graph theorem is unaffected.

A separate [Lean corollary](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_independence_reuse.md) proves that the
auxiliary graph's independence polynomial is nonunimodal. It uses the same
state-counting and concentration lemmas. A balanced-phase construction of a nonunimodal independence polynomial
is given in
Bhattacharyya–Kahn's 2013 paper,
[*A bipartite graph with non-unimodal independent set sequence*](https://arxiv.org/abs/1301.1752).
The result here transfers finite counting bounds to ordinary domination
coefficients. Publication priority is not certified.

A connection between domination polynomials and statistical models is given
in Dod, Kotek, Preen, and Tittmann's 2015 paper,
*Bipartition Polynomials, the Ising Model, and Domination in Graphs*, gives a
common polynomial generalization ([DOI](https://doi.org/10.7151/dmgt.1808)).

## Algorithmic impact

A source search on 2026-09-06 identified no established algorithm or downstream
theorem that assumes universal domination-polynomial unimodality. No practical
speedup or engineering application has been demonstrated.

[Galvin–Zhang](https://arxiv.org/abs/2408.12731) proves unimodality for powers
of paths and cycles. That restricted result remains valid.
[Mertens's counting algorithm](https://cs.uwaterloo.ca/journals/JIS/VOL27/Mertens2/mertens12.pdf)
uses exact transfer-state recurrences and does not assume unimodality.
