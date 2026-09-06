# Why a counting sequence can have two peaks

Review explanation for a mathematical audience, 2026-09-06. The full canonical
counterexample theorem passes Lean, including the graph, counting and numerical
estimates. A fresh build of the copied sources also passed. Publication priority
has not been established by the literature search.

A dominating set is a selection of vertices that reaches the whole graph:
every unselected vertex has a selected neighbor. Let d_k count the selections
of size k. The Alikhani–Peng conjecture says that d_0,d_1,...,d_n first weakly
increase and then weakly decrease. A strict dip between two larger entries
would refute it.

The construction creates two large classes of valid selections. The classes
have comparable total counts, but their selections have different typical
sizes. The proof then bounds the number of selections between those sizes.
This is the feature that matters; simply finding two visually different kinds
of selections would not prove anything about the full counting sequence.

The local design is small. Two independent vertices have four independent
subsets: one empty, two of size one, and one of size two. A triangle also has
four independent subsets: one empty and three of size one. There are equally
many choices in both gadgets, but a uniform choice has mean size one in the
first gadget and three quarters in the second.

Many copies are connected using projective-plane incidence. Its expansion
property prevents substantial occupation on both sides at once. Swapping
the two sides preserves the number of configurations because each occupied
cell has three internal choices. It changes the typical number of selected
controls. This gives two equally numerous classes with different sizes.

To turn this independent-set picture into ordinary domination, make all
controls a clique. For every edge of the auxiliary graph, add a group of
vertices adjacent exactly to its two endpoints. Omitting both endpoints
forces every vertex of that group into a dominating set. Each such omission
therefore loses many optional choices. An exact finite bound controls the
combined contribution of every configuration containing an auxiliary edge.

The optional vertices add binomial noise. The graph parameters make the
separation between the two classes much larger than this noise. A final
counting argument proves a strict coefficient dip. No full adjacency list
or full coefficient sequence needs to be computed.

The original explicit example has about 1.52×10^31 vertices. An analytically
improved member has 44,272,117,255,374,666,459,015 vertices, over 343 million
times fewer. Its changed ordinary estimates were independently checked and
all 33 scalar certificate checks passed. It still awaits a complete graph-level
Lean proof. Neither size is a lower bound on the size of a counterexample.
See [the simplification study](domination_simplification_study.md).

A second construction uses symmetric collections of permutations in place of
projective geometry. Its ordinary proof guarantees a counterexample with at
most 7,776,066,000,000,000,000 vertices. All 36 scalar checks passed independently.
The proof establishes existence of a suitable permutation collection; no such
collection was generated, and this extension is not yet a full Lean theorem.
See [the alternate construction](domination_permutation_extension.md).

## Why this could matter

The canonical theorem supplies a counterexample to the specific conjecture,
already within connected split graphs. The novelty audit found no earlier
ordinary-domination disproof. Recent work
still develops approaches to that conjecture, including
[Omar's 2026 paper](https://arxiv.org/abs/2601.14494). That supports a claim of
specialist relevance, rather than a prediction of broad publicity.

The wider opportunity is a construction principle: balance the numbers of
local choices while separating their sizes, enforce distinct classes with
expansion, and control the finite penalties and added noise. A general theorem
would tell other researchers exactly when this strategy produces a coefficient
valley. We have tested reuse: a separate closed Lean theorem proves that the
auxiliary graph's independence polynomial is nonunimodal, using the same phase
and count components. This is a known possible phenomenon for independence
polynomials, not a second new conjecture resolution.

The broad balanced-phase idea has a direct antecedent in Bhattacharyya and
Kahn's 2013 paper, [*A bipartite graph with non-unimodal independent set
sequence*](https://arxiv.org/abs/1301.1752). The specific contribution assessed
here is the finite transfer to ordinary domination coefficients and the
verified counterexample, not the invention of balanced phases.

There is existing work connecting domination polynomials with other graph
polynomials and statistical models. For example, Dod, Kotek, Preen, and
Tittmann's 2015 paper *Bipartition Polynomials, the Ising Model, and Domination
in Graphs* gives a common polynomial generalization
([DOI](https://doi.org/10.7151/dmgt.1808)). We should not claim that this broad
connection is our discovery. The narrower question is whether our finite
construction and strict-valley transfer are new and useful.

## Initial usefulness assessment

| Audience | Potential benefit | Evidence and limits |
|---|---|---|
| Graph-polynomial researchers | Settle an active conjecture and identify a concrete obstruction to unimodality | Closed canonical Lean theorem; no earlier disproof found in the dated audit |
| Enumerative and probabilistic combinatorialists | Reuse balanced local choices and quantitative error bounds | Verified independence-polynomial reuse and an alternate permutation construction; no second new conjecture claim |
| Formal mathematics researchers | Reusable domination counting, finite tails, and incidence-expansion components | A copied source package builds from fresh local proof artifacts; external dependency caches were reused |
| Algorithm researchers | A possible structured test family for counting or sampling methods | No actual algorithmic consequence is currently established |
| Broader mathematical audience | A short, understandable statement and an auditable discovery process | Clear exposition that separates construction, proof, and verification |

The present result does not establish a faster domination algorithm or an
engineering application. A large artificial counterexample can still be
mathematically valuable because it settles a universal claim. A smaller
example would improve inspectability and computational use; a reusable theorem
would provide stronger evidence of broader mathematical value.

The priority is correctness, followed by simplicity and demonstrable reuse.
Publicity is an uncertain consequence, not a verification criterion.

## Which existing work is affected?

A targeted public-source search on 2026-09-06 found no established algorithm
or downstream theorem whose correctness relies on the universal conjecture.
A hypothetical optimization shortcut is not evidence of a deployed use.

[Galvin–Zhang](https://arxiv.org/abs/2408.12731) proves unimodality for powers
of paths and cycles; this restricted theorem is unaffected.
[Mertens](https://cs.uwaterloo.ca/journals/JIS/VOL27/Mertens2/mertens12.pdf)
computes domination polynomials by exact transfer-state recurrences; that
algorithm does not assume unimodality.
[Omar, Section 6](https://arxiv.org/html/2601.14494v1#S6) asks about extending
unimodality to split graphs. The present split-graph counterexample rules out
a universal extension of that kind. This answers a proposed research question
rather than invalidating the narrower threshold-graph theorem.
