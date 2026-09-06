# Sources and statement scope

Primary-source review dated 2026-09-06. Publication priority is not certified;
no authors were contacted.
The canonical Lean counterexample compiles with only standard Lean foundations.
The smaller constructions have separate ordinary analysis and scalar
certificates; they are not the graph of the canonical theorem.

## Finding and intended statement

The sources listed below state ordinary, unweighted domination-polynomial
unimodality as a conjecture. None of these sources gives a counterexample to
that statement. This source review is not an exhaustive priority determination.

For a finite simple graph G, d_k counts all dominating vertex subsets of size k.
The assertion is that for some m the sequence d_0,...,d_n weakly increases up
to m and weakly decreases afterwards. Thus a strict valley d_i>d_j<d_k with
i<j<k disproves it. Connected split graphs, however large, are included.
Auxiliary probability weights in a proof do not make the final graph weighted.

Alikhani–Peng's [preprint](https://arxiv.org/pdf/0905.2251), seventh
PDF page, states: “The domination polynomial of any graph is unimodal.”
It was submitted on 14 May 2009. The journal publication is *Introduction to
Domination Polynomial of a Graph*, Ars Combinatoria 114 (2014), 257–266;
the [publisher record](https://combinatorialpress.com/ars-articles/volume-114-ars-articles/introduction-to-domination-polynomial-of-a-graph/)
records 30 April 2014. Therefore both the 2009 preprint attribution and the
customary 2014 journal attribution are appropriate. The quotation was checked in the preprint. The final publisher PDF could
not be extracted during the search, so its wording has not been checked.

## Primary sources and related results

- Mohamed Omar, [*New Perspectives on the Unimodality of Domination
  Polynomials*](https://arxiv.org/html/2601.14494v1): Conjecture 1 is the
  all-finite-graph assertion. Section 6 asks whether total positivity can
  establish unimodality for split graphs. The threshold-graph theorem is
  narrower. The [history](https://arxiv.org/abs/2601.14494) inspected on 2026-09-06
  lists v1, 20 January 2026; the HTML's internal 24 August 2026 date is not an arXiv revision. Its introduction overstates reference 8
  as covering maximum degree at most 400: the actual cited result covers
  spiders with at most 400 legs, not all graphs of that degree.
- Du–Heilman–Panova, [*Trees and Graphs with Non Log-concave Dominating Set
  Sequence via AI Tools*](https://arxiv.org/html/2605.02193v1), Conjecture 1.1,
  gives precisely the weak-unimodality formulation and says it remains open
  even for trees. The [history](https://arxiv.org/abs/2605.02193) lists
  only v1, 4 May 2026. Its counterexamples, including arbitrarily many
  failing indices, concern log-concavity. These do not supply a valley in
  the ordinary domination sequence.
- [*On domination polynomials of some graphs*](https://combinatorialpress.com/jcmcc-articles/volume-126/on-domination-polynomials-of-some-graphs/)
  concerns generalized friendship graphs and proves log-concavity and
  unimodality there. The paper proves results for those graph families.
- Rather's *Complex zeros, unimodality and log-concavity in independent
  domination polynomial of zero divisor graphs*, DOI
  [10.1016/j.tcs.2025.115594](https://doi.org/10.1016/j.tcs.2025.115594), counts
  independent dominating sets. Search snippets report failures for that
  different polynomial. The publisher abstract fetch returned 403 in this
  refresh; its title specifies the independent-domination polynomial.
  The full text was not checked in this refresh.
- The [16 July 2026 UPEI seminar](https://www.upei.ca/notice/2026/07/smcs-research-seminar-when-are-graph-polynomials-unimodal)
  by Iain Beaton discusses sufficient conditions for upward-closed families
  through their minimal-set clutters. Its abstract announces no domination
  disproof. The scope of unpublished related work remains unknown.

## Antecedents

A related construction is due to Bhattacharyya–Kahn,
[*A bipartite graph with non-unimodal independent set sequence*](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v20i4p11/pdf/),
Electronic Journal of Combinatorics 20(4) (2013), P11, published 28 October.
For their graph G(a,b),

    i_t = (2^t - 1) binom(a,t) + binom(b,t).

They take b approximately a log_2(3), balance the two exponential masses,
and separate their modes at approximately 2a/3 and b/2. Negligible overlap
and concentration produce a valley; a=95, b=151 gives one at indices
70,71,72. They also explain multiple peaks. This construction balances phase masses and obtains a valley from separated
concentrated phases. Its polynomial counts independent sets, so its conclusion
does not refute Alikhani–Peng.

The closed-neighborhood hypergraph/complement identity is also standard;
Omar explicitly identifies it as such. This package makes no individual
novelty claim for projective-plane incidence expansion, hard-core phase
separation, finite clone gadgets, Chernoff/Hoeffding bounds, exponential
weighting, or the interval-mass pigeonhole argument.

The construction combines: an explicit finite
connected split graph whose degree-two edge cohorts implement a sufficiently
small soft penalty; local independent states with equal counts but different
size distributions; sparse symmetric incidence constraints keeping mixed
phases small; and estimates showing the resulting ordinary domination
coefficients retain a strict valley despite optional-cohort noise. No matching domination counterexample was located in the listed sources.
This does not establish publication priority for the construction or its components.

## Why the checked sufficient theorems do not cover this graph

The graph fails the following sufficient hypotheses.
Every cohort has degree two, so the high-minimum-degree hypothesis in
[Beaton–Brown](https://arxiv.org/html/2012.11813) fails. No control is universal:
it is nonadjacent to cohorts on an edge of another right-cell triangle. Cohorts are not
universal either, so [Zhang's universal-vertex theorem](https://arxiv.org/abs/2111.00641)
does not apply. Choosing cohorts on two disjoint underlying edges and one
endpoint from each gives an induced P4, excluding threshold graphs. All
cohorts together form a minimal dominating set, giving upper domination
number at least L and excluding the low-upper-domination criterion of
[Burcroff–O'Brien](https://www.sciencedirect.com/science/article/pii/S0012365X23001942).

Repeated cohorts share an open neighborhood {u,v}; their closed neighborhoods
{u,v,z} are distinct. No general degree-two false-twin preservation theorem
was found. This is a search result, not a claim that no such theorem exists.
The counterexample cannot satisfy the hypotheses of a valid sufficient
criterion for unimodality. This alone does not identify which other graph
classes satisfy an improved neighborhood-overlap criterion.

## Search scope and concrete priority limits

The search queries combined “domination polynomial” with non-unimodal,
nonunimodal, counterexample, disproof, split graph(s), twins, edge clones,
expander, phase, clique, independent sets, Alikhani, Peng, 2026, and September.
Relevant hits were checked against arXiv papers and histories, publisher
papers, and the institutional seminar announcement.
Searches produced unrelated independent-domination, independence-polynomial,
log-concavity, average-polynomial and graph-complexity hits; those are not
ordinary-domination disproofs. No broad computation was performed.

The audit is limited by index coverage, inaccessible full text, publication
lag, unpublished or privately circulated manuscripts, and concurrent work.
The specific July seminar is one reason not to treat the public record as a
complete inventory. It has not established an exhaustive citation genealogy
for every gadget or probability argument. Independent mathematical review
and publication priority remain distinct from the completed canonical Lean
proof: kernel verification establishes its formal statement, not historical
novelty, bibliographic completeness, or priority. No authors were contacted. Repository publication does not establish priority.
