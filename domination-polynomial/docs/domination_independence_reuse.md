# Nonunimodal independence polynomial of the auxiliary graph

The auxiliary graph has a nonunimodal independence polynomial. This corollary uses the counting lemmas from the domination proof. For another nonunimodal independence polynomial, see [Bhattacharyya–Kahn](https://arxiv.org/abs/1301.1752).

[DominationIndependenceCorollary.lean](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Research/DominationIndependenceCorollary.lean) proves the closed theorem
`Research.DominationIndependenceCorollary.control_independence_not_unimodal`.
A targeted `lake build Research.DominationIndependenceCorollary` succeeded. Its only axioms are propext, Classical.choice and Quot.sound; it has no hypotheses, new axioms or tactic holes.

The graph is the auxiliary `controlGraph`. Set q=2147483647 and b=q²+q+1. The graph has b two-vertex cells and b three-vertex cells, so its order is t=5b=23058430081399521285. The edges are defined in the [projective construction](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_projective_counterexample_proof.md). The file defines an independent set by requiring every two selected vertices to be nonadjacent in that ordinary graph. The coefficient at k counts **all** such subsets of cardinality k. An explicit equivalence identifies these subsets with the hard control configurations.

The hard-phase estimates give two separated omission-size bands. For the independence polynomial these are the actual selected-set sizes, so their order is:

- Lower band [0.71b,0.80b], with normalized independent-set count at least 1/2−2^-300.
- Middle index floor(0.86b), outside both bands.
- Upper band [0.92b,1.08b], also with normalized count at least 1/2−2^-300.

The count outside the two bands is at most 2^-300 of all independent sets. There are at most t+1≤2^65 coefficient indices. Consequently each band contains a coefficient larger than the coefficient at the middle index. The generic exact event-to-coefficient theorem proves failure of weak unimodality. There is no need for the clone-noise or soft-penalty steps in this corollary.

The state-balance, finite-tail, and coefficient-counting lemmas apply to both
polynomials. The domination proof also requires the clone and finite-penalty
estimates. Smaller nonunimodal independence examples are known; this corollary
establishes reuse of the formal lemmas without minimizing graph order.
