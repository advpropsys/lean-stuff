# Verified reuse: an independence-polynomial valley

The method has now been tested on a second ordinary graph polynomial. This is a reuse demonstration, **not** a new conjecture resolution: independence polynomials of general graphs have long been known to be nonunimodal.

`Research/DominationIndependenceCorollary.lean` proves the closed theorem
`Research.DominationIndependenceCorollary.control_independence_not_unimodal`.
A targeted `lake build Research.DominationIndependenceCorollary` succeeded. Its only axioms are propext, Classical.choice and Quot.sound; it has no hypotheses, new axioms or tactic holes.

The graph is the actual auxiliary `controlGraph`, not the final split graph. Its vertices are the b two-vertex cells and b three-vertex cells, so its order is t=5b=23058430081399521285. The file defines an independent set by requiring every two selected vertices to be nonadjacent in that ordinary graph. The coefficient at k counts **all** such subsets of cardinality k. An explicit equivalence identifies these subsets with the already verified hard control configurations.

The two hard phases already force two separated omission-size bands. For the independence polynomial these are the actual selected-set sizes, so their order is:

- Lower band [0.71b,0.80b], with normalized independent-set count at least 1/2−2^-300.
- Middle index floor(0.86b), outside both bands.
- Upper band [0.92b,1.08b], also with normalized count at least 1/2−2^-300.

The count outside the two bands is at most 2^-300 of all independent sets. There are at most t+1≤2^65 coefficient indices. Consequently each band contains a coefficient larger than the coefficient at the middle index. The generic exact event-to-coefficient theorem proves failure of weak unimodality. There is no need for the clone-noise or soft-penalty steps in this corollary.

This clarifies the mechanism's division of labor. Unequal local size statistics with exactly balanced state multiplicities create a cardinality valley already for independent subsets of the auxiliary graph. The split-graph/clone construction transfers that valley to ordinary dominating sets while suppressing nonindependent control omissions. Thus the same verified phase and coefficient components support two graph-polynomial conclusions; the extra construction is what makes the domination conclusion possible.

This is not an optimized independence example: much smaller examples are known. Its usefulness is the exact reuse of the abstract state-balance, finite-tail, event-bijection and coefficient-valley components, with a separately defined ordinary graph statistic and all transfer hypotheses discharged.
