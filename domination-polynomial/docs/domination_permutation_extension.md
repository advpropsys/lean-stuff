# Symmetric-permutation extension: complete numerical existence certificate

This is an ordinary-proof extension of the audited domination construction.
It does not modify the canonical projective graph or its Lean proof. No
permutation tuple has been generated. The output is existence of a finite
simple connected graph, with an unambiguous but computationally impractical
lexicographically first description if desired.

Take

- `b = 240000000000`, `d = 30000`, `w = 90`;
- `epsilon = 1/1500`, `k = b/1500 = 160000000`;
- left omission deviation `a = 2/25`, right deviation `c = 57/1000`;
- clone deviation `r = 11/200`.

The resulting graph has order at most
`7776066000000000000 < 2^63`.
This is at least 5693 times smaller than the previously audited projective
member of order `44272117255374666459015`.

## 1. Exact auxiliary existence proof

Choose d independent uniform permutations of [b]. On two labeled copies of
[b], put an edge `(i,j)` whenever some permutation sends i to j or j to i.
Collapse duplicate edges. This defines a simple bipartite graph B with a
symmetric adjacency matrix and degree at most 2d. A diagonal matrix entry is
an ordinary edge between the two different copies, not a loop. Every vertex
has a neighbor.

For fixed sets S,T of size k, one permutation avoids all arrows from S to T
with probability

`(b-k)_k / (b)_k <= (1-k/b)^k <= exp(-k^2/b)`.

If the symmetrized graph has no edge between S and T, all d permutations
avoid these arrows. Thus the probability of any such empty rectangle is at
most

`binom(b,k)^2 exp(-d k^2/b)`.

Use `binom(b,k) <= (eb/k)^k` and `ln(1500) < 8`. The latter follows from
`e > 65/24 > 27/10` and the exact integer comparison
`27^8 > 1500 * 10^8`. The logarithm of the union bound is strictly less than

`18k - d k^2/b = -b/750 < 0`.

Consequently there exists a tuple for which every two sets of size at least
k have an edge. Larger empty sets would contain an empty k-by-k rectangle.
Symmetry is exact, not probabilistic, because each permutation was included
with its transpose.

A definite finite choice is the lexicographically first d-tuple of
permutations having this property, under the ordinary order on their image
lists. Existence makes this definition total. The certificate neither lists
that tuple nor claims efficient adjacency evaluation.

## 2. Actual graph and order bounds

Apply the same construction as in the projective manuscript: left cells
are independent pairs, right cells are triangles; each B-edge supplies all
six cross edges. Call this incidence graph F. Its t=5b vertices are the
controls. There are

`m = 3b + 6 |E(B)|`, so `3b <= m <= b(12d+3)`.

Make the controls a clique. For every edge of F add w distinct independent
clone vertices, adjacent exactly to that edge's endpoints. The resulting
graph is simple and connected. Duplicate permutation arrows have already
been collapsed; the indexed clones remain distinct graph vertices. All
controls have an incident F-edge, as required by the domination partition.

Write `L=wm`, `n=t+L`, and `K=t+L/2`. Because w is even, K is an integer for
every possible qualifying tuple. In particular,

`L <= 7776064800000000000`,
`n <= 7776066000000000000`.

We do not assert equality: overlapping permutation arrows can reduce m.
All subsequent estimates use the upper bound for L and are uniform over
all qualifying tuples.

## 3. Hard phase and finite-penalty errors

An omitted-control subset P has weight `2^(-w e_F(P))`. Independent P are
the hard states. The three nonempty states of a left pair and the three
singleton states of a right triangle give equal activity 3 on B. Symmetry
of B therefore gives an exact bijection exchanging the two hard phases.
The disperser condition makes the phases, defined by at least k occupied
cells on the indicated side, disjoint.

For either minority side, its weighted configuration count is bounded by

`T = sum_(j<=epsilon b) binom(b,j) 3^j <= exp(E b)`,
`E = 19/3000`.

This follows from the entropy bound
`h(epsilon)+epsilon ln 3 <= epsilon(1+ln(3/epsilon))`
and `ln 4500 < 17/2`. The latter is certified by
`27^17 > 4500^2 * 10^17` and `e>27/10`.

The left unrestricted microstates are uniform subsets of 2b controls, so
the omission-size tail beyond `a b` from b is at most `2 exp(-a^2 b)`.
The right microstates give Bin(b,3/4), whose deviation beyond `c b` has
probability at most `2 exp(-2c^2 b)`. Multiplying by the minority count and
dividing by the hard partition function, at least `4^b`, gives the hard
phase estimates used in the manuscript. The both-small remainder is at
most `T^2/4^b`. Exact rational comparisons give

`a^2-E >= 1/15000`,
`2c^2-E >= 1/15000`,
`1-2E >= 1/15000`.

Hence the total hard exceptional fraction is at most
`5 exp(-b/15000) < 2^-100`, since `b/15000 > 110`, `e>2`, and
`5*2^-110 < 2^-100`. Each good hard phase has fraction greater than
`1/2 - 2^-100`.

The cleanup injection, valid for this actual F, gives
`Zsoft/Zhard <= (1+rho)^t` with `rho=2^-90`.
For `x=t rho<1/2`, the elementary estimates
`(1+rho)^t <= exp(x) <= 1/(1-x) <= 1+2x`
imply actual nonhard mass at most `2t rho < 2^-48`.

Conditional on any hard P, all L clones are independent fair choices.
Hoeffding gives clone deviation beyond `r b` probability at most

`2 exp(-2 r^2 b^2/L)`.

Using the maximum L, the exponent is at least
`2 r^2 b/[w(12d+3)] > 42`.
The exact rational comparison `2(10/27)^42 < 2^-59` certifies a noise error
less than `2^-59`.

Thus actual outside-good mass is less than

`2^-48 + 2^-100 + 2^-59 < 2^-47`.

Each good phase with good clone count has actual mass greater than

`(1-2^-48)(1/2-2^-100)(1-2^-59) > 1/3`.

## 4. Integer coefficient valley

The good hard omission bands are

- left: `[(1-a)b, (1+a+epsilon)b]`;
- right: `[(3/4-c)b, (3/4+c+2epsilon)b]`.

Since selected size is `t-|P|+|clones selected|`, good clone noise places
these respectively in

- left interval `[K-3407b/3000, K-173b/200]`;
- right interval `[K-259b/300, K-319b/500]`.

Their lengths are `203b/750` and `169b/750`, both less than b. Each contains
at most b+1 integer coefficient indices, irrespective of nonintegral
endpoints. Set the integer

`j = K - floor(108b/125)`.

The certificate checks exactly

`200 floor(108b/125) < 173b`,
`300 floor(108b/125) > 259b`.

Therefore every index in the left interval is less than j and every index
in the right interval is greater than j. The lower bound `L>=90*3b`
ensures the left interval and j are nonnegative; all upper offsets from K
are negative and `K<=n`, so all indices are in the coefficient range.

Each interval has probability greater than 1/3. Pigeonhole gives an index
in each with coefficient divided by the total number of dominating sets
strictly larger than

`1/[3(b+1)] > 2^-40`,

whereas the coefficient at j divided by that same total is less than
`2^-47`. This is a strict valley in the ordinary, unweighted domination
coefficient sequence, and therefore disproves unimodality for every
qualifying tuple's constructed graph.

## Verification and limits

`domination_permutation_extension.py` uses integers and Python Fractions
only. All 36 checks passed; its exact values and booleans are stored in the
companion JSON. This is scalar checking of the displayed existence proof,
not a graph/permutation sweep, and not a Lean formalization of this new
member. The canonical projective Lean proof remains unchanged. No claim
of a generated tuple, efficient construction, minimal order, or separate
novelty audit is made.
