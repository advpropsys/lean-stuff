# An explicit split graph with a non-unimodal domination sequence

The proof defines a finite graph and derives exact counting and concentration
bounds for its domination sequence. A [Lean formalization](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Research/DominationCounterexample.lean)
and [axiom report](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/repository_axioms.log) accompany the argument.

## Statement

There is a finite connected simple split graph G with

    n = 15211807199220036387538871517957

vertices whose domination sequence is not unimodal. More precisely, for the
explicit graph below there are integers i<j<k with

    d_i(G)>d_j(G)<d_k(G),

where d_r counts all dominating vertex subsets of cardinality r. This is the
ordinary, unweighted domination polynomial. The middle index j is specified
below; the two larger coefficients are obtained by finite pigeonhole.

The intended Alikhani–Peng conjecture asserts unimodality for every finite
simple graph. The formulation is recorded in
[Omar (2026)](https://arxiv.org/html/2601.14494v1) and independently in
[Du–Heilman–Panova (2026), Conjecture 1.1](https://arxiv.org/html/2605.02193v1).
Their log-concavity discussions concern a stronger, different property.

## 1. The explicit graph

Put

    Q=2147483647=2^31−1,    b=Q²+Q+1=4611686016279904257,
    w=256,                 ε=1/10000.

Q is prime: trial division by every integer from 2 through 46340, inclusive,
finds no divisor. This finite check is independently implemented in the
saved parameter/audit scripts. Work over the prime field F_Q.

Use the following normalized representatives of projective points:

    (1,a,b') for a,b'∈F_Q;
    (0,1,a)  for a∈F_Q;
    (0,0,1).

There are b representatives. Form a bipartite cell graph B with two copies
of this set, joining x on the left to y on the right exactly when x·y=0.

Construct an incidence graph F by replacing each left cell with two
independent controls and each right cell with three controls forming a
triangle. For every B-edge join its two left controls to its three right
controls, adding all six edges. There are no other F-edges.

Finally, G has these t=5b controls, made into a clique, and, for every
F-edge, w new vertices adjacent exactly to that edge's two controls.
All new vertices are mutually nonadjacent. Distinct edge/clone labels give
distinct vertices. This specifies a finite simple connected split graph.
It has no universal control: each control misses cohorts at other F-edges.

Every B-row has Q+1 neighbors, so

    m=|E(F)|=b(6Q+9)=59421121871863195146318249987,
    L=wm=15211807199196977957457471996672,
    n=t+L=15211807199220036387538871517957 < 2^104.

## 2. The required property of B

The dot-product rule is symmetric. Its b×b incidence matrix N satisfies

    N=Nᵀ,    N1=(Q+1)1,    N²=QI+J.

Indeed one nonzero linear equation in three variables has a two-dimensional
kernel, hence Q+1 projective solutions. Two independent linear equations
have a one-dimensional common kernel, hence one projective solution.
Distinct normalized projective vectors are independent. This proves every
diagonal and off-diagonal entry of N².

On the subspace perpendicular to 1, the operator norm of N is sqrt(Q).
Centering indicator vectors and applying Cauchy–Schwarz therefore gives

    |e_B(S,T)−(Q+1)|S||T|/b| ≤ sqrt(Q|S||T|).

If S,T have no edge and are nonempty, this implies

    |S||T| ≤ Qb²/(Q+1)².

The exact integer inequality 10^8 Q<(Q+1)² shows that B has no empty S×T
with both |S|≥εb and |T|≥εb. Thus any independent occupied-cell set has
fewer than εb occupied cells on at least one side. Notice that x·x=0 causes
an edge between distinct left/right cells; it never creates a graph loop.

## 3. Exact domination counting and the soft-error bound

For a dominating set of G, let P be its omitted controls. Every clone whose
F-edge has both endpoints in P is forced into the dominating set. Every
other clone is optional. If any control is selected, the clique dominates
all controls. If no control is selected, all clones are forced and dominate
every control because F has no isolated vertices. Consequently, for every P,
including P=V(F), the number of dominating sets with this omitted set is

    2^(L−w e_F(P)).

Put ρ=2^(−256), Z=Σ_P ρ^e_F(P), and H=|Ind(F)|. Then the total number of
dominating sets is 2^L Z. Moreover

    H ≤ Z ≤ H(1+ρ)^t.                                      (1)

To prove the upper bound, fix a vertex ordering. From each P, repeatedly
delete a deterministically chosen endpoint of a remaining induced edge.
The final I is independent. If R=P\I, then |R|≤e_F(P), since each deletion
removes at least one remaining edge. The pair (I,R) determines P, so

    Σ_P ρ^e_F(P) ≤ Σ_(I independent) Σ_(R⊆V(F)\I) ρ^|R|
                 = Σ_(I independent) (1+ρ)^(t−|I|)
                 ≤ H(1+ρ)^t.

Call a configuration hard when P is independent in F. Under the uniform
distribution on all dominating sets, (1) bounds the probability of not
being hard by

    δ_S ≤ (1+ρ)^t−1 < 2^(−190).                            (2)

For an elementary exact bound, t<2^65 gives tρ<2^(−191), and
(1+ρ)^t≤Σ_(r≥0)(tρ)^r=1/(1−tρ). Thus δ_S<2tρ<2^(−190).

Conditional on being hard, P is uniform in Ind(F), and the selected clones
are independent fair binary choices, independent of P. If X is their number,

    X~Binomial(L,1/2),    |D|=t−|P|+X.                     (3)

This controls all finite-penalty configurations, including multiple omitted
vertices of a right triangle. It is not a zero-temperature approximation.

## 4. Two large hard phases

A nonempty independent subset of a left cell has three choices of sizes
1,1,2. A nonempty independent subset of a right triangle has three choices,
all of size one. Thus an occupied-cell independent set U in B represents
exactly 3^|U| independent sets of F. In particular H≥4^b, by using either
one side alone.

Let A be the hard configurations with at least εb occupied left cells, and
C those with at least εb occupied right cells. They are disjoint by §2.
They have equal cardinality: swap the cell parts in B and use any fixed
bijection between the three nonempty left and right local choices. This is
a bijection on independent sets of F even though F itself is not symmetric.
The remaining class O has fewer than εb occupied cells on both sides.

Write

    T=Σ_(0≤r≤floor(εb)) binom(b,r)3^r.

The elementary entropy bound gives

    T≤exp(b[−ε log ε−(1−ε)log(1−ε)+ε log3])
      <exp(0.0012b).                                      (4)

For completeness, insert z=ε/[3(1−ε)]<1 in (1+3z)^b and use
z^r≥z^(εb) for r≤εb. This proves the first inequality. Also
−(1−ε)log(1−ε)≤ε and log30000<11, proving the second. The latter logarithm
bound follows, for example, from e>8/3 and 8^11>30000·3^11.

The class O has at most T² configurations. Since log4≥1, its fraction among
all hard configurations is at most exp(−0.9976b).

The binary-sum bound is

    Pr(|Y−E Y|≥u) ≤ 2exp(−2u²/r)

for a sum Y of r independent variables valued in {0,1}. One short proof:
the second derivative of the log moment-generating function of a Bernoulli
variable is a tilted Bernoulli variance, at most 1/4. Integrating twice
bounds the centered log moment-generating function by s²/8. Independence,
Markov's inequality, and s=4u/r give each one-sided tail; add the two tails.
This is also [Hoeffding's classical bound](https://doi.org/10.1080/01621459.1963.10500830).

In A, the right side is a minority, with at most T possible internal states.
Ignoring all intercell restrictions on the left gives all 4^b subsets of
its 2b controls. Their sizes have distribution Binomial(2b,1/2). The number
whose left omitted-control size is outside [0.94b,1.06b], multiplied by T
and divided by H≥4^b, is at most

    2exp(−0.0036b)T ≤ 2exp(−0.0024b).

All other configurations of A have total omitted-control size in
[0.94b,1.0601b], since each occupied right cell adds one. In particular

    |P|∈[0.92b,1.08b].                                   (5)

In C, ignore restrictions on the right. Each right cell has four possible
states, three nonempty, so its total omitted size is Binomial(b,3/4).
The fraction outside [0.71b,0.79b], allowing at most T states on the minority
left, is at most

    2exp(−0.0032b)T ≤ 2exp(−0.002b).

The minority left adds at most 2εb omitted controls. Thus the remaining
configurations of C satisfy

    |P|∈[0.71b,0.80b].                                   (6)

Combining the both-small class and these two atypical counts, the total
hard fraction outside the good parts of A,C is at most

    δ_H≤5exp(−b/500)<2^(−300).                            (7)

The numerical bound uses only b/500>310 and e≥2. Since |A|=|C|, each good
part has hard probability at least 1/2−δ_H. All interval comparisons above
are real comparisons with integer counts, so no divisibility of b by 10000
or 100 is assumed.

## 5. Optional vertices cannot fill the gap

Let K=t+L/2, an integer because w=256. By the same binary-sum bound,

    Pr(|X−L/2|≥b/100) ≤ 2exp(−b/[5000·256·(6Q+9)])
                       <2exp(−279)<2^(−278)=δ_B.           (8)

The exponent >279 is an exact rational inequality verified in the saved
scalar checks. Conditional on a good hard configuration and this clone
event, (3), (5), and (6) place dominating-set sizes in the disjoint intervals

    J_A=[K−1.09b, K−0.91b],
    J_C=[K−0.81b, K−0.70b].

Each interval has probability at least

    (1−δ_S)(1/2−δ_H)(1−δ_B)>1/3

under the uniform distribution on ALL dominating sets. The probability of
falling outside their union is less than

    δ_S+δ_H+δ_B <2^(−189).                                (9)

In particular this estimate includes every positive-cost omitted-control
set; none was discarded without a bound.

## 6. A strict coefficient valley

Choose the explicit integer

    j=K−floor(43b/50).

Since b>20, every integer in J_A is less than j and every integer in J_C
is greater than j. Also 0≤j≤n. Hence (9) gives

    d_j(G)/D(G,1)<2^(−189).

There are only n+1 possible sizes. Each of J_A and J_C has probability
greater than 1/3, so finite pigeonhole supplies i∈J_A and k∈J_C such that

    d_i(G)/D(G,1)>1/[3(n+1)]>2^(−106),
    d_k(G)/D(G,1)>1/[3(n+1)]>2^(−106),

where n+1≤2^104 was checked exactly. Therefore i<j<k and both d_i,d_k
strictly exceed d_j. A sequence that first weakly increases and then weakly
decreases cannot have this pattern. This proves the statement.

## Verification

The [semantic audit](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_formal_semantic_audit.md) checks the graph,
geometry, and counting correspondences. The [Lean sources](https://github.com/advpropsys/lean-stuff/tree/main/domination-polynomial/Research)
prove the quantitative estimates and parameter inequalities. These arguments
do not enumerate the graph or its coefficients.

`Research.DominationCounterexample.canonical_not_unimodal` is a closed
Lean theorem about the actual graph's ordinary domination coefficients.
`canonical_connected_counterexample` includes connectedness and the explicit
vertex count. Both report only `propext`, `Classical.choice`, and `Quot.sound`
in the axiom audit. The formal chain includes projective geometry, the exact
domination and state correspondences, all count and concentration estimates,
and the final coefficient implication. Reproducibility instructions and
source hashes are included in the review package. Novelty searches and
external mathematical review remain separate from kernel verification.
