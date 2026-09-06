# A general transfer from independent-set sizes to domination coefficients

Ordinary proof draft, 2026-09-06. This isolates a reusable implication from the
current construction. It is not a claim of novelty for elementary mixture or
pigeonhole arguments, and this full graph-level statement is not yet in Lean.

Let F be a finite simple graph without isolated vertices, with t vertices and
m edges. Fix a positive integer w. Build G by making the t controls a clique
and adding w independent clone vertices per F-edge, each adjacent exactly to
its endpoints. Write L=wm and n=t+L.

Let I be a uniformly chosen independent subset of F and let X be an independent
Binomial(L,1/2) variable. Write μ for the law of t−|I|+X. Write ν for the size
law of a uniformly chosen ordinary dominating set of G.

Put ρ=2^(-w), H=|Ind(F)| and Z=Σ_(P⊆V(F))ρ^(e_F(P)). The exact counting
identity gives

    ν = α μ + (1−α) η,       α=H/Z,

for a probability law η if α<1; if α=1 then ν=μ. Indeed each omitted control
set P has exactly 2^(L−w e_F(P)) completions. Conditional on e_F(P)=0, all
independent P have equal weight, and all clones are independent fair choices.
The all-controls-omitted case is included because F has no isolates.

The deletion encoding proves H≤Z≤H(1+ρ)^t. Consequently

    0≤1−α≤1−(1+ρ)^(-t)≤(1+ρ)^t−1 =: ξ.

For every event A, |ν(A)−μ(A)|≤1−α≤ξ. This is a uniform finite error bound;
it does not require taking w to infinity.

Suppose J_1,J_2 are integer intervals within {0,...,n}, separated by an
integer j, with every index in J_1 below j and every index in J_2 above j.
Let M be any positive upper bound on the number of integer indices in each
interval. Assume

    μ(J_1)≥a,   μ(J_2)≥a,   μ(outside J_1∪J_2)≤h,
    (h+ξ)M < a−ξ.

Then ν(J_s)≥a−ξ, whereas ν({j})≤h+ξ. Each interval contains at most n+1
indices, and by hypothesis at most M indices, so it contains an index of
probability at least (a−ξ)/M>h+ξ.
Thus there exist i<j<k with ν(i)>ν(j)<ν(k). Multiplication by the positive
number of dominating sets proves d_i(G)>d_j(G)<d_k(G).

This theorem separates the work into three requirements:

1. Find two sufficiently large, separated classes of independent-set sizes.
2. Show that adding Binomial(L,1/2) noise preserves the separation.
3. Choose w so the finite error ξ is small relative to 1/M.

One may always take M=n+1, but using the actual interval widths can greatly
improve the parameters. The coefficient-only implication with separate exact
cardinalities for both intervals is formalized as
`DominationValley.not_unimodal_of_interval_mass_card`.

Increasing w helps the third requirement but increases L and makes the second
harder. This explicit tradeoff explains why simply adding more clones is not
a general amplification argument.

The projective-plane example supplies these hypotheses through balanced
two-vertex/triangle cells and expansion. The transfer itself does not require
a projective plane or those particular cells. This is the first useful target
for an alternative construction: satisfy the same quantitative hypotheses
with a simpler auxiliary F.

A further extension is immediate at the level of this argument: if r ordered
intervals each have mass at least a, total mass outside their union is at
most h, and each neighboring pair has an integer gap, the same strict
inequality supplies r large coefficients separated by r−1 smaller ones.
Constructing graphs that meet those r-phase hypotheses is an open research
task here; no such domination family has been established by this note.
