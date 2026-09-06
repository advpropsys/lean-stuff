# Smaller parameters for the projective domination construction

2026-09-06. This is a smaller member of the same construction and ordinary proof argument. The coordinator independently read the changed entropy, phase, noise and interval estimates and reran all 33 exact scalar checks successfully. The full graph theorem is not yet verified in Lean. The canonical manuscript and Lean constants have not been changed. No graph enumeration or domination-coefficient search was used.

The improved member uses

    Q=4194301=2^22−3,    w=100,    ε=1/1500,
    b=17592165072903,
    m=b(6Q+9)=442721171674138410945,
    L=wm=44272117167413841094500,
    n=5b+L=44272117255374666459015.

Its order is over **343 million times smaller** than the canonical member. The graph definition, projective incidence geometry, and finite soft-to-hard comparison are unchanged. The main quantitative improvement is to pigeonhole within each good interval, which contains at most b+1 indices, instead of using the total graph order n+1.

## Parameterized sufficient inequalities

Let Q be a prime, b=Q²+Q+1, and w a positive even integer. Put t=5b, L=wb(6Q+9), and K=t+L/2. Choose an omission minority threshold 0<ε<1/4 and positive deviations a,c,r. Here a is the left omitted-vertex deviation from b, c the right deviation from 3b/4, and r the clone deviation from L/2, all in units of b.

The following conditions suffice for the manuscript's argument:

1. **Disperser:** Q<(Q+1)²ε².
2. **Entropy:** let E be an explicit upper bound for h(ε)+ε log3. Require η=min(a²−E,2c²−E,log4−2E)>0. Then the total bad hard-model probability is at most δ_H=5exp(−ηb).
3. **Soft error:** if t2^(−w)<1/2, then δ_S≤2t2^(−w).
4. **Clone error:** δ_B≤2exp(−2r²b/[w(6Q+9)]).
5. **Separated intervals:** a+c+2ε+2r<1/4, with b times the remaining gap larger than the necessary integer-rounding allowance.

The good selected-size intervals are exactly

    J_A=[K−(1+a+ε+r)b, K−(1−a−r)b],
    J_C=[K−(3/4+c+2ε+r)b, K−(3/4−c−r)b].

Their lengths are (2a+ε+2r)b and (2c+2ε+2r)b. If each length is at most b, each interval contains at most b+1 integers. Thus it suffices that

    (1−δ_S)(1/2−δ_H)(1−δ_B)>1/3,
    δ_S+δ_H+δ_B < 1/[3(b+1)].

Any integer strictly in the gap then has smaller probability than some coefficient on each side. These are sufficient bounds rather than an optimized characterization. They keep all finite-penalty configurations and all rounding effects.

The underlying scaling is useful: the clone exponent is approximately r²Q/(3w), while the peak probability need only be of order Q^(−2). The soft bound therefore asks for w roughly greater than 4log₂Q, rather than the approximately 5log₂Q required by pigeonholing over the whole graph. Increasing r helps quadratically, but the entropy and phase-gap inequalities limit it.

## Exact choices and hard-model tails

For the stated smaller member take

    a=2/25=0.08,    c=57/1000=0.057,    r=11/200=0.055,
    E=19/3000,      η=1/15000.

Q is prime by trial division through 2047. The exact disperser inequality is

    Q·1500² < (Q+1)².

For entropy, the elementary bound gives

    h(ε)+ε log3 ≤ ε[1+log(3/ε)]
                    = [1+log4500]/1500 < 19/3000.

The last inequality follows from log4500<17/2. One entirely rational check proves it: e>65/24>27/10, and 27^17>4500²·10^17. Then

    a²−E=1/15000,
    2c²−E>1/15000,
    1−2E>1/15000.

Using log4≥1, all three hard-model errors are bounded by 5exp(−b/15000). Since b/15000>110 and e>2,

    δ_H <5·2^(−110)<2^(−100).

The same phase symmetry and counting argument as in the manuscript applies. Good left configurations omit between (1−a)b and (1+a+ε)b controls; good right configurations omit between (3/4−c)b and (3/4+c+2ε)b controls. These are actual finite hard-model counts, not independent assumptions about variables under conditioning.

## Exact soft and optional-vertex errors

The finite cleanup comparison is unchanged. With w=100,

    t2^(−100)<1/2,
    δ_S≤2t2^(−100)=10b·2^(−100)<2^(−52).

For clone noise the exact rational exponent is

    2r²b/[100(6Q+9)] > 42

(its decimal value is approximately 42.29253, used only for illustration). Thus

    δ_B < 2e^(−42) < 2(10/27)^42 < 2^(−59).

The final comparison is checked by integer powers, without floating-point logarithms. Consequently

    δ_S+δ_H+δ_B < 2^(−52)+2^(−100)+2^(−59) < 2^(−51).

Also the rational lower bound

    (1−2^(−52))(1/2−2^(−100))(1−2^(−59)) > 1/3

certifies that each good interval carries more than one third of the mass of all dominating sets.

## Endpoints, floors, and the stronger pigeonhole step

The exact intervals are

    J_A=[K−(3407/3000)b, K−(173/200)b],
    J_C=[K−(259/300)b, K−(319/500)b].

Their lengths are (203/750)b and (169/750)b, both less than b. Therefore each contains at most b+1 coefficient indices. This bound uses only the fact that distinct integers are spaced at least one apart; endpoints need not be integral.

Choose

    j=K−floor(108b/125).

The exact floor comparisons are

    200 floor(108b/125)<173b,
    300 floor(108b/125)>259b.

They put j strictly above every index in J_A and strictly below every index in J_C. The second also follows algebraically from b>1500, because 108/125−259/300=1/1500; the first is immediate from 108/125<173/200. The certificate verifies 0≤j≤n and that both entire real intervals lie in [0,n].

Finally b+1≤2^44. Each good interval contains a coefficient with probability greater than

    1/[3(b+1)] > 2^(−46),

whereas the middle index has probability below 2^(−51). This gives a strict valley with a factor exceeding 32 between the guaranteed peak lower bound and center upper bound. No comparison with n+1 is required.

## Exact scalar certificate

`domination_simplification_certificate.py` checks all 33 finite scalar claims above using integers and rational arithmetic, and saves the full parameters and checks in its matching JSON. It includes complete trial division for Q, the entropy power inequality, all three hard tail margins, the soft bound, the clone exponent and power bound, phase-mass arithmetic, interval endpoints and cardinality widths, and both floor comparisons. It passed with exit code 0. No graph adjacency list or coefficient list was generated.

The preliminary candidate w=112 was also sufficient, but w=100 simplifies the multiplicity and reduces the order further while retaining the same five-bit probability gap. This study makes no claim that the selected parameters minimize the graph order.

## Could the auxiliary graph be simpler?

A symmetric graph built from permutations can replace the projective geometry in an existence proof. Take d independent uniformly random permutations π_i of [b], and put both edges x_L–π_i(x)_R and π_i(x)_L–x_R in H, suppressing duplicates. H is symmetric, has maximum degree at most 2d, and has no isolated vertices.

For fixed sets A,B of size k=ceil(εb), the probability all permutation edges avoid A×B is at most exp(−dk²/b). A union bound over binom(b,k)^2 pairs proves existence whenever

    2log binom(b,k) < dk²/b.

This is substantially sharper than a union bound over all 4^b pairs. One may use a binary-entropy bound to choose d of order ε^(−1)log(1/ε), then increase b until the clone concentration inequality holds. The number of F-edges is at most b(12d+3), so all subsequent estimates can use that upper bound even when suppressed duplicates make H irregular. The exact local-state side-swap still holds because H is symmetric.

This is a rigorously justified alternate existence mechanism, but this study has not certified a complete numerical member for it. A lexicographically first successful permutation tuple gives a finite definition, yet is less transparent as an evaluable adjacency rule and currently less convenient for Lean than the projective graph whose geometry component has now been formalized. It is therefore not proposed as a canonical replacement here. No claim that a particular untested permutation tuple is a disperser is made.
