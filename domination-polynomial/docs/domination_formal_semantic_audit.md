# Canonical domination counterexample: independent semantic audit

This review covers the formal definitions, counting identities, and theorem
interfaces. It was AI-assisted and includes author review of some components;
it is not external peer review.

No mismatch was found between the formal statement and ordinary domination
unimodality. The [final axiom report](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/repository_axioms.log)
records `canonical_not_unimodal` and `canonical_connected_counterexample`
with no premises and only `propext`, `Classical.choice`, and `Quot.sound`.

## Target statement

Du–Heilman–Panova, *Trees and Graphs with Non Log-concave Dominating Set Sequence via AI Tools*, arXiv:2605.02193v1, introduction and Conjecture 1.1, define d_j(G) as the number of all dominating subsets of cardinality j, for 0≤j≤n, and use weak increase followed by weak decrease. The Lean definitions use the same convention. [Source](https://arxiv.org/html/2605.02193v1).

The conjecture is due to Alikhani–Peng, *Introduction to Domination Polynomial of a Graph*, preprint arXiv:0905.2251 (2009), published Ars Combinatoria 114 (2014), 257–266. The [source review](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_novelty_refresh_2026-09-06.md) gives bibliographic details.

`DominationValley.Unimodal` is an existential mode in `Fin(n+1)`, with all pairs before the mode weakly increasing and all pairs after the mode weakly decreasing. This is equivalent to the adjacent-inequality definition in the conjecture. It is not strict unimodality, log-concavity, or an independence-polynomial statement. Including leading zero coefficients does not change the intended definition; the cited formulation includes d_0 through d_n.

## Concrete graph and all-subset semantics

- `DominationProjectiveInstance.Scalar` is `ZMod 2147483647`; its field instance is discharged by the proved `DominationParameters.q_prime`. Points are normalized triples, encoded by `(F×F) ⊕ (F⊕Unit)`. Their exact cardinality is b=q²+q+1.
- `DominationProjectiveGeometry` proves normalization existence/uniqueness, degree q+1, unique common neighbor, the real 0/1 Gram identity, and the expansion estimate. `canonical_disperser_integer` discharges the numerical 1/10000 threshold. No projective-plane-existence or spectral assumption is retained.
- `DominationGadgetGraph.Control` is the disjoint union of b left two-vertex cells and b right three-vertex cells. Indexed edges are all three right-triangle edges plus all six cross edges for each projective incidence. The finite edge-index count is m=b(6q+9), control count is t=5b. Endpoint pairs are distinct and nonrepeated as unordered pairs (`endpoints_distinct`, `endpoint_pair_unique`).
- Projective absolute points, for which Inc(p,p) holds, create cross edges between *different* left/right vertices. They do not create loops. Diagonal incidences are included.
- `finalGraph` puts a clique on all controls and an independent set of w=256 distinct clone vertices per indexed edge, each adjacent exactly to its two endpoints. It is an ordinary `SimpleGraph`, with n=t+wm=15211807199220036387538871517957 vertices. `final_connected` proves connectedness. Clone multiplicity produces distinct vertices, not weights or parallel edges.
- `DominationIncidenceGraph.Dominates` says every vertex is selected or has a selected neighbor. Thus it is domination by closed neighborhoods, not total domination, minimal domination, or independent domination.
- `selected_representation` represents **every** vertex subset uniquely by omitted controls P and selected clones K. `dominates_iff_forced` is exact when w>0 and every control is incident to an indexed edge; both assumptions are proved for the canonical construction.
- For P equal to all controls, `all_controls_omitted` proves domination iff all clones are selected. All-clone and all-vertex dominating sets therefore are not lost. The empty subset is correctly rejected for this nonempty graph.
- `dominating_fiber_count` gives 2^(wm−we(P)); `dominatingEquivSigma` and `dominating_count` include all P. Hard subsets are an intermediate class, not the definition of the final coefficient count.

## State encoding and hard-phase estimates

`DominationGadgetStates.hardEquiv` is a bijection between compatible pairs of four-state words and all edge-free control subsets. The left code covers the four subsets of I2, with sizes 0,1,1,2. The right code covers the empty set and three singletons of K3, with sizes 0,1,1,1. The proof includes surjectivity for arbitrary edge-free P and preservation of its cardinality (`encoded_card`, `hard_size_event_count`). Hence counts are not multiplied by an unaccounted local-state degeneracy.

Compatibility means no simultaneously occupied left/right cells across an incidence. Symmetry of Inc gives a state-label-preserving swap and equal phase counts. The swap need not preserve the *number of omitted controls*: the unequal size observables are the intended source of the two modes, not a contradiction in the symmetry argument.

The phase estimates distinguish independent uniform words from words conditioned on compatibility. The tail bounds apply to the former. Exceptional compatible configurations inject into an unrestricted majority-tail word times a minority word (`left_exceptional_product`, `right_exceptional_product`). Compatibility is dropped only for an upper bound. There is no unsupported assertion that the majority word remains iid after conditioning on a hard phase.

`DominationFiniteTails.alphabet_tail` constructs the product measure and proves independence, moments and its exact uniform-cardinality interpretation. `DominationBitEncoding.wordBits` explicitly identifies the left four-state statistic with 2b fair bits. The resulting left exponent is −u²/b, while the right exponent is −2u²/b; the distinct exponents are used correctly. All reindexing from the canonical point type to `Fin b` is through equivalences preserving the statistic.

The cutoff `(b+9999)/10000` is handled on both sides by `cutoff_large` and `cutoff_small`, so the rectangle argument and minority-count truncation agree. `GoodA` and `GoodC` imply the stated total omitted-size bands via explicit minority-size bounds. `bad_fraction_small`, `goodA_fraction_lower` and `goodC_fraction_lower` leave no probability assumptions. The bad class includes both-small configurations and either exceptional phase.

## Soft error, clone noise and actual size intervals

`DominationPartition.labeled_soft_comparison` deletes left endpoints of all currently induced indexed edges. Its remainder is hard; deleted vertices are in P; the pair (remainder,deleted set) reconstructs P; and the number deleted is at most the number of induced edges. This proves the soft upper bound without any monotonicity assumption about a conditional distribution. `nonhard_fraction_lt` in CanonicalPartition gives the actual ratio of nonhard dominating sets to all dominating sets, <2^-190. Both D and H are positive.

`DominationCloneSizes.selected_size` proves the actual size t−|P|+|K|. `hardEventEquiv` gives the exact product of a hard-control event and a clone-subset event. The clone tail transports every subset of the actual finite clone type to a subset of `Fin L`; the bound is on the normalized count of real subsets. Its numerical exponent agrees with L=256b(6q+9), and gives <2^-278. No Gaussian approximation is used.

`DominationSizeIntervals` uses real endpoints but integer sizes. It accounts for natural subtraction by proving |P|≤t, and proves K=t+L/2 with the canonical even L. Control bands [0.92b,1.08b] and [0.71b,0.80b], together with clone deviation≤b/100, imply JA=[K−1.09b,K−.91b] and JC=[K−.81b,K−.70b]. All JA indices precede j and all JC indices follow j. Boundary equalities do not create a missing case: clone-bad is the complement of the closed good interval and is contained in the closed tail event.

`DominationIntervalMass.joint_prob` factors actual dominating-set fractions into hard fraction × hard-control fraction × clone fraction. Its lower bounds retain only the corresponding exact hard-control band hypothesis. Its outside-union bound retains only the exact hard-control bad-band hypothesis. The union cover includes every nonhard dominating set. The three errors are not implicitly conditioned under different denominators.

## Coefficients and final logical closure

`DominationCanonicalPartition.DomSet` is the subtype of all actual dominating vertex subsets. `size` is their ordinary cardinality. `coefficient k` counts all such subsets with size k, and `size_le_n` permits the full index type `Fin(n+1)`.

`DominationCoefficientCounts.eventFibers` proves the exact event-to-coefficient-sum identity; it is not assumed. `DominationCoefficientBridge.coefficient_eq_generic` identifies this generic count with the actual graph coefficient. `center_card_le_outside` uses the proved strict interval separation. The interval-cardinality bound uses n+1≤2^104, while the center probability is bounded by 2^-189, giving an interval-average gap. Thus the conclusion is an actual strict coefficient valley and hence failure of ordinary weak unimodality, not merely separated mass in a continuous distribution.

The final dependencies are:

1. `HardBandTransfer.left_band_fraction`, `.right_band_fraction`, `.bad_band_fraction` discharge the three hypotheses of IntervalMass through `hardEquiv`/`encoded_card` and the hard-phase bounds.
2. Convert Fintype.card to Nat.card in the actual DomSet fractions, and convert ¬(JA∨JC) to ¬JA∧¬JC. These are definitional/cardinality equivalences, not new mathematical assumptions.
3. Use 2^-190+2^-300+2^-278<2^-189 and `not_unimodal_of_outside_fraction`.
4. The final theorem discharges all three hard-fraction premises. The axiom report contains only the standard Lean foundations.

The formalization defines the coefficients d_k(G) directly and proves their nonunimodality. It does not define a separate polynomial-valued object.

## Trust and scope

The [source manifest](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/source_manifest.json) records hashes of all 29 packaged Lean files (27 modules and two entrypoints). The closed-theorem axiom audit covers the complete dependency chain. No tactic holes, new axioms, or native_decide uses were found. Component axiom reports inspected during development contain only propext, Classical.choice and Quot.sound. Plain `decide` is used for small code tables and kernel-checked arithmetic; q primality is proved by norm_num. Noncomputable equivalences do not add assumptions or replace the explicit graph.

This does not certify unpublished priority, the smaller numerical candidate, minimum counterexample order, the tree restriction, or any new universal theorem about phase methods. The graph is a connected split graph with many degree-two vertices. Its applicability to the general finite-simple-graph conjecture is exact. The closed theorem has no remaining graph or counting hypotheses.

The independence corollary: `DominationIndependenceCorollary.control_independence_not_unimodal` also completed a targeted build, with only the same three standard axioms. It counts ordinary independent subsets of the actual auxiliary controlGraph and proves a strict-valley consequence of the existing hard-phase bands. This is a method reuse demonstration, not a new conjecture claim; see [domination_independence_reuse.md](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_independence_reuse.md).
