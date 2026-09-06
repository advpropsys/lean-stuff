# Verification evidence

Verification evidence for the counterexample, smaller constructions,
independence corollary, and literature review is listed below.

| Result or check | Evidence | Scope |
|---|---|---|
| Graph counterexample | `canonical_connected_counterexample` in [DominationCounterexample.lean](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Research/DominationCounterexample.lean) | Closed theorem, finite connected simple graph and ordinary coefficients |
| Complete Lean proof | [fresh_build.log](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/fresh_build.log), [package_build.log](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/package_build.log), [axiom_audit.log](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/verification/axiom_audit.log) | All proof modules compiled against pinned dependencies |
| No proof holes or research axioms | Transitive final axiom report | Only propext, Classical.choice and Quot.sound |
| Intended conjecture | [domination_formal_semantic_audit.md](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_formal_semantic_audit.md) and [source review](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_novelty_refresh_2026-09-06.md) | Exact all-dominating-subsets and weak-unimodality semantics |
| Source review | [domination_novelty_refresh_2026-09-06.md](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_novelty_refresh_2026-09-06.md) | Dated primary-source search; no matching ordinary-domination disproof in the listed sources; no certification of publication priority |
| Smaller or simpler construction | Smaller-projective and permutation studies; exact scripts; [DominationSmallParameters.lean](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/Research/DominationSmallParameters.lean) | Two strict order improvements; complete graph-level Lean proof for the canonical member |
| Independence corollary | `control_independence_not_unimodal`; permutation extension | Closed second-statistic theorem and audited alternative auxiliary family; known phenomenon; no second open-problem resolution |
| Construction and applications | [domination_package_explanation.md](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/docs/domination_package_explanation.md) | Construction, references, consequences, and limits |
| Proof and verification files | [RESEARCH_LOG.md](https://github.com/advpropsys/lean-stuff/blob/main/domination-polynomial/RESEARCH_LOG.md), README, source manifest, scripts and transcripts | Proof artifacts included here; no external peer review claimed |

Only the canonical graph has a complete Lean proof. No minimal-order claim, generated permutation tuple,
practical algorithmic speedup, or publication-priority guarantee is made.

The axiom audit command displays closed statements with no unproved graph or
probability premises. The source hash check covers all 29 packaged Lean source
files, including the umbrella and audit entrypoints.
