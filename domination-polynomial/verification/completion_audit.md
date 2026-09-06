# Requirement audit, 2026-09-06

The package was checked against the original counterexample research objective
and the expanded request for formal proof, simplification, reuse, exposition,
and usefulness. Completion was not inferred from intermediate lemmas.

| Requirement | Authoritative evidence | Scope |
|---|---|---|
| Actual rigorous graph counterexample | `canonical_connected_counterexample` in `Research/DominationCounterexample.lean` | Closed theorem, actual finite connected simple graph and ordinary coefficients |
| Complete Lean proof | `fresh_build.log`, `package_build.log`, `axiom_audit.log` | Fresh local proof artifacts in a copied project; pinned external dependency caches reused |
| No proof holes or research axioms | Transitive final axiom report | Only propext, Classical.choice and Quot.sound |
| Intended conjecture | `docs/domination_formal_semantic_audit.md` and novelty refresh | Exact all-dominating-subsets and weak-unimodality semantics |
| Current status and novelty research | `docs/domination_novelty_refresh_2026-09-06.md` | Dated primary-source search; no earlier ordinary disproof found; no certification of publication priority |
| Smaller or simpler construction | Smaller-projective and permutation studies; exact scripts; `DominationSmallParameters.lean` | Two strict order improvements; full graph-level Lean proof remains the canonical member |
| Test method elsewhere | `control_independence_not_unimodal`; permutation extension | Closed second-statistic theorem and audited alternative auxiliary family; neither advertised as a second new open-problem resolution |
| Accessible explanation and usefulness | `docs/domination_package_explanation.md` | Mechanism, beneficiaries, antecedents and limitations explicitly stated |
| Research log and reviewable artifact | `RESEARCH_LOG.md`, README, source manifest, scripts and transcripts | Proof artifacts included here; no external peer review claimed |

The smaller constructions are deliberately distinguished from the canonical
kernel-checked graph. No minimal-order claim, generated permutation tuple,
practical algorithmic speedup, or publication-priority guarantee is made.

The final audit command displays closed statements with no unproved graph or
probability premises. The source hash check covers all 29 packaged Lean source
files, including the umbrella and audit entrypoints.
