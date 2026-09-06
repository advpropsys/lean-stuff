import Mathlib

/-!
Finite combinatorial components of the soft domination comparison.
No projective geometry, probabilistic tail bound, or graph valley is asserted here.
-/

namespace Research.DominationSoftComparison

/-- Removing at most one vertex per nonempty contained edge leaves an edge-free
remainder. Edges are finite vertex sets, so this also applies to hypergraphs. -/
theorem exists_edge_free_remainder {V : Type*} [DecidableEq V]
    (P : Finset V) (E : Finset (Finset V))
    (hne : ∀ e ∈ E, e.Nonempty) (hsub : ∀ e ∈ E, e ⊆ P) :
    ∃ I : Finset V, I ⊆ P ∧ (P \ I).card ≤ E.card ∧
      ∀ e ∈ E, ¬ e ⊆ I := by
  classical
  let pick : {e // e ∈ E} → V := fun e => (hne e.val e.property).choose
  have hpick (e : {e // e ∈ E}) : pick e ∈ e.val :=
    (hne e.val e.property).choose_spec
  let R : Finset V := E.attach.image pick
  have hRP : R ⊆ P := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    exact hsub e.val e.property (hpick e)
  have hRc : R.card ≤ E.card := by
    calc
      R.card ≤ E.attach.card := Finset.card_image_le
      _ = E.card := Finset.card_attach
  refine ⟨P \ R, Finset.sdiff_subset, ?_, ?_⟩
  · have hdiff : P \ (P \ R) ⊆ R := by
      intro v hv
      simp only [Finset.mem_sdiff] at hv
      by_contra hn
      exact hv.2 ⟨hv.1, hn⟩
    exact le_trans (Finset.card_le_card hdiff) hRc
  · intro e he hcontained
    let ee : {e // e ∈ E} := ⟨e, he⟩
    have hr : pick ee ∈ R :=
      Finset.mem_image.mpr ⟨ee, Finset.mem_attach E ee, rfl⟩
    exact (Finset.mem_sdiff.mp (hcontained (hpick ee))).2 hr

/-- The partition function of all finite removed-vertex sets is a binomial power. -/
theorem sum_removed_weights {V : Type*} [Fintype V] (ρ : ℝ) :
    (∑ R : Finset V, ρ ^ R.card) = (1 + ρ) ^ Fintype.card V := by
  classical
  simpa [add_comm] using Fintype.sum_pow_mul_eq_add_pow V ρ (1 : ℝ)

/-- An injective encoding into a hard configuration and a removed-vertex set
gives the full soft-versus-hard partition-function bound. -/
theorem weighted_injection_bound {X H V : Type*}
    [Fintype X] [Fintype H] [Fintype V]
    (hard : X → H) (removed : X → Finset V) (energy : X → ℕ)
    (hinj : Function.Injective (fun x => (hard x, removed x)))
    (hcost : ∀ x, (removed x).card ≤ energy x)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑ x : X, ρ ^ energy x) ≤
      (Fintype.card H : ℝ) * (1 + ρ) ^ Fintype.card V := by
  classical
  let enc : X → H × Finset V := fun x => (hard x, removed x)
  calc
    (∑ x : X, ρ ^ energy x) ≤ ∑ x : X, ρ ^ (removed x).card := by
      apply Finset.sum_le_sum
      intro x hx
      exact pow_le_pow_of_le_one hρ0 hρ1 (hcost x)
    _ = ∑ p ∈ Finset.univ.image enc, ρ ^ p.2.card := by
      symm
      apply Finset.sum_image
      intro x hx y hy heq
      exact hinj heq
    _ ≤ ∑ p : H × Finset V, ρ ^ p.2.card := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro p
      exact pow_nonneg hρ0 _
    _ = (Fintype.card H : ℝ) * (1 + ρ) ^ Fintype.card V := by
      rw [Fintype.sum_prod_type]
      simp [sum_removed_weights]

/-- A cleanup witness suffices; injectivity follows from recovering the original
configuration as the union of its cleaned set and its removed vertices. -/
theorem soft_comparison_of_cleanup {V : Type*} [Fintype V] [DecidableEq V]
    (hardSets : Finset (Finset V)) (energy : Finset V → ℕ)
    (hcleanup : ∀ P : Finset V, ∃ I ∈ hardSets,
      I ⊆ P ∧ (P \ I).card ≤ energy P)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑ P : Finset V, ρ ^ energy P) ≤
      (hardSets.card : ℝ) * (1 + ρ) ^ Fintype.card V := by
  classical
  let clean : Finset V → {I // I ∈ hardSets} := fun P =>
    ⟨(hcleanup P).choose, (hcleanup P).choose_spec.1⟩
  have hc (P : Finset V) : (clean P).val ⊆ P ∧
      (P \ (clean P).val).card ≤ energy P :=
    (hcleanup P).choose_spec.2
  have hinj : Function.Injective
      (fun P : Finset V => (clean P, P \ (clean P).val)) := by
    intro P Q heq
    have hI : clean P = clean Q := congrArg Prod.fst heq
    have hR : P \ (clean P).val = Q \ (clean Q).val := congrArg Prod.snd heq
    calc
      P = (clean P).val ∪ (P \ (clean P).val) :=
        (Finset.union_sdiff_of_subset (hc P).1).symm
      _ = (clean Q).val ∪ (Q \ (clean Q).val) :=
        congrArg₂ (fun A B : Finset V => A ∪ B) (congrArg Subtype.val hI) hR
      _ = Q := Finset.union_sdiff_of_subset (hc Q).1
  simpa using weighted_injection_bound clean
    (fun P => P \ (clean P).val) energy hinj (fun P => (hc P).2) ρ hρ0 hρ1

/-- Full finite soft-to-hard comparison for a family of nonempty edges.
The energy counts edges entirely contained in the chosen vertex set.
For an ordinary graph, take its distinct two-vertex edge sets as `E`. -/
theorem finite_edge_soft_comparison {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Finset V)) (hne : ∀ e ∈ E, e.Nonempty)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑ P : Finset V, ρ ^ (E.filter (fun e => e ⊆ P)).card) ≤
      ((Finset.univ.filter (fun I : Finset V => ∀ e ∈ E, ¬ e ⊆ I)).card : ℝ) *
        (1 + ρ) ^ Fintype.card V := by
  classical
  apply soft_comparison_of_cleanup _ _ ?_ ρ hρ0 hρ1
  intro P
  obtain ⟨I, hIP, hcost, hfree⟩ := exists_edge_free_remainder P
    (E.filter (fun e => e ⊆ P))
    (fun e he => hne e (Finset.mem_filter.mp he).1)
    (fun e he => (Finset.mem_filter.mp he).2)
  refine ⟨I, ?_, hIP, hcost⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro e he hEI
  exact hfree e (Finset.mem_filter.mpr ⟨he, Finset.Subset.trans hEI hIP⟩) hEI

end Research.DominationSoftComparison

#print axioms Research.DominationSoftComparison.exists_edge_free_remainder
#print axioms Research.DominationSoftComparison.weighted_injection_bound
#print axioms Research.DominationSoftComparison.finite_edge_soft_comparison
