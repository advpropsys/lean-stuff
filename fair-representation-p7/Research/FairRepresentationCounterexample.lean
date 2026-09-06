import Mathlib

/-! Counterexample to the literal integer-budget Conjecture 1.6 in
arXiv:1611.03196v1. This does not refute the different fair-splitting
formulation proved by Alishahi and Meunier in 2017.
Vertices here are numbered 0 through 6. -/
namespace FairRepresentationCounterexample

def P7 : SimpleGraph (Fin 7) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := by intro i j h; exact h.symm
  loopless := ⟨by intro i; omega⟩

instance : DecidableRel P7.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def parts : Fin 3 → Finset (Fin 7) := ![{1, 3, 5}, {0}, {2, 4, 6}]

def Independent (S : Finset (Fin 7)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ P7.Adj u v

instance (S : Finset (Fin 7)) : Decidable (Independent S) := by
  unfold Independent
  infer_instance

theorem independent_iff_mathlib (S : Finset (Fin 7)) :
    Independent S ↔ P7.IsIndepSet (S : Set (Fin 7)) := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h u hu v hv _
    exact h u hu v hv
  · intro h u hu v hv
    by_cases huv : u = v
    · subst v
      change ¬ (u.val + 1 = u.val ∨ u.val + 1 = u.val)
      omega
    · exact h hu hv huv

theorem connected : P7.Connected := by decide
theorem edge_count : P7.edgeFinset.card = 6 := by decide
theorem nonempty_parts : ∀ i, (parts i).Nonempty := by decide
theorem disjoint_parts : ∀ i j, i ≠ j → Disjoint (parts i) (parts j) := by decide
theorem covers : parts 0 ∪ parts 1 ∪ parts 2 = Finset.univ := by decide
theorem part_sizes : (parts 0).card = 3 ∧ (parts 1).card = 1 ∧
    (parts 2).card = 3 := by decide

theorem parts_independent : ∀ i, Independent (parts i) := by decide

/-- The counterexample still satisfies the later, weaker formulation,
with strict half-minus-one bounds in every part. -/
theorem weaker_formulation_witness : Independent {0, 3, 6} ∧
    ∀ i, ((parts i).card : ℤ) <
      2 * ((({0, 3, 6} : Finset (Fin 7)) ∩ parts i).card : ℤ) + 2 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem independent_classification : ∀ S : Finset (Fin 7), Independent S →
    S.card ≤ 3 ∨ S = {0, 2, 4, 6} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem count_partition : ∀ S : Finset (Fin 7),
    (S ∩ parts 0).card + (S ∩ parts 1).card + (S ∩ parts 2).card = S.card := by
  decide +kernel

/-- The source's half-integer inequalities, with denominators cleared.
The budgets are arbitrary integers, including negative integers. -/
def Feasible (S : Finset (Fin 7)) (b : Fin 3 → ℤ) : Prop :=
  Independent S ∧
  (∀ i, (parts i).card ≤ 2 * ((S ∩ parts i).card : ℤ) + 2 * b i) ∧
  2 * (∑ i, b i) ≤ 3 ∧ (∀ i, b i ≤ 1)

theorem integer_budget_conjecture_false : ¬ ∃ S b, Feasible S b := by
  rintro ⟨S, b, hi, hquota, hsum, hcap⟩
  have h0 := hquota 0
  have h1 := hquota 1
  have h2 := hquota 2
  have hcounts := count_partition S
  obtain ⟨hs0, hs1, hs2⟩ := part_sizes
  rw [hs0] at h0
  rw [hs1] at h1
  rw [hs2] at h2
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsum
  change 2 * (b 0 + (b 1 + b 2)) ≤ 3 at hsum
  rcases independent_classification S hi with hsmall | rfl
  · omega
  · have hz : (({0, 2, 4, 6} : Finset (Fin 7)) ∩ parts 0).card = 0 := by decide
    rw [hz] at h0
    have hc := hcap 0
    omega

/-- The same statement with the original real-valued halves. -/
theorem integer_budget_conjecture_false_real :
    ¬ ∃ (S : Finset (Fin 7)) (b : Fin 3 → ℤ), Independent S ∧
      (∀ i, ((S ∩ parts i).card : ℝ) ≥ (parts i).card / 2 - (b i : ℝ)) ∧
      (∑ i, (b i : ℝ)) ≤ (3 : ℝ) / 2 ∧ (∀ i, b i ≤ 1) := by
  rintro ⟨S, b, hi, hq, hs, hc⟩
  apply integer_budget_conjecture_false
  refine ⟨S, b, hi, ?_, ?_, hc⟩
  · intro i
    have h := hq i
    have h' : ((parts i).card : ℝ) ≤
        2 * ((S ∩ parts i).card : ℝ) + 2 * (b i : ℝ) := by linarith
    exact_mod_cast h'
  · have h' : 2 * (∑ i, (b i : ℝ)) ≤ 3 := by linarith
    exact_mod_cast h'

#print axioms integer_budget_conjecture_false
#print axioms integer_budget_conjecture_false_real

end FairRepresentationCounterexample
