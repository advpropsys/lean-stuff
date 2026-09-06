import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! A known sharpness example for Lužar–Soták Problem 5.1.
This file does not prove the general conjecture. -/
namespace Research.CubicHomogeneous

def TwoHomogeneous {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (c : V → Fin k) : Prop :=
  (∀ u v, G.Adj u v → c u ≠ c v) ∧
    ∀ v, ((G.neighborFinset v).image c).card = 2

instance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (c : V → Fin k) :
    Decidable (TwoHomogeneous G c) := by
  unfold TwoHomogeneous
  infer_instance

def K33 : SimpleGraph (Fin 6) where
  Adj i j := (i.val < 3 ∧ 3 ≤ j.val) ∨ (j.val < 3 ∧ 3 ≤ i.val)
  symm := by intro i j h; exact h.symm
  loopless := ⟨by intro i h; omega⟩

instance : DecidableRel K33.Adj := by
  unfold K33
  infer_instance

def fourColoring : Fin 6 → Fin 4 := ![0, 0, 1, 2, 2, 3]

theorem K33_cubic : ∀ v, K33.degree v = 3 := by decide

theorem K33_four_colors : TwoHomogeneous K33 fourColoring := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem K33_no_three_colors : ¬ ∃ c : Fin 6 → Fin 3, TwoHomogeneous K33 c := by
  decide +kernel

#print axioms K33_cubic
#print axioms K33_four_colors
#print axioms K33_no_three_colors

end Research.CubicHomogeneous
