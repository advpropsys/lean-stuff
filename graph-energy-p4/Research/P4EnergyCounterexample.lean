import Mathlib

/-! Exact counterexample to Remark 1, p.302 of Jahanbani--Gutman (2025).
The energy is defined from the real roots of the adjacency characteristic
polynomial, counting multiplicity. This file does not assume the spectrum. -/
set_option maxHeartbeats 1000000
namespace P4EnergyCounterexample
open Matrix Polynomial

noncomputable def A : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0,1,0,0; 1,0,1,0; 0,1,0,1; 0,0,1,0]

def G : SimpleGraph (Fin 4) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := by intro i j h; exact h.symm
  loopless := ⟨by intro i; omega⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem connected : G.Connected := by decide
theorem edge_count : G.edgeFinset.card = 3 := by decide

theorem adjacency : G.adjMatrix ℝ = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [SimpleGraph.adjMatrix, G, A]

theorem charpoly_exact : A.charpoly = (X^4 - 3*X^2 + 1 : ℝ[X]) := by
  have hc : Matrix.charmatrix A =
      !![X,-1,0,0; -1,X,-1,0; 0,-1,X,-1; 0,0,-1,X] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.charmatrix, Matrix.diagonal, A]
  rw [Matrix.charpoly, hc, Matrix.det_succ_row_zero]
  norm_num [Matrix.det_fin_three, Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.vecHead, Matrix.vecTail]
  dsimp [Matrix.vecCons, Fin.cons]
  ring_nf
  change -(X * X) - X^2 * 2 + X^4 - (-1) = (1 - X^2 * 3 + X^4 : ℝ[X])
  ring

theorem determinant_one : A.det = 1 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_exact]
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul]

noncomputable def a : ℝ := (Real.sqrt 5 + 1)/2
noncomputable def b : ℝ := (Real.sqrt 5 - 1)/2

lemma sqrt5_sq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
lemma a_pos : 0 < a := by unfold a; positivity
lemma b_pos : 0 < b := by
  have h := Real.sqrt_nonneg (5:ℝ)
  have hs := sqrt5_sq
  unfold b
  nlinarith

lemma roots_factor : A.charpoly =
    (X-C a)*(X-C b)*(X-C (-b))*(X-C (-a)) := by
  rw [charpoly_exact]
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_one]
  unfold a b
  nlinarith [sqrt5_sq, sq_nonneg (t^2 - 1)]

noncomputable def energy : ℝ := (A.charpoly.roots.map abs).sum

lemma root_multiset : A.charpoly.roots = {a,b,-b,-a} := by
  have hf : A.charpoly = (({a,b,-b,-a} : Multiset ℝ).map (fun r => X-C r)).prod := by
    rw [roots_factor]
    simp
    ring
  rw [hf, Polynomial.roots_multiset_prod_X_sub_C]

lemma extreme_roots : a ∈ A.charpoly.roots ∧ -a ∈ A.charpoly.roots ∧
    ∀ r ∈ A.charpoly.roots, -a ≤ r ∧ r ≤ a := by
  rw [root_multiset]
  have ha := a_pos
  have hb := b_pos
  have hab : b < a := by unfold a b; linarith
  constructor
  · simp
  constructor
  · simp
  intro r hr
  simp at hr
  rcases hr with rfl | rfl | rfl | rfl <;> constructor <;> linarith

noncomputable def graphEnergy (H : SimpleGraph (Fin 4)) [DecidableRel H.Adj] : ℝ :=
  (((H.adjMatrix ℝ).charpoly).roots.map abs).sum

lemma graph_energy_eq : graphEnergy G = energy := by
  unfold graphEnergy energy
  rw [adjacency]

theorem energy_exact : energy = 2 * Real.sqrt 5 := by
  unfold energy
  rw [root_multiset]
  simp [abs_neg, abs_of_pos a_pos, abs_of_pos b_pos]
  unfold a b
  ring

theorem energy_squared : energy^2 = 20 := by
  rw [energy_exact]
  nlinarith [sqrt5_sq]

theorem signed_spectral_span : a - |-a| = 0 := by
  rw [abs_neg, abs_of_pos a_pos]
  ring

theorem claimed_bound_squared :
    (2 * (3:ℝ) * 4 - 4^2 / 4 * (a - |-a|)^2) = 24 := by
  rw [signed_spectral_span]
  norm_num

theorem remark_one_is_false :
    ¬ energy ≥ Real.sqrt (2 * (3:ℝ) * 4 - 4^2 / 4 * (a - |-a|)^2) := by
  rw [claimed_bound_squared, energy_exact]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 24 by norm_num)
  have h5 := sqrt5_sq
  have h24 := Real.sqrt_nonneg (24:ℝ)
  have h5n := Real.sqrt_nonneg (5:ℝ)
  nlinarith
/-- The proposed inequality fails for the graph G. -/
theorem graph_remark_one_is_false :
    ¬ graphEnergy G ≥ Real.sqrt
      (2 * (G.edgeFinset.card : ℝ) * Fintype.card (Fin 4) -
        (Fintype.card (Fin 4) : ℝ)^2 / 4 * (a - |-a|)^2) := by
  simpa [graph_energy_eq, edge_count] using remark_one_is_false

#print axioms graph_remark_one_is_false
#print axioms extreme_roots
#print axioms connected
#print axioms determinant_one

end P4EnergyCounterexample
