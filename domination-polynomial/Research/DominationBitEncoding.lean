import Research.DominationHardPhases

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Research.DominationBitEncoding
open DominationHardPhases

def twoBits : Fin 4 ≃ (Fin 2 → Bool) where
  toFun s j := if j = 0 then decide (2 ≤ s.val) else decide (s.val % 2 = 1)
  invFun w := ⟨(if w 0 then 2 else 0) + (if w 1 then 1 else 0), by
    cases w 0 <;> cases w 1 <;> norm_num⟩
  left_inv s := by fin_cases s <;> decide
  right_inv w := by
    funext j
    fin_cases j <;> cases h0 : w 0 <;> cases h1 : w 1 <;> simp [h0, h1]

theorem twoBits_sum (s : Fin 4) :
    (∑ j, if twoBits s j then (1 : ℝ) else 0) = leftSize s := by
  fin_cases s <;> norm_num [twoBits, Fin.sum_univ_two, leftSize]
  all_goals decide

def wordBits (r : ℕ) : Word (Fin r) ≃ (Fin (r * 2) → Bool) :=
  (Equiv.arrowCongr (Equiv.refl (Fin r)) twoBits).trans
    ((Equiv.curry (Fin r) (Fin 2) Bool).symm.trans
      (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool)))

theorem wordBits_sum (r : ℕ) (w : Word (Fin r)) :
    (∑ j, if wordBits r w j then (1 : ℝ) else 0) = ∑ i, (leftSize (w i) : ℝ) := by
  calc
    _ = ∑ p : Fin r × Fin 2, if wordBits r w (finProdFinEquiv p) then (1 : ℝ) else 0 :=
      (finProdFinEquiv.sum_comp _).symm
    _ = ∑ i : Fin r, ∑ j : Fin 2, if twoBits (w i) j then (1 : ℝ) else 0 := by
      simp only [wordBits, Equiv.trans_apply, Equiv.arrowCongr_apply,
        Function.comp_apply, Equiv.refl_apply, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type]
      rfl
    _ = _ := by simp_rw [twoBits_sum]

/-- Sharp two-bit tail for the left state sizes 0,1,1,2. -/
theorem left_word_tail (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {w : Word (Fin r) //
      u ≤ |(∑ i, (leftSize (w i) : ℝ)) - r|} : ℝ) / 4 ^ r ≤
      2 * Real.exp (-u ^ 2 / r) := by
  have hc : ((r * 2 : ℕ) : ℝ) / 2 = r := by push_cast; ring
  let E := (wordBits r).subtypeEquiv (p := fun w ↦
      u ≤ |(∑ i, (leftSize (w i) : ℝ)) - r|)
    (q := fun ω ↦ u ≤ |(∑ i, if ω i then (1 : ℝ) else 0) - ((r * 2 : ℕ) : ℝ) / 2|)
    (by intro w; dsimp; rw [wordBits_sum, hc])
  have h := DominationFiniteTails.binary_word_tail (r * 2) (by omega) u hu
  have hpow : (2 : ℝ) ^ (r * 2) = 4 ^ r := by
    rw [Nat.mul_comm, pow_mul]
    norm_num
  have hexp : -2 * u ^ 2 / ((r * 2 : ℕ) : ℝ) = -u ^ 2 / r := by push_cast; ring
  rw [← Fintype.card_congr E, hpow, hexp] at h
  exact h

end Research.DominationBitEncoding

#print axioms Research.DominationBitEncoding.left_word_tail
