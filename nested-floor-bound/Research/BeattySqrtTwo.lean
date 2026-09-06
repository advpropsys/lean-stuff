import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-! Proof of the inequality conjecture stated in OEIS A341239. -/
namespace Research.BeattySqrtTwo

noncomputable def seq (n : ℕ) : ℤ :=
  ⌊(1 + Real.sqrt 2) * (⌊Real.sqrt 2 * (n : ℝ)⌋ : ℝ)⌋

theorem conjecture (n : ℕ) (hn : 1 ≤ n) :
    1 < (1 + Real.sqrt 2) * Real.sqrt 2 * (n : ℝ) - seq n ∧
    (1 + Real.sqrt 2) * Real.sqrt 2 * (n : ℝ) - seq n < 3 := by
  let s : ℝ := Real.sqrt 2
  let m : ℤ := ⌊s * (n : ℝ)⌋
  let a : ℤ := seq n
  let t : ℝ := s * n - m
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslt : s < 2 := by nlinarith
  have hmle : (m : ℝ) ≤ s * n := Int.floor_le _
  have hmlt : s * (n : ℝ) < m + 1 := Int.lt_floor_add_one _
  have hirr : Irrational (s * (n : ℝ)) :=
    irrational_sqrt_two.mul_natCast (by omega)
  have ht0 : 0 < t := by
    have := hirr.ne_int m
    dsimp [t]
    rcases lt_or_eq_of_le hmle with h | h
    · linarith
    · exact False.elim (this h.symm)
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hale : (a : ℝ) ≤ (1 + s) * m := Int.floor_le _
  have halt : (1 + s) * (m : ℝ) < a + 1 := Int.lt_floor_add_one _
  have hident : (1 + s) * (m : ℝ) = m + 2 * (n : ℝ) - s * t := by
    dsimp [t]
    nlinarith [hs2]
  let k : ℤ := m + 2 * (n : ℤ) - a
  have hkcast : (k : ℝ) = m + 2 * (n : ℝ) - a := by simp [k]
  have hst0 : 0 < s * t := mul_pos hs0 ht0
  have hst2 : s * t < 2 := by nlinarith
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by rw [hkcast]; linarith
    exact_mod_cast this
  have hklt : k < 3 := by
    have : (k : ℝ) < 3 := by rw [hkcast]; linarith
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
  have herr : (1 + s) * s * (n : ℝ) - a = t + k := by
    rw [hkcast]
    dsimp [t]
    nlinarith [hs2]
  change 1 < (1 + s) * s * (n : ℝ) - a ∧
    (1 + s) * s * (n : ℝ) - a < 3
  rw [herr]
  constructor <;> linarith

#print axioms conjecture
end Research.BeattySqrtTwo
