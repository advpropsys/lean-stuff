import Research.Motzkin
import Research.MotzkinAnalysis

/-! Analytic estimates applied to the alternating Motzkin sums. -/
namespace Research.Motzkin

theorem T_real_positive (n : ℕ) (hn : 2 ≤ n) : 0 < (T n : ℝ) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact_mod_cast T_positive k

theorem y_real_enclosure (n : ℕ) (hn : 9 ≤ n) :
    6 * ((n : ℝ) + 1) / (2 * n + 5) ≤ (T (n + 1) : ℝ) / T n ∧
    (T (n + 1) : ℝ) / T n ≤ 6 * ((n : ℝ) + 3) / (2 * n + 9) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  have hh := y_enclosure k
  unfold b y at hh
  have hr :
      6 * (((k : ℝ) + 9) + 1) / (2 * ((k : ℝ) + 9) + 5) ≤
          (T (k + 9 + 1) : ℝ) / T (k + 9) ∧
      (T (k + 9 + 1) : ℝ) / T (k + 9) ≤
        6 * (((k : ℝ) + 11) + 1) / (2 * ((k : ℝ) + 11) + 5) := by
    have hl := (Rat.cast_le (K := ℝ)).mpr hh.1
    have hu := (Rat.cast_le (K := ℝ)).mpr hh.2
    push_cast at hl hu
    exact ⟨hl, hu⟩
  push_cast
  convert hr using 1
  ring_nf

theorem root_log_concave_tail (k : ℕ) :
    Real.log (T (k + 11) : ℝ) / ((k : ℝ) + 11) +
      Real.log (T (k + 13) : ℝ) / ((k : ℝ) + 13) <
      2 * Real.log (T (k + 12) : ℝ) / ((k : ℝ) + 12) := by
  exact Research.MotzkinAnalysis.tail_log_concavity (fun n => (T n : ℝ))
    (fun n hn => T_real_positive n (by omega)) y_real_enclosure
    (by change (T 12 : ℝ) = 11299; rw [T12]; norm_num) k

/-- Zhao's Conjecture 1, in a strict logarithmic form at every center n ≥ 10. -/
theorem zhao_log_concavity (n : ℕ) (hn : 10 ≤ n) :
    Real.log (T (n - 1) : ℝ) / (n - 1 : ℕ) +
      Real.log (T (n + 1) : ℝ) / (n + 1 : ℕ) <
      2 * Real.log (T n : ℝ) / n := by
  by_cases h10 : n = 10
  · subst n
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]
    exact center10_log
  by_cases h11 : n = 11
  · subst n
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, Nat.reduceAdd]
    exact center11_log
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
  have hsub : k + 12 - 1 = k + 11 := by omega
  simpa only [hsub, Nat.add_assoc, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Nat.reduceAdd] using
    root_log_concave_tail k

theorem sharp_root_log_concavity (n : ℕ) (hn : 6 ≤ n) :
    Real.log (T (n - 1) : ℝ) / (n - 1 : ℕ) +
      Real.log (T (n + 1) : ℝ) / (n + 1 : ℕ) <
      2 * Real.log (T n : ℝ) / n := by
  by_cases h10 : 10 ≤ n
  · exact zhao_log_concavity n h10
  have hu : n ≤ 9 := by omega
  interval_cases n
  · exact center6_log
  · exact center7_log
  · exact center8_log
  · exact center9_log

/-- The real nth-root sequence; its terms are positive for n ≥ 2. -/
noncomputable def root (n : ℕ) : ℝ := (T n : ℝ) ^ (1 / (n : ℝ))

/-- Strict log-concavity from index 5: every center n ≥ 6. -/
theorem root_strict_log_concave (n : ℕ) (hn : 6 ≤ n) :
    root (n - 1) * root (n + 1) < (root n)^2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hs : k + 2 - 1 = k + 1 := by omega
  have hl := sharp_root_log_concavity (k + 2) hn
  have hp := T_real_positive (k + 1) (by omega)
  have hc := T_real_positive (k + 2) (by omega)
  have hd := T_real_positive (k + 3) (by omega)
  have hlog : Real.log (T (k + 1) : ℝ) / ((k : ℝ) + 1) +
      Real.log (T (k + 3) : ℝ) / ((k : ℝ) + 3) <
      2 * Real.log (T (k + 2) : ℝ) / ((k : ℝ) + 2) := by
    simpa only [hs, Nat.add_assoc, Nat.reduceAdd, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat] using hl
  simpa only [root, hs, Nat.add_assoc, Nat.reduceAdd, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] using root_concave_of_log k hp hc hd hlog

/-- The starting index 5 is sharp: the inequality strictly fails at center 5. -/
theorem root_center5_reverse : (root 5)^2 < root 4 * root 6 := by
  have h4 := T_real_positive 4 (by norm_num)
  have h5 := T_real_positive 5 (by norm_num)
  have h6 := T_real_positive 6 (by norm_num)
  unfold root
  apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow h5, Real.log_rpow h4, Real.log_rpow h6]
  norm_num
  convert center5_log_reverse using 1 <;> ring

/-- The bound for centers n ≥ 10 follows from the bound for centers n ≥ 6. -/
theorem zhao_conjecture (n : ℕ) (hn : 10 ≤ n) :
    root (n - 1) * root (n + 1) ≤ (root n)^2 :=
  le_of_lt (root_strict_log_concave n (by omega))

#print axioms zhao_conjecture
#print axioms root_strict_log_concave
#print axioms root_center5_reverse

end Research.Motzkin
