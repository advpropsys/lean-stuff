import Mathlib

/-! Exact parameters for the projective-incidence domination construction.
These arithmetic facts do not assert existence of a counterexample graph.
-/

namespace Research.DominationParameters

set_option exponentiation.threshold 1024

def q : ℕ := 2147483647
def b : ℕ := q ^ 2 + q + 1
def w : ℕ := 256
def t : ℕ := 5 * b
def m : ℕ := b * (6 * q + 9)
def L : ℕ := w * m
def n : ℕ := t + L
def K : ℕ := t + L / 2
def j : ℕ := K - (43 * b / 50)

set_option maxHeartbeats 2000000 in
theorem q_prime : Nat.Prime q := by
  norm_num [q]

theorem b_value : b = 4611686016279904257 := by norm_num [b, q]
theorem m_value : m = 59421121871863195146318249987 := by
  norm_num [m, b, q]
theorem L_value : L = 15211807199196977957457471996672 := by
  norm_num [L, w, m, b, q]
theorem n_value : n = 15211807199220036387538871517957 := by
  norm_num [n, t, L, w, m, b, q]

theorem disperser_strict : 10000 ^ 2 * q < (q + 1) ^ 2 := by norm_num [q]
theorem entropy_aux : 30000 * 3 ^ 11 < (8 : ℕ) ^ 11 := by norm_num
theorem order_bound : n + 1 ≤ 2 ^ 104 := by norm_num [n, t, L, w, m, b, q]
theorem controls_bound : t < 2 ^ 65 := by norm_num [t, b, q]
theorem noise_exponent : 279 * 5000 * w * (6 * q + 9) < b := by
  norm_num [w, b, q]
theorem hard_exponent : 500 * 310 < b := by norm_num [b, q]
theorem clones_even : L % 2 = 0 := by norm_num [L, w, m, b, q]
theorem valley_valid : 0 < j ∧ j < n := by
  norm_num [j, K, n, t, L, w, m, b, q]
theorem valley_after_left : 100 * (K - j) < 91 * b := by
  norm_num [j, K, t, L, w, m, b, q]
theorem valley_before_right : 81 * b < 100 * (K - j) := by
  norm_num [j, K, t, L, w, m, b, q]

theorem pow_mul_linear_le_one (x : ℝ) (hx : 0 ≤ x) (r : ℕ) :
    (1 + x) ^ r * (1 - r * x) ≤ 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp : 0 ≤ (1 + x) ^ r := pow_nonneg (by linarith) _
    have hs : (1 + x) * (1 - ((r : ℝ) + 1) * x) ≤ 1 - r * x := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ r + 1 by positivity) (sq_nonneg x)]
    have hm := mul_le_mul_of_nonneg_left hs hp
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem pow_sub_one_le_twice (x : ℝ) (hx : 0 ≤ x) (r : ℕ)
    (hr : (r : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ r - 1 ≤ 2 * r * x := by
  have hp : 1 ≤ (1 + x) ^ r := one_le_pow₀ (by linarith)
  have h := pow_mul_linear_le_one x hx r
  have hm := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hr)
  nlinarith

theorem soft_error_bound :
    (1 + 1 / (2 : ℝ) ^ 256) ^ t - 1 < 1 / (2 : ℝ) ^ 190 := by
  have h := pow_sub_one_le_twice (1 / (2 : ℝ) ^ 256) (by positivity) t
    (by norm_num [t, b, q])
  have hc : 2 * (t : ℝ) * (1 / (2 : ℝ) ^ 256) < 1 / (2 : ℝ) ^ 190 := by
    norm_num [t, b, q]
  exact lt_of_le_of_lt h hc

theorem exp_neg_nat_le (r : ℕ) : Real.exp (-(r : ℝ)) ≤ 1 / (2 : ℝ) ^ r := by
  calc
    Real.exp (-(r : ℝ)) = Real.exp (-1) ^ r := by
      simpa using Real.exp_nat_mul (-1) r
    _ ≤ (1 / 2 : ℝ) ^ r :=
      pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le _
    _ = 1 / (2 : ℝ) ^ r := by rw [one_div_pow]

theorem hard_error_bound :
    5 * Real.exp (-(b : ℝ) / 500) < 1 / (2 : ℝ) ^ 300 := by
  have hb : -(b : ℝ) / 500 < -(310 : ℝ) := by norm_num [b, q]
  have he := Real.exp_lt_exp.mpr hb
  have h := exp_neg_nat_le 310
  norm_num only [Nat.cast_ofNat] at h
  have hn : 5 * (1 / (2 : ℝ) ^ 310) < 1 / (2 : ℝ) ^ 300 := by norm_num
  linarith

theorem noise_error_bound :
    2 * Real.exp (-(b : ℝ) / (5000 * w * (6 * q + 9))) <
      1 / (2 : ℝ) ^ 278 := by
  have hb : -(b : ℝ) / (5000 * w * (6 * q + 9)) < -(279 : ℝ) := by
    norm_num [b, q, w]
  have he := Real.exp_lt_exp.mpr hb
  have h := exp_neg_nat_le 279
  norm_num only [Nat.cast_ofNat] at h
  have hn : 2 * (1 / (2 : ℝ) ^ 279) = 1 / (2 : ℝ) ^ 278 := by norm_num
  linarith

theorem combined_error_bound (s h c : ℝ)
    (hs : s ≤ 1 / (2 : ℝ) ^ 190) (hh : h ≤ 1 / (2 : ℝ) ^ 300)
    (hc : c ≤ 1 / (2 : ℝ) ^ 278) :
    s + h + c < 1 / (2 : ℝ) ^ 189 := by
  have hn : 1 / (2 : ℝ) ^ 190 + 1 / (2 : ℝ) ^ 300 +
      1 / (2 : ℝ) ^ 278 < 1 / (2 : ℝ) ^ 189 := by norm_num
  linarith

theorem good_phase_mass_bound (s h c : ℝ)
    (hs : s ≤ 1 / (2 : ℝ) ^ 190) (hh : h ≤ 1 / (2 : ℝ) ^ 300)
    (hc : c ≤ 1 / (2 : ℝ) ^ 278) :
    1 / 3 < (1 - s) * (1 / 2 - h) * (1 - c) := by
  have hs' : s ≤ 1 / 100 := le_trans hs (by norm_num)
  have hh' : h ≤ 1 / 100 := le_trans hh (by norm_num)
  have hc' : c ≤ 1 / 100 := le_trans hc (by norm_num)
  have hprod : 0 ≤ (1 - s) * (1 / 2 - h) :=
    mul_nonneg (by linarith) (by linarith)
  have hp : (99 / 100 : ℝ) * (49 / 100) * (99 / 100) ≤
      (1 - s) * (1 / 2 - h) * (1 - c) := by
    gcongr <;> linarith
  linarith

end Research.DominationParameters

#print axioms Research.DominationParameters.q_prime
#print axioms Research.DominationParameters.valley_before_right
#print axioms Research.DominationParameters.soft_error_bound
#print axioms Research.DominationParameters.hard_error_bound
#print axioms Research.DominationParameters.noise_error_bound
#print axioms Research.DominationParameters.good_phase_mass_bound
