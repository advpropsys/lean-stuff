import Research.DominationParameters

/-! Exact scalar and analytic certificates for the smaller projective
candidate. This file does not assert its graph has a nonunimodal polynomial.
The canonical construction and constants are unchanged. -/

noncomputable section
namespace Research.DominationSmallParameters

set_option exponentiation.threshold 1024

def q : ℕ := 4194301
def w : ℕ := 100
def b : ℕ := q ^ 2 + q + 1
def t : ℕ := 5 * b
def m : ℕ := b * (6 * q + 9)
def L : ℕ := w * m
def n : ℕ := t + L
def K : ℕ := t + L / 2
def j : ℕ := K - 108 * b / 125
def ε : ℝ := 1 / 1500
def a : ℝ := 2 / 25
def c : ℝ := 57 / 1000
def r : ℝ := 11 / 200
def E : ℝ := 19 / 3000
def η : ℝ := 1 / 15000

set_option maxHeartbeats 2000000 in
theorem q_prime : Nat.Prime q := by norm_num [q]

theorem scalar_values : q = 2 ^ 22 - 3 ∧ b = 17592165072903 ∧
    m = 442721171674138410945 ∧ L = 44272117167413841094500 ∧
    n = 44272117255374666459015 := by norm_num [q, b, m, L, n, t, w]

theorem disperser_strict : q * 1500 ^ 2 < (q + 1) ^ 2 := by norm_num [q]

theorem entropy_helpers : (27 : ℝ) / 10 < 65 / 24 ∧
    4500 ^ 2 * 10 ^ 17 < (27 : ℕ) ^ 17 ∧ ε * (1 + 17 / 2) = E := by
  norm_num [ε, E]

theorem log4500_lt : Real.log 4500 < (17 : ℝ) / 2 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have hp : ((27 : ℝ) / 10) ^ 17 ≤ (Real.exp 1) ^ 17 := by
    gcongr
    linarith [Real.exp_one_gt_d9]
  have he : (Real.exp 1) ^ 17 = (Real.exp ((17 : ℝ) / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hp
  have hn : (4500 : ℝ) ^ 2 < (27 / 10 : ℝ) ^ 17 := by norm_num
  have hpos := Real.exp_pos ((17 : ℝ) / 2)
  nlinarith

theorem entropy_upper : ε * (1 + Real.log (3 / ε)) < E := by
  norm_num only [ε, E, div_div, div_one, OfNat.ofNat_ne_zero, mul_comm] at *
  linarith [log4500_lt]

/-- Directly matches the generic minority-word entropy lemma's tilt. -/
theorem optimized_entropy_upper :
    Real.log (1 + (3 : ℝ) * (1 / 4497)) - ε * Real.log (1 / 4497) < E := by
  have hy : Real.log ((1500 : ℝ) / 1499) ≤ (1 : ℝ) / 1499 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1500 / 1499)
    norm_num at h ⊢
    exact h
  have hz : Real.log ((1 : ℝ) / 4497) =
      Real.log ((1500 : ℝ) / 1499) - Real.log 4500 := by
    rw [show (1 : ℝ) / 4497 = (1500 / 1499) / 4500 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  rw [show (1 : ℝ) + 3 * (1 / 4497) = 1500 / 1499 by norm_num, hz]
  unfold ε E
  linarith [log4500_lt]

theorem hard_margins : a ^ 2 - E = η ∧ η < 2 * c ^ 2 - E ∧ η < 1 - 2 * E := by
  norm_num [a, c, E, η]

theorem hard_exponent : (110 : ℝ) < η * b := by norm_num [η, b, q]

theorem hard_error_bound : 5 * Real.exp (-(b : ℝ) / 15000) < 1 / (2 : ℝ) ^ 100 := by
  have hb : -(b : ℝ) / 15000 < -(110 : ℝ) := by norm_num [b, q]
  have he := Real.exp_lt_exp.mpr hb
  have hh := DominationParameters.exp_neg_nat_le 110
  norm_num only [Nat.cast_ofNat] at hh
  have hn : 5 * (1 / (2 : ℝ) ^ 110) < 1 / (2 : ℝ) ^ 100 := by norm_num
  linarith

theorem soft_smallness : (t : ℝ) / (2 : ℝ) ^ w < 1 / 2 := by norm_num [t, b, q, w]
theorem soft_scalar_bound : 2 * (t : ℝ) / (2 : ℝ) ^ w < 1 / (2 : ℝ) ^ 52 := by
  norm_num [t, b, q, w]

theorem soft_error_bound : (1 + 1 / (2 : ℝ) ^ w) ^ t - 1 < 1 / (2 : ℝ) ^ 52 := by
  have hs : (t : ℝ) * (1 / (2 : ℝ) ^ w) ≤ 1 / 2 := by norm_num [t, b, q, w]
  have h := DominationParameters.pow_sub_one_le_twice (1 / (2 : ℝ) ^ w)
    (div_nonneg (by norm_num) (pow_nonneg (by norm_num) _)) t hs
  have hh : 2 * (t : ℝ) * (1 / (2 : ℝ) ^ w) < 1 / (2 : ℝ) ^ 52 := by
    norm_num [t, b, q, w]
  exact h.trans_lt hh

theorem noise_exponent : (42 : ℝ) < 2 * r ^ 2 * b / (w * (6 * q + 9)) := by
  norm_num [r, b, q, w]

theorem exp_neg_one_le : Real.exp (-1) ≤ (10 : ℝ) / 27 := by
  rw [Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  linarith [Real.exp_one_gt_d9]

theorem noise_power_bound : 2 * ((10 : ℝ) / 27) ^ 42 < 1 / (2 : ℝ) ^ 59 := by norm_num

theorem noise_error_bound :
    2 * Real.exp (-(2 * r ^ 2 * b / (w * (6 * q + 9)))) < 1 / (2 : ℝ) ^ 59 := by
  have hx : Real.exp (-(2 * r ^ 2 * b / (w * (6 * q + 9)))) < Real.exp (-42) :=
    Real.exp_lt_exp.mpr (neg_lt_neg noise_exponent)
  have he : Real.exp (-42) ≤ ((10 : ℝ) / 27) ^ 42 := by
    calc
      _ = Real.exp (-1) ^ 42 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le _
  linarith [noise_power_bound]

theorem combined_error_bound (s h d : ℝ)
    (hs : s ≤ 1 / (2 : ℝ) ^ 52) (hh : h ≤ 1 / (2 : ℝ) ^ 100)
    (hd : d ≤ 1 / (2 : ℝ) ^ 59) : s + h + d < 1 / (2 : ℝ) ^ 51 := by
  have hn : 1 / (2 : ℝ) ^ 52 + 1 / (2 : ℝ) ^ 100 + 1 / (2 : ℝ) ^ 59 <
      1 / (2 : ℝ) ^ 51 := by norm_num
  linarith

theorem mass_scalar_bound : (1 - 1 / (2 : ℝ) ^ 52) *
    (1 / 2 - 1 / (2 : ℝ) ^ 100) * (1 - 1 / (2 : ℝ) ^ 59) > 1 / 3 := by norm_num

theorem good_phase_mass_bound (s h d : ℝ)
    (hs : s ≤ 1 / (2 : ℝ) ^ 52) (hh : h ≤ 1 / (2 : ℝ) ^ 100)
    (hd : d ≤ 1 / (2 : ℝ) ^ 59) : 1 / 3 < (1 - s) * (1 / 2 - h) * (1 - d) := by
  apply mass_scalar_bound.trans_le
  apply mul_le_mul
  · apply mul_le_mul <;> linarith
  · linarith
  · norm_num
  · exact mul_nonneg (by linarith) (by linarith)

theorem interval_formulas :
    1 + a + ε + r = (3407 : ℝ) / 3000 ∧ 1 - a - r = (173 : ℝ) / 200 ∧
    3 / 4 + c + 2 * ε + r = (259 : ℝ) / 300 ∧ 3 / 4 - c - r = (319 : ℝ) / 500 ∧
    2 * a + ε + 2 * r = (203 : ℝ) / 750 ∧
    2 * c + 2 * ε + 2 * r = (169 : ℝ) / 750 ∧
    a + c + 2 * ε + 2 * r < 1 / 4 := by norm_num [a, c, ε, r]

theorem interval_widths : (203 : ℝ) / 750 * b < b ∧ (169 : ℝ) / 750 * b < b := by
  norm_num [b, q]

theorem floors_and_center : 200 * (108 * b / 125) < 173 * b ∧
    259 * b < 300 * (108 * b / 125) ∧ 0 < j ∧ j < n ∧ L % 2 = 0 := by
  norm_num [j, K, n, t, L, m, b, q, w]

theorem real_intervals_and_center :
    0 ≤ (K : ℝ) - 3407 / 3000 * b ∧
    (K : ℝ) - 3407 / 3000 * b < K - 173 / 200 * b ∧
    (K : ℝ) - 173 / 200 * b < j ∧
    (j : ℝ) < K - 259 / 300 * b ∧
    (K : ℝ) - 259 / 300 * b < K - 319 / 500 * b ∧
    (K : ℝ) - 319 / 500 * b ≤ n := by
  norm_num [j, K, n, t, L, m, b, q, w]

theorem pigeonhole_bounds : b + 1 ≤ 2 ^ 44 ∧
    1 / (2 : ℝ) ^ 46 < 1 / (3 * ((b : ℝ) + 1)) ∧
    1 / (2 : ℝ) ^ 51 < 1 / (2 : ℝ) ^ 46 := by norm_num [b, q]

theorem reduction_factor : 343000000 * n < DominationParameters.n := by
  rw [DominationParameters.n_value]
  norm_num [n, t, L, m, b, q, w]

end Research.DominationSmallParameters

#print axioms Research.DominationSmallParameters.q_prime
#print axioms Research.DominationSmallParameters.entropy_upper
#print axioms Research.DominationSmallParameters.optimized_entropy_upper
#print axioms Research.DominationSmallParameters.noise_error_bound
#print axioms Research.DominationSmallParameters.good_phase_mass_bound
#print axioms Research.DominationSmallParameters.real_intervals_and_center
