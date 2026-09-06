import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Analytic estimates for the alternating Motzkin root inequality.
These lemmas are generic; the recurrence module must discharge their hypotheses.
-/
namespace Research.MotzkinAnalysis
open Real

theorem log_constant : (15 : ℝ) / 4 < log (531441 / 11299) := by
  have h2 := Real.log_two_gt_d9
  have h7 := Real.one_sub_inv_le_log_of_pos (x := (7 : ℝ) / 5) (by norm_num)
  norm_num at h7
  have hprod : log ((2 : ℝ)^5 * (7 / 5)) = 5 * log 2 + log (7 / 5) := by
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hmono : log ((2 : ℝ)^5 * (7 / 5)) < log (531441 / 11299) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

theorem previous_log_bound {n p : ℝ} (hn : 1 ≤ n)
    (hp : 6 * n / (2 * n + 3) ≤ p) :
    -(3 / 2 : ℝ) ≤ n * (log p - log 3) := by
  have hn0 : 0 < n := by linarith
  have hd : 0 < 2 * n + 3 := by linarith
  have hb : 0 < 6 * n / (2 * n + 3) := div_pos (by positivity) hd
  have hp0 : 0 < p := lt_of_lt_of_le hb hp
  have hlog := Real.one_sub_inv_le_log_of_pos (x := p / 3) (by positivity)
  rw [Real.log_div (ne_of_gt hp0) (by norm_num)] at hlog
  have hmul : 6 * n ≤ p * (2 * n + 3) := (div_le_iff₀ hd).mp hp
  have hinv : 3 / p ≤ (2 * n + 3) / (2 * n) := by
    apply (div_le_div_iff₀ hp0 (by positivity)).mpr
    nlinarith
  have hrewrite : (p / 3)⁻¹ = 3 / p := by field_simp
  rw [hrewrite] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hn0)
  have hi := mul_le_mul_of_nonneg_left hinv (le_of_lt hn0)
  have hid : n * ((2 * n + 3) / (2 * n)) = n + 3 / 2 := by
    field_simp
  rw [hid] at hi
  nlinarith

theorem ratio_log_bound {n p q : ℝ} (hn : 1 ≤ n)
    (hp : 6 * n / (2 * n + 3) ≤ p) (hq0 : 0 < q)
    (hq : q ≤ 6 * (n + 3) / (2 * n + 9)) :
    n * (n - 1) * (log q - log p) ≤ (9 : ℝ) / 2 := by
  have hn0 : 0 < n := by linarith
  have hd3 : 0 < 2 * n + 3 := by linarith
  have hd9 : 0 < 2 * n + 9 := by linarith
  have hb : 0 < 6 * n / (2 * n + 3) := div_pos (by positivity) hd3
  have hp0 : 0 < p := lt_of_lt_of_le hb hp
  have hr : q / p ≤ (6 * (n + 3) / (2 * n + 9)) /
      (6 * n / (2 * n + 3)) :=
    div_le_div₀ (by positivity) hq hb hp
  have hid : (6 * (n + 3) / (2 * n + 9)) / (6 * n / (2 * n + 3)) =
      1 + 9 / (n * (2 * n + 9)) := by
    field_simp
    ring
  rw [hid] at hr
  have hlog := Real.log_le_sub_one_of_pos (x := q / p) (by positivity)
  rw [Real.log_div (ne_of_gt hq0) (ne_of_gt hp0)] at hlog
  have hm : 0 ≤ n * (n - 1) := mul_nonneg (by linarith) (by linarith)
  have hh := mul_le_mul_of_nonneg_left (show log q - log p ≤
      9 / (n * (2 * n + 9)) by linarith) hm
  have hid2 : n * (n - 1) * (9 / (n * (2 * n + 9))) =
      9 * (n - 1) / (2 * n + 9) := by field_simp
  rw [hid2] at hh
  have hlast : 9 * (n - 1) / (2 * n + 9) ≤ (9 : ℝ) / 2 := by
    apply (div_le_iff₀ hd9).mpr
    linarith
  exact hh.trans hlast

theorem concavity_numerator_positive {n L p q : ℝ} (hn : 1 ≤ n)
    (hp : 6 * n / (2 * n + 3) ≤ p) (hq0 : 0 < q)
    (hq : q ≤ 6 * (n + 3) / (2 * n + 9))
    (hL : L ≤ n * log 3 - log (531441 / 11299)) :
    0 < -2 * L + n * (n + 1) * log p - n * (n - 1) * log q := by
  have hprev := previous_log_bound hn hp
  have hratio := ratio_log_bound hn hp hq0 hq
  have hc := log_constant
  nlinarith

theorem log_growth_bound (a : ℕ → ℝ)
    (hpos : ∀ n, 9 ≤ n → 0 < a n)
    (hupper : ∀ n, 9 ≤ n → a (n + 1) / a n ≤
      6 * ((n : ℝ) + 3) / (2 * n + 9))
    (hbase : a 12 = 11299) (k : ℕ) :
    log (a (k + 12)) ≤ ((k : ℝ) + 12) * log 3 - log (531441 / 11299) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_add, hbase]
    have hc : log (531441 / (11299 : ℝ)) = 12 * log 3 - log 11299 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      congr 1
      have h := Real.log_pow (3 : ℝ) 12
      norm_num at h
      exact h
    rw [hc]
    linarith
  | succ k ih =>
    have hp := hpos (k + 12) (by omega)
    have hq := hpos (k + 12 + 1) (by omega)
    have hu := hupper (k + 12) (by omega)
    have hb : 6 * (((k + 12 : ℕ) : ℝ) + 3) / (2 * (k + 12 : ℕ) + 9) ≤ 3 := by
      apply (div_le_iff₀ (by positivity)).mpr
      push_cast
      linarith
    have hl := Real.log_le_log (div_pos hq hp) (hu.trans hb)
    rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)] at hl
    have hi : k + 1 + 12 = k + 12 + 1 := by omega
    simp only [hi, Nat.cast_add, Nat.cast_one]
    linarith

theorem tail_log_concavity (a : ℕ → ℝ)
    (hpos : ∀ n, 9 ≤ n → 0 < a n)
    (hbounds : ∀ n : ℕ, 9 ≤ n →
      6 * ((n : ℝ) + 1) / (2 * n + 5) ≤ a (n + 1) / a n ∧
      a (n + 1) / a n ≤ 6 * ((n : ℝ) + 3) / (2 * n + 9))
    (hbase : a 12 = 11299) (k : ℕ) :
    log (a (k + 11)) / ((k : ℝ) + 11) +
      log (a (k + 13)) / ((k : ℝ) + 13) <
      2 * log (a (k + 12)) / ((k : ℝ) + 12) := by
  have hp11 := hpos (k + 11) (by omega)
  have hp12 := hpos (k + 12) (by omega)
  have hp13 := hpos (k + 13) (by omega)
  have hb11 := (hbounds (k + 11) (by omega)).1
  have hb12 := (hbounds (k + 12) (by omega)).2
  have hL := log_growth_bound a hpos (fun n hn => (hbounds n hn).2) hbase k
  have hprev : 6 * ((k : ℝ) + 12) / (2 * ((k : ℝ) + 12) + 3) ≤
      a (k + 12) / a (k + 11) := by
    convert hb11 using 1
    push_cast
    ring
  have hnext : a (k + 13) / a (k + 12) ≤
      6 * (((k : ℝ) + 12) + 3) / (2 * ((k : ℝ) + 12) + 9) := by
    convert hb12 using 1
    push_cast
    ring
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hD := concavity_numerator_positive (n := (k : ℝ) + 12)
    (L := log (a (k + 12))) (by linarith) hprev (div_pos hp13 hp12) hnext hL
  rw [Real.log_div (ne_of_gt hp12) (ne_of_gt hp11),
    Real.log_div (ne_of_gt hp13) (ne_of_gt hp12)] at hD
  have h11 : 0 < (k : ℝ) + 11 := by positivity
  have h12 : 0 < (k : ℝ) + 12 := by positivity
  have h13 : 0 < (k : ℝ) + 13 := by positivity
  apply (lt_div_iff₀ h12).mpr
  rw [add_mul, div_mul_eq_mul_div, div_mul_eq_mul_div]
  apply (div_add_div _ _ (ne_of_gt h11) (ne_of_gt h13) ▸
    (div_lt_iff₀ (mul_pos h11 h13)).mpr ?_)
  nlinarith

end Research.MotzkinAnalysis
