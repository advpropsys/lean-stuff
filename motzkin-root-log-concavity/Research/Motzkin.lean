import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Research.MotzkinFinite

/-!
# Alternating Motzkin root inequality: recurrence and ratio bounds

The definitions below use the standard Motzkin recurrence over the rationals.
The universal inequality is proved in `Research.MotzkinTheorem`.
This module proves the alternating-sum identity, universal ratio enclosure, finite
logarithmic cases, and the conversion from logarithmic inequalities to real roots.
-/
namespace Research.Motzkin

/-- The standard Motzkin numbers, represented in ℚ. -/
def M : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | n + 2 => (((2 : ℚ) * (n + 1) + 3) * M (n + 1) +
      3 * (n + 1) * M n) / (n + 4)

/-- Alternating Motzkin sums; equivalently `T (n+1) + T n = M (n+1)`. -/
def T : ℕ → ℚ
  | 0 => 1
  | n + 1 => M (n + 1) - T n

def b (k : ℚ) : ℚ := 6 * (k + 1) / (2 * k + 5)
def f (k t : ℚ) : ℚ := (2 * k + 3) / (k + 3) + 3 * k / ((k + 3) * t)
def x (k : ℕ) : ℚ := M (k + 1) / M k

theorem T_add_previous (n : ℕ) : T (n + 1) + T n = M (n + 1) := by
  simp [T]

/-- The recursively defined T is exactly the alternating sum in Zhao's conjecture. -/
theorem T_eq_alternating_sum (n : ℕ) :
    T n = ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - j) * M j := by
  induction n with
  | zero => norm_num [T, M]
  | succ n ih =>
    rw [T, Finset.sum_range_succ]
    have hs : (∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n + 1 - j) * M j) =
        -(∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - j) * M j) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
      ring
    rw [hs, Nat.sub_self, pow_zero, one_mul, ← ih]
    ring

theorem M_positive (n : ℕ) : 0 < M n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [M]
  | one => norm_num [M]
  | more n ih0 ih1 =>
    rw [M]
    positivity

theorem x_positive (n : ℕ) : 0 < x n := div_pos (M_positive _) (M_positive _)

theorem x_recurrence (n : ℕ) : x (n + 1) = f (n + 1) (x n) := by
  have hn := ne_of_gt (M_positive n)
  have hn1 := ne_of_gt (M_positive (n + 1))
  have hd : (n : ℚ) + 4 ≠ 0 := by positivity
  simp only [x, M, f]
  field_simp
  ring

theorem b_positive {k : ℚ} (hk : 0 ≤ k) : 0 < b k := by
  unfold b
  positivity

theorem b_mono {k l : ℚ} (hk : 0 ≤ k) (hkl : k ≤ l) : b k ≤ b l := by
  have hkd : 0 < 2 * k + 5 := by linarith
  have hld : 0 < 2 * l + 5 := by linarith
  unfold b
  apply (div_le_div_iff₀ hkd hld).2
  nlinarith

theorem f_antitone {k s t : ℚ} (hk : 0 ≤ k) (hs : 0 < s) (hst : s ≤ t) :
    f k t ≤ f k s := by
  unfold f
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  exact mul_le_mul_of_nonneg_left hst (by positivity)

theorem f_b_lower {k : ℚ} (hk : 2 ≤ k) : b k ≤ f k (b k) := by
  have hk3 : 0 < k + 3 := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have hk5 : 0 < 2 * k + 5 := by linarith
  have hid : f k (b k) - b k =
      3 * (k - 2) / (2 * (k + 3) * (k + 1) * (2 * k + 5)) := by
    unfold f b
    field_simp
    ring
  have hk2 : 0 ≤ k - 2 := by linarith
  have hnonneg : 0 ≤ 3 * (k - 2) / (2 * (k + 3) * (k + 1) * (2 * k + 5)) := by
    positivity
  linarith

theorem f_b_upper {k : ℚ} (hk : 2 ≤ k) : f k (b (k - 1)) ≤ b (k + 1) := by
  have hk0 : 0 < k := by linarith
  have hk3 : 0 < k + 3 := by linarith
  have hk7 : 0 < 2 * k + 7 := by linarith
  have hid : b (k + 1) - f k (b (k - 1)) = 9 / (2 * (k + 3) * (2 * k + 7)) := by
    unfold f b
    simp only [sub_add_cancel]
    field_simp [ne_of_gt hk0]
    ring
  have hnonneg : 0 ≤ 9 / (2 * (k + 3) * (2 * k + 7)) := by positivity
  linarith

theorem x_bounds (n : ℕ) :
    b ((n : ℚ) + 2) ≤ x (n + 2) ∧ x (n + 2) ≤ b ((n : ℚ) + 3) := by
  induction n with
  | zero => norm_num [b, x, M]
  | succ n ih =>
    have hn : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
    have hr : x (n + 1 + 2) = f ((n : ℚ) + 3) (x (n + 2)) := by
      convert x_recurrence (n + 2) using 1
      push_cast
      ring_nf
    rw [hr]
    simp only [Nat.cast_add, Nat.cast_one]
    constructor
    · calc
        b (↑n + 1 + 2) = b (↑n + 3) := by ring_nf
        _ ≤ f (↑n + 3) (b (↑n + 3)) := f_b_lower (by linarith)
        _ ≤ f (↑n + 3) (x (n + 2)) :=
          f_antitone (by positivity) (x_positive _) ih.2
    · calc
        f (↑n + 3) (x (n + 2)) ≤ f (↑n + 3) (b (↑n + 2)) :=
          f_antitone (by positivity) (b_positive (by positivity)) ih.1
        _ ≤ b (↑n + 1 + 3) := by
          convert f_b_upper (k := (n : ℚ) + 3) (by linarith) using 1 <;> ring_nf

theorem x_ge_two (n : ℕ) : 2 ≤ x (n + 2) := by
  calc
    2 = b 2 := by norm_num [b]
    _ ≤ b ((n : ℚ) + 2) := b_mono (by norm_num) (by have := Nat.cast_nonneg (α := ℚ) n; linarith)
    _ ≤ x (n + 2) := (x_bounds n).1

theorem T_recurrence (n : ℕ) :
    T (n + 2) = (x (n + 1) - 1) * T (n + 1) + x (n + 1) * T n := by
  have hm : M (n + 1) ≠ 0 := ne_of_gt (M_positive _)
  have ht := T_add_previous n
  rw [show T (n + 2) = M (n + 2) - T (n + 1) from rfl]
  unfold x
  field_simp
  nlinarith [congrArg (fun z : ℚ => M (n + 2) * z) ht]

theorem T_positive (n : ℕ) : 0 < T (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [T, M]
  | one => norm_num [T, M]
  | more n ih0 ih1 =>
    rw [T_recurrence (n + 2)]
    have hx : 2 ≤ x (n + 2 + 1) := by
      convert x_ge_two (n + 1) using 1
    have h1 : 0 < (x (n + 2 + 1) - 1) * T (n + 2 + 1) := by
      apply mul_pos (by linarith)
      convert ih1 using 1
    have h2 : 0 < x (n + 2 + 1) * T (n + 2) := mul_pos (by linarith) ih0
    linarith

def y (k : ℕ) : ℚ := T (k + 1) / T k

theorem y_positive (n : ℕ) : 0 < y (n + 2) := by
  unfold y
  apply div_pos
  · convert T_positive (n + 1) using 1
  · exact T_positive n

theorem y_recurrence (n : ℕ) :
    y (n + 3) = x (n + 3) - 1 + x (n + 3) / y (n + 2) := by
  have ht2 : T (n + 2) ≠ 0 := ne_of_gt (T_positive n)
  have ht3 : T (n + 3) ≠ 0 := by
    convert ne_of_gt (T_positive (n + 1)) using 1
  have hr := T_recurrence (n + 2)
  unfold y
  have hi : n + 2 + 1 = n + 3 := by omega
  rw [hi] at hr ⊢
  field_simp
  nlinarith

def H (k t : ℚ) : ℚ :=
  f (k + 1) t - 1 + f (k + 1) t / t - f (k + 2) (f (k + 1) t)

theorem f_positive {k t : ℚ} (hk : 0 ≤ k) (ht : 0 < t) : 0 < f k t := by
  unfold f
  positivity

theorem H_antitone {k s t : ℚ} (hk : 0 ≤ k) (hs : 0 < s) (hst : s ≤ t) :
    H k t ≤ H k s := by
  have ht : 0 < t := hs.trans_le hst
  have hfp := f_positive (k := k + 1) (by linarith) ht
  have hf := f_antitone (k := k + 1) (by linarith) hs hst
  have hd : f (k + 1) t / t ≤ f (k + 1) s / s := by
    apply (div_le_div_iff₀ ht hs).2
    exact (mul_le_mul_of_nonneg_right hf hs.le).trans
      (mul_le_mul_of_nonneg_left hst (f_positive (by linarith) hs).le)
  have hff := f_antitone (k := k + 2) (by linarith) hfp hf
  unfold H
  linarith

theorem H_b_negative {k : ℚ} (hk : 9 ≤ k) : H k (b k) < 0 := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k + 1 := by linarith
  have hk4 : 0 < k + 4 := by linarith
  have hk5 : 0 < k + 5 := by linarith
  have hk25 : 0 < 2 * k + 5 := by linarith
  have hid : H k (b k) =
      -(3 * (4 * k^2 - 13*k - 53)) /
        (4 * (k + 1) * (k + 4) * (k + 5) * (2*k + 5)) := by
    unfold H f b
    field_simp
    ring
  rw [hid]
  have hp : 0 < 4 * k^2 - 13*k - 53 := by nlinarith
  apply div_neg_of_neg_of_pos
  · nlinarith
  · positivity

/-- Each alternating-sum ratio lies between two consecutive Motzkin ratios. -/
theorem y_sandwich (n : ℕ) :
    x (n + 9) ≤ y (n + 9) ∧ y (n + 9) ≤ x (n + 10) := by
  induction n with
  | zero => norm_num [x, y, M, T]
  | succ n ih =>
    change x (n + 10) ≤ y (n + 10) ∧ y (n + 10) ≤ x (n + 11)
    have hn : 0 ≤ (n : ℚ) := Nat.cast_nonneg n
    have hyp : 0 < y (n + 9) := y_positive (n + 7)
    have hr : y (n + 10) = x (n + 10) - 1 + x (n + 10) / y (n + 9) :=
      y_recurrence (n + 7)
    constructor
    · have hd : 1 ≤ x (n + 10) / y (n + 9) :=
        (le_div_iff₀ hyp).2 (by simpa using ih.2)
      linarith
    · have hd : x (n + 10) / y (n + 9) ≤ x (n + 10) / x (n + 9) :=
        div_le_div_of_nonneg_left (x_positive _).le (x_positive _) ih.1
      have hb : b ((n : ℚ) + 9) ≤ x (n + 9) := by
        convert (x_bounds (n + 7)).1 using 1; push_cast; ring_nf
      have hh : H ((n : ℚ) + 9) (x (n + 9)) < 0 :=
        lt_of_le_of_lt
          (H_antitone (by linarith) (b_positive (by linarith)) hb)
          (H_b_negative (by linarith))
      have hrx : f ((n : ℚ) + 9 + 1) (x (n + 9)) = x (n + 10) := by
        symm
        convert x_recurrence (n + 9) using 1
        push_cast
        ring_nf
      have hrx2 : f ((n : ℚ) + 9 + 2) (x (n + 10)) = x (n + 11) := by
        symm
        convert x_recurrence (n + 10) using 1
        push_cast
        ring_nf
      simp only [H, hrx, hrx2] at hh
      linarith

/-- The universal rational enclosure needed for root log-concavity. -/
theorem y_enclosure (n : ℕ) :
    b ((n : ℚ) + 9) ≤ y (n + 9) ∧ y (n + 9) ≤ b ((n : ℚ) + 11) := by
  have hl : b ((n : ℚ) + 9) ≤ x (n + 9) := by
    convert (x_bounds (n + 7)).1 using 1; push_cast; ring_nf
  have hu : x (n + 10) ≤ b ((n : ℚ) + 11) := by
    convert (x_bounds (n + 8)).2 using 1; push_cast; ring_nf
  exact ⟨hl.trans (y_sandwich n).1, (y_sandwich n).2.trans hu⟩

/-- An exact-power inequality implies logarithmic root concavity. -/
theorem log_concave_of_power {a c d : ℝ} (k : ℕ)
    (ha : 0 < a) (_hc : 0 < c) (hd : 0 < d)
    (hp : a ^ ((k + 2) * (k + 3)) * d ^ ((k + 2) * (k + 1)) <
      c ^ (2 * (k + 1) * (k + 3))) :
    Real.log a / ((k : ℝ) + 1) + Real.log d / ((k : ℝ) + 3) <
      2 * Real.log c / ((k : ℝ) + 2) := by
  have hl := Real.log_lt_log (show 0 < a ^ ((k + 2) * (k + 3)) *
    d ^ ((k + 2) * (k + 1)) by positivity) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hl
  push_cast at hl
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  field_simp
  nlinarith

/-- Passing from the logarithmic statement to the usual squared-root formulation. -/
theorem root_concave_of_log {a c d : ℝ} (k : ℕ)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hl : Real.log a / ((k : ℝ) + 1) + Real.log d / ((k : ℝ) + 3) <
      2 * Real.log c / ((k : ℝ) + 2)) :
    a ^ (1 / ((k : ℝ) + 1)) * d ^ (1 / ((k : ℝ) + 3)) <
      (c ^ (1 / ((k : ℝ) + 2))) ^ (2 : ℕ) := by
  apply (Real.log_lt_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_rpow ha, Real.log_rpow hd, Real.log_rpow hc]
  norm_num
  convert hl using 1 <;> ring

/-- The two exceptional centers from the paper proof, checked by exact arithmetic. -/
theorem center10_integer : (1586 : ℕ)^198 > 602^110 * 4212^90 := by norm_num

theorem center11_integer : (4212 : ℕ)^240 > 1586^132 * 11299^110 := by norm_num

theorem T9 : T 9 = 602 := by norm_num [T, M]
theorem T10 : T 10 = 1586 := by norm_num [T, M]
theorem T11 : T 11 = 4212 := by norm_num [T, M]
theorem T12 : T 12 = 11299 := by norm_num [T, M]

theorem center10_log :
    Real.log (T 9 : ℝ) / 9 + Real.log (T 11 : ℝ) / 11 <
      2 * Real.log (T 10 : ℝ) / 10 := by
  rw [T9, T10, T11]
  norm_cast
  convert log_concave_of_power (a := 602) (c := 1586) (d := 4212) 8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

theorem center11_log :
    Real.log (T 10 : ℝ) / 10 + Real.log (T 12 : ℝ) / 12 <
      2 * Real.log (T 11 : ℝ) / 11 := by
  rw [T10, T11, T12]
  norm_cast
  convert log_concave_of_power (a := 1586) (c := 4212) (d := 11299) 9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;> norm_num

theorem center6_log :
    Real.log (T 5 : ℝ) / 5 + Real.log (T 7 : ℝ) / 7 <
      2 * Real.log (T 6 : ℝ) / 6 := by
  norm_num [T, M]
  convert log_concave_of_power (a := 14) (c := 37) (d := 90) 4
    (by norm_num) (by norm_num) (by norm_num) (by
      exact_mod_cast Research.MotzkinFinite.center6) using 1 <;> norm_num

theorem center7_log :
    Real.log (T 6 : ℝ) / 6 + Real.log (T 8 : ℝ) / 8 <
      2 * Real.log (T 7 : ℝ) / 7 := by
  norm_num [T, M]
  convert log_concave_of_power (a := 37) (c := 90) (d := 233) 5
    (by norm_num) (by norm_num) (by norm_num) (by
      exact_mod_cast Research.MotzkinFinite.center7) using 1 <;> norm_num

theorem center8_log :
    Real.log (T 7 : ℝ) / 7 + Real.log (T 9 : ℝ) / 9 <
      2 * Real.log (T 8 : ℝ) / 8 := by
  norm_num [T, M]
  convert log_concave_of_power (a := 90) (c := 233) (d := 602) 6
    (by norm_num) (by norm_num) (by norm_num) (by
      exact_mod_cast Research.MotzkinFinite.center8) using 1 <;> norm_num

theorem center9_log :
    Real.log (T 8 : ℝ) / 8 + Real.log (T 10 : ℝ) / 10 <
      2 * Real.log (T 9 : ℝ) / 9 := by
  norm_num [T, M]
  convert log_concave_of_power (a := 233) (c := 602) (d := 1586) 7
    (by norm_num) (by norm_num) (by norm_num) (by
      exact_mod_cast Research.MotzkinFinite.center9) using 1 <;> norm_num

theorem center5_log_reverse :
    2 * Real.log (T 5 : ℝ) / 5 <
      Real.log (T 4 : ℝ) / 4 + Real.log (T 6 : ℝ) / 6 := by
  norm_num [T, M]
  have hp : (14 : ℝ)^48 < 7^30 * 37^20 := by
    exact_mod_cast Research.MotzkinFinite.center5_reverse
  have hl := Real.log_lt_log (by positivity) hp
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hl
  norm_num at hl
  linarith

end Research.Motzkin
