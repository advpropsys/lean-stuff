import Mathlib

/-! Reusable analytic bounds for the domination manuscript. These results do
not construct the graph or identify a counting distribution with a product
measure. All independence, measurability and boundedness hypotheses appear
explicitly below. -/

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

namespace Research.DominationConcentration

/-- The two-sided form of Mathlib's sub-Gaussian tail bound. -/
theorem subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * c)) := by
  have hs : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hs]
  have hp := hX.measure_ge_le hu
  have hn := hX.neg.measure_ge_le hu
  have hh := measureReal_union_le (μ := μ) {ω | u ≤ X ω} {ω | u ≤ -X ω}
  change μ.real {ω | u ≤ -X ω} ≤ _ at hn
  linarith

/-- Hoeffding for a finite sum of independent centered variables, each in an
interval of length one. In particular it applies to centered Bernoulli
variables, with arbitrary success probabilities. -/
theorem bounded_sum_abs_tail {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hind : iIndepFun X μ) (s : Finset ι) (a : ι → ℝ)
    (hmeas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (a i + 1))
    (hzero : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0)
    {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |∑ i ∈ s, X i ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * ((s.card : ℝ) / 4))) := by
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (X i) (1 / 4) μ := by
    intro i hi
    have hh := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hmeas i hi) (hbound i hi) (hzero i hi)
    norm_num at hh ⊢
    exact hh
  have hh := subgaussian_abs_tail
    (HasSubgaussianMGF.sum_of_iIndepFun hind hsub) hu
  simpa using hh

/-- An exact finite weighted-binomial lower-tail bound. The parameter z is
the exponential tilt used in the manuscript's minority-cell entropy bound.
There are no probability or integrality assumptions on the real cutoff r. -/
theorem weighted_binomial_lower_tail (b : ℕ) (c z r : ℝ)
    (hc : 0 ≤ c) (hz : 0 < z) (hz1 : z ≤ 1) :
    (∑ i ∈ (range (b + 1)).filter (fun i : ℕ => (i : ℝ) ≤ r),
      (b.choose i : ℝ) * c ^ i) ≤
      (1 + c * z) ^ b * Real.exp (-r * Real.log z) := by
  let S := (range (b + 1)).filter (fun i : ℕ => (i : ℝ) ≤ r)
  have hlog : Real.log z ≤ 0 := Real.log_nonpos (le_of_lt hz) hz1
  have hterm (i : ℕ) (hi : i ∈ S) :
      (b.choose i : ℝ) * c ^ i ≤
        ((b.choose i : ℝ) * (c * z) ^ i) * Real.exp (-r * Real.log z) := by
    have hir : (i : ℝ) ≤ r := (mem_filter.mp hi).2
    have he : 1 ≤ z ^ i * Real.exp (-r * Real.log z) := by
      have hzpow : z ^ i = Real.exp ((i : ℝ) * Real.log z) := by
        rw [Real.exp_nat_mul, Real.exp_log hz]
      rw [hzpow, ← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by nlinarith)
    have hnon : 0 ≤ (b.choose i : ℝ) * c ^ i := by positivity
    calc
      (b.choose i : ℝ) * c ^ i ≤
        ((b.choose i : ℝ) * c ^ i) *
          (z ^ i * Real.exp (-r * Real.log z)) := le_mul_of_one_le_right hnon he
      _ = _ := by rw [mul_pow]; ring
  have hsum : (∑ i ∈ range (b + 1), (b.choose i : ℝ) * (c * z) ^ i) =
      (1 + c * z) ^ b := by
    simpa [mul_comm, add_comm] using (add_pow (c * z) (1 : ℝ) b).symm
  calc
    _ ≤ ∑ i ∈ S, ((b.choose i : ℝ) * (c * z) ^ i) *
        Real.exp (-r * Real.log z) := sum_le_sum hterm
    _ = (∑ i ∈ S, (b.choose i : ℝ) * (c * z) ^ i) *
        Real.exp (-r * Real.log z) := by rw [sum_mul]
    _ ≤ (∑ i ∈ range (b + 1), (b.choose i : ℝ) * (c * z) ^ i) *
        Real.exp (-r * Real.log z) := by
      gcongr
      exact filter_subset _ _
    _ = _ := by rw [hsum]

/-- Exponential form of the same bound, with a fractional cutoff. -/
theorem weighted_binomial_entropy (b : ℕ) (c z ε : ℝ)
    (hc : 0 ≤ c) (hz : 0 < z) (hz1 : z ≤ 1) :
    (∑ i ∈ (range (b + 1)).filter (fun i : ℕ => (i : ℝ) ≤ ε * b),
      (b.choose i : ℝ) * c ^ i) ≤
      Real.exp ((b : ℝ) * (Real.log (1 + c * z) - ε * Real.log z)) := by
  have h := weighted_binomial_lower_tail b c z (ε * b) hc hz hz1
  have he : (1 + c * z) ^ b = Real.exp ((b : ℝ) * Real.log (1 + c * z)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [he, ← Real.exp_add] at h
  convert h using 1
  congr 1
  ring

private theorem log_29997_lt : Real.log 29997 < (43 : ℝ) / 4 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  have h10 : ((8 : ℝ) / 3) ^ 10 ≤ Real.exp 10 := by
    calc
      _ ≤ (Real.exp 1) ^ 10 := by
        gcongr
        linarith [Real.exp_one_gt_d9]
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hfrac : (7 : ℝ) / 4 ≤ Real.exp (3 / 4) := by
    have := Real.add_one_le_exp (3 / 4 : ℝ)
    linarith
  have hm := mul_le_mul h10 hfrac (by norm_num : (0 : ℝ) ≤ 7 / 4)
    (Real.exp_pos 10).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  linarith

/-- The manuscript's explicit minority-state estimate, valid for every b.
The weak inequality also covers b=0. -/
theorem minority_states_bound (b : ℕ) :
    (∑ i ∈ (range (b + 1)).filter (fun i : ℕ => (i : ℝ) ≤ (b : ℝ) / 10000),
      (b.choose i : ℝ) * (3 : ℝ) ^ i) ≤
      Real.exp ((3 : ℝ) * b / 2500) := by
  have h := weighted_binomial_entropy b 3 (1 / 29997) (1 / 10000)
    (by norm_num) (by norm_num) (by norm_num)
  have hl : Real.log (1 + (3 : ℝ) * (1 / 29997)) ≤ (1 : ℝ) / 9999 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 + 3 * (1 / 29997))
    norm_num at hh ⊢
    exact hh
  have hz : Real.log ((1 : ℝ) / 29997) = -Real.log 29997 := by
    rw [one_div, Real.log_inv]
  have he : Real.log (1 + (3 : ℝ) * (1 / 29997)) -
      (1 / 10000) * Real.log (1 / 29997) ≤ (3 : ℝ) / 2500 := by
    rw [hz]
    linarith [log_29997_lt]
  have hh : Real.exp ((b : ℝ) * (Real.log (1 + (3 : ℝ) * (1 / 29997)) -
      (1 / 10000) * Real.log (1 / 29997))) ≤ Real.exp ((3 : ℝ) * b / 2500) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ (b : ℝ) * (3 / 2500) := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg b)
      _ = _ := by ring
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h.trans hh

end Research.DominationConcentration

#print axioms Research.DominationConcentration.bounded_sum_abs_tail
#print axioms Research.DominationConcentration.weighted_binomial_lower_tail
#print axioms Research.DominationConcentration.minority_states_bound
