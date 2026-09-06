import Mathlib

/-!
Finite coefficient lemmas for the domination-polynomial investigation.
These statements contain no graph construction or probabilistic estimates.
All interval sums and coefficient bounds are explicit hypotheses.
-/

namespace Research.DominationValley

/-- Unimodality on the complete finite coefficient index set, including endpoints. -/
def Unimodal {n : ℕ} (f : Fin (n + 1) → ℕ) : Prop :=
  ∃ m : Fin (n + 1),
    (∀ i j, i ≤ j → j ≤ m → f i ≤ f j) ∧
    (∀ i j, m ≤ i → i ≤ j → f j ≤ f i)

/-- A strict valley contradicts the usual increasing-then-decreasing definition. -/
theorem not_unimodal_of_strict_valley {n : ℕ} (f : Fin (n + 1) → ℕ)
    (i j k : Fin (n + 1)) (hij : i < j) (hjk : j < k)
    (hleft : f j < f i) (hright : f j < f k) : ¬ Unimodal f := by
  rintro ⟨m, hinc, hdec⟩
  rcases le_total j m with hjm | hmj
  · have := hinc i j (le_of_lt hij) hjm
    omega
  · have := hdec j k hmj (le_of_lt hjk)
    omega

/-- A finite subset with enough coefficient mass contains a value above `f j`. -/
theorem exists_larger_of_mass {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℕ)
    (hmass : a ≤ ∑ i ∈ S, f i) (hsmall : f j < c)
    (hgap : c * (n + 1) < a) : ∃ i ∈ S, f j < f i := by
  by_contra h
  push Not at h
  have hbound : (∑ i ∈ S, f i) ≤ S.card * c := by
    calc
      (∑ i ∈ S, f i) ≤ ∑ _i ∈ S, c := by
        apply Finset.sum_le_sum
        intro i hi
        exact le_trans (h i hi) (Nat.le_of_lt hsmall)
      _ = S.card * c := by simp
  have hcard : S.card ≤ n + 1 := by
    simpa using (Finset.card_le_univ S)
  have htotal : S.card * c ≤ c * (n + 1) := by
    calc
      S.card * c ≤ (n + 1) * c := Nat.mul_le_mul_right c hcard
      _ = c * (n + 1) := Nat.mul_comm _ _
  omega

/-- Sufficient coefficient mass on each side of `j` implies a strict valley. -/
theorem strict_valley_of_interval_mass {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S T : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℕ)
    (hS : ∀ i ∈ S, i < j) (hT : ∀ k ∈ T, j < k)
    (hmassS : a ≤ ∑ i ∈ S, f i) (hmassT : a ≤ ∑ k ∈ T, f k)
    (hsmall : f j < c) (hgap : c * (n + 1) < a) :
    ∃ i k, i < j ∧ j < k ∧ f j < f i ∧ f j < f k := by
  obtain ⟨i, hi, hfi⟩ := exists_larger_of_mass f S j a c hmassS hsmall hgap
  obtain ⟨k, hk, hfk⟩ := exists_larger_of_mass f T j a c hmassT hsmall hgap
  exact ⟨i, k, hS i hi, hT k hk, hfi, hfk⟩

/-- Integer interval-mass certificate for failure of finite-prefix unimodality. -/
theorem not_unimodal_of_interval_mass {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S T : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℕ)
    (hS : ∀ i ∈ S, i < j) (hT : ∀ k ∈ T, j < k)
    (hmassS : a ≤ ∑ i ∈ S, f i) (hmassT : a ≤ ∑ k ∈ T, f k)
    (hsmall : f j < c) (hgap : c * (n + 1) < a) : ¬ Unimodal f := by
  obtain ⟨i, k, hij, hjk, hleft, hright⟩ :=
    strict_valley_of_interval_mass f S T j a c hS hT hmassS hmassT hsmall hgap
  exact not_unimodal_of_strict_valley f i j k hij hjk hleft hright

/-- Real mass thresholds avoid rounding the total number of dominating sets. -/
theorem exists_larger_of_real_mass {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℝ)
    (hc : 0 ≤ c) (hmass : a < ∑ i ∈ S, (f i : ℝ))
    (hsmall : (f j : ℝ) < c) (hgap : c * (n + 1) ≤ a) :
    ∃ i ∈ S, f j < f i := by
  by_contra h
  push Not at h
  have hbound : (∑ i ∈ S, (f i : ℝ)) ≤ (S.card : ℝ) * c := by
    calc
      (∑ i ∈ S, (f i : ℝ)) ≤ ∑ _i ∈ S, c := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (f i : ℝ) ≤ f j := by exact_mod_cast h i hi
        exact le_trans hi' hsmall.le
      _ = (S.card : ℝ) * c := by simp
  have hcard : (S.card : ℝ) ≤ n + 1 := by
    exact_mod_cast (show S.card ≤ n + 1 by simpa using Finset.card_le_univ S)
  have htotal : (S.card : ℝ) * c ≤ c * (n + 1) := by
    nlinarith
  linarith

/-- The stated real thresholds imply failure of unimodality.
The graph-specific coefficient mass estimates remain explicit hypotheses. -/
theorem not_unimodal_of_real_interval_mass {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S T : Finset (Fin (n + 1))) (j : Fin (n + 1)) (Z : ℝ)
    (hZ : 0 < Z) (hn : n + 1 ≤ 2 ^ 104)
    (hS : ∀ i ∈ S, i < j) (hT : ∀ k ∈ T, j < k)
    (hmassS : Z / 3 < ∑ i ∈ S, (f i : ℝ))
    (hmassT : Z / 3 < ∑ k ∈ T, (f k : ℝ))
    (hsmall : (f j : ℝ) < Z / (2 : ℝ) ^ 189) : ¬ Unimodal f := by
  have hc : 0 ≤ Z / (2 : ℝ) ^ 189 := by positivity
  have hn' : (n : ℝ) + 1 ≤ (2 : ℝ) ^ 104 := by exact_mod_cast hn
  have hgap : (Z / (2 : ℝ) ^ 189) * (n + 1) ≤ Z / 3 := by
    calc
      (Z / (2 : ℝ) ^ 189) * (n + 1) ≤ (Z / (2 : ℝ) ^ 189) * 2 ^ 104 :=
        mul_le_mul_of_nonneg_left hn' hc
      _ ≤ Z / 3 := by norm_num; linarith
  obtain ⟨i, hi, hfi⟩ :=
    exists_larger_of_real_mass f S j _ _ hc hmassS hsmall hgap
  obtain ⟨k, hk, hfk⟩ :=
    exists_larger_of_real_mass f T j _ _ hc hmassT hsmall hgap
  exact not_unimodal_of_strict_valley f i j k (hS i hi) (hT k hk) hfi hfk

/-- The pigeonhole threshold depends on the number of indices in the selected
interval rather than the length of the full sequence. -/
theorem exists_larger_of_real_mass_card {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℝ)
    (hmass : a ≤ ∑ i ∈ S, (f i : ℝ)) (hsmall : (f j : ℝ) ≤ c)
    (hgap : (S.card : ℝ) * c < a) : ∃ i ∈ S, f j < f i := by
  by_contra h
  push Not at h
  have hb : (∑ i ∈ S, (f i : ℝ)) ≤ (S.card : ℝ) * c := by
    calc
      (∑ i ∈ S, (f i : ℝ)) ≤ ∑ _i ∈ S, c := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (f i : ℝ) ≤ f j := by exact_mod_cast h i hi
        exact le_trans hi' hsmall
      _ = (S.card : ℝ) * c := by simp
  linarith

/-- Interval certificate with thresholds determined by interval cardinalities. -/
theorem not_unimodal_of_interval_mass_card {n : ℕ} (f : Fin (n + 1) → ℕ)
    (S T : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℝ)
    (hS : ∀ i ∈ S, i < j) (hT : ∀ k ∈ T, j < k)
    (hmassS : a ≤ ∑ i ∈ S, (f i : ℝ))
    (hmassT : a ≤ ∑ k ∈ T, (f k : ℝ))
    (hsmall : (f j : ℝ) ≤ c)
    (hgapS : (S.card : ℝ) * c < a) (hgapT : (T.card : ℝ) * c < a) :
    ¬ Unimodal f := by
  obtain ⟨i, hi, hfi⟩ := exists_larger_of_real_mass_card f S j a c hmassS hsmall hgapS
  obtain ⟨k, hk, hfk⟩ := exists_larger_of_real_mass_card f T j a c hmassT hsmall hgapT
  exact not_unimodal_of_strict_valley f i j k (hS i hi) (hT k hk) hfi hfk

end Research.DominationValley

#print axioms Research.DominationValley.not_unimodal_of_interval_mass
#print axioms Research.DominationValley.not_unimodal_of_real_interval_mass
#print axioms Research.DominationValley.not_unimodal_of_interval_mass_card
