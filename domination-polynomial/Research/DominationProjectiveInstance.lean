import Research.DominationParameters
import Research.DominationProjectiveGeometry

/-! The canonical projective incidence structure and its expansion bound.
Nonunimodality is proved in `Research.DominationCounterexample`. -/
namespace Research.DominationProjectiveInstance

open DominationParameters DominationProjectiveGeometry

instance canonicalPrime : Fact (Nat.Prime q) := ⟨q_prime⟩

abbrev Scalar := ZMod q
abbrev Point := DominationProjectiveGeometry.Point Scalar

 theorem scalar_card : Fintype.card Scalar = q := by
  exact ZMod.card q

theorem point_card : Fintype.card Point = b := by
  rw [DominationProjectiveGeometry.point_count, scalar_card]
  rfl

theorem point_card_explicit : Fintype.card Point = 4611686016279904257 :=
  point_card.trans b_value

/-- Every two sets of size at least b/10000 have an incidence. -/
theorem canonical_disperser (S T : Finset Point)
    (hS : (b : ℝ) / 10000 ≤ S.card)
    (hT : (b : ℝ) / 10000 ≤ T.card) :
    ∃ p ∈ S, ∃ r ∈ T, Inc p r := by
  apply incidence_between_large_sets S T (1 / 10000 : ℝ) (by positivity)
  · rw [scalar_card]
    norm_num [q]
  · rw [point_card]
    simpa [div_eq_mul_inv, mul_comm] using hS
  · rw [point_card]
    simpa [div_eq_mul_inv, mul_comm] using hT

/-- An equivalent integer form avoids real-valued cardinality assumptions. -/
theorem canonical_disperser_integer (S T : Finset Point)
    (hS : b ≤ 10000 * S.card)
    (hT : b ≤ 10000 * T.card) :
    ∃ p ∈ S, ∃ r ∈ T, Inc p r := by
  apply canonical_disperser S T
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10000)).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hS)
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 10000)).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hT)

#print axioms canonical_disperser
#print axioms canonical_disperser_integer
end Research.DominationProjectiveInstance
