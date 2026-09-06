import Research.DominationCanonicalPartition
import Research.DominationSizeIntervals
import Research.DominationCoefficientCounts

/-! Nonunimodality of the canonical graph follows from the finite interval
fraction bounds stated as hypotheses below. -/
namespace Research.DominationCoefficientBridge

open Research.DominationCanonicalPartition Research.DominationParameters
open Research.DominationSizeIntervals

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem coefficient_eq_generic (k : Fin (n + 1)) :
    DominationCanonicalPartition.coefficient k =
      DominationCoefficientCounts.coefficient sizeIndex k := by
  unfold DominationCanonicalPartition.coefficient DominationCoefficientCounts.coefficient
  rw [Fintype.card_eq_nat_card]
  apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro S
  constructor
  · intro h
    exact Fin.ext h
  · intro h
    exact congrArg Fin.val h

def leftIndices : Finset (Fin (n + 1)) := Finset.univ.filter LeftIndex
def rightIndices : Finset (Fin (n + 1)) := Finset.univ.filter RightIndex

theorem left_event_card : Nat.card {S : DomSet // sizeIndex S ∈ leftIndices} =
    Nat.card {S : DomSet // LeftInterval (size S)} := by
  apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro S
  simp [leftIndices, LeftIndex, sizeIndex]

theorem right_event_card : Nat.card {S : DomSet // sizeIndex S ∈ rightIndices} =
    Nat.card {S : DomSet // RightInterval (size S)} := by
  apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro S
  simp [rightIndices, RightIndex, sizeIndex]

theorem center_event_card : Nat.card {S : DomSet // sizeIndex S = valleyIndex} =
    Nat.card {S : DomSet // size S = j} := by
  apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro S
  exact Fin.ext_iff

theorem interval_card_gap (I : Finset (Fin (n + 1))) :
    (I.card : ℝ) * (1 / (2 : ℝ) ^ 189) < 1 / 3 := by
  have hi : I.card ≤ n + 1 := by simpa using Finset.card_le_univ I
  have hcard : (I.card : ℝ) ≤ (2 : ℝ) ^ 104 := by
    exact_mod_cast hi.trans order_bound
  calc
    _ ≤ (2 : ℝ) ^ 104 * (1 / (2 : ℝ) ^ 189) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ < 1 / 3 := by norm_num

/-- Bounds on the interval fractions and center fraction imply nonunimodality
of the canonical graph's domination coefficients. -/
theorem not_unimodal_of_center_fraction
    (hleft : (1 / 3 : ℝ) < (Nat.card {S : DomSet // LeftInterval (size S)} : ℝ) / D)
    (hright : (1 / 3 : ℝ) < (Nat.card {S : DomSet // RightInterval (size S)} : ℝ) / D)
    (hcenter : (Nat.card {S : DomSet // size S = j} : ℝ) / D < 1 / (2 : ℝ) ^ 189) :
    ¬ DominationValley.Unimodal DominationCanonicalPartition.coefficient := by
  letI : Nonempty DomSet := Fintype.card_pos_iff.mp D_pos
  have hD : Nat.card DomSet = D := Nat.card_eq_fintype_card
  have heq : DominationCanonicalPartition.coefficient =
      DominationCoefficientCounts.coefficient sizeIndex := funext coefficient_eq_generic
  rw [heq]
  apply DominationCoefficientCounts.not_unimodal_of_event_counts sizeIndex
    leftIndices rightIndices valleyIndex (1 / 3) (1 / (2 : ℝ) ^ 189)
  · intro i hi
    exact leftIndex_before_valley (Finset.mem_filter.mp hi).2
  · intro k hk
    exact rightIndex_after_valley (Finset.mem_filter.mp hk).2
  · rw [left_event_card, hD]
    exact hleft.le
  · rw [right_event_card, hD]
    exact hright.le
  · rw [center_event_card, hD]
    exact hcenter.le
  · exact interval_card_gap leftIndices
  · exact interval_card_gap rightIndices

/-- The size j is outside both coefficient intervals. -/
theorem center_card_le_outside : Nat.card {S : DomSet // size S = j} ≤
    Nat.card {S : DomSet // ¬ LeftInterval (size S) ∧ ¬ RightInterval (size S)} := by
  have h := Fintype.card_le_of_injective
    (fun S : {S : DomSet // size S = j} =>
      (⟨S.val, by rw [S.property]; exact ⟨valley_not_left, valley_not_right⟩⟩ :
        {S : DomSet // ¬ LeftInterval (size S) ∧ ¬ RightInterval (size S)}))
    (by
      intro S T heq
      apply Subtype.ext
      exact congrArg (fun S : {S : DomSet //
        ¬ LeftInterval (size S) ∧ ¬ RightInterval (size S)} => S.val) heq)
  simpa only [Fintype.card_eq_nat_card] using h

/-- Bounds on the fractions inside and outside the two size intervals imply
nonunimodality of the domination coefficients. -/
theorem not_unimodal_of_outside_fraction
    (hleft : (1 / 3 : ℝ) < (Nat.card {S : DomSet // LeftInterval (size S)} : ℝ) / D)
    (hright : (1 / 3 : ℝ) < (Nat.card {S : DomSet // RightInterval (size S)} : ℝ) / D)
    (houtside : (Nat.card {S : DomSet //
      ¬ LeftInterval (size S) ∧ ¬ RightInterval (size S)} : ℝ) / D <
        1 / (2 : ℝ) ^ 189) :
    ¬ DominationValley.Unimodal DominationCanonicalPartition.coefficient := by
  apply not_unimodal_of_center_fraction hleft hright
  have hc : (Nat.card {S : DomSet // size S = j} : ℝ) ≤
      Nat.card {S : DomSet // ¬ LeftInterval (size S) ∧ ¬ RightInterval (size S)} := by
    exact_mod_cast center_card_le_outside
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hc D_real_pos.le) houtside

end
end Research.DominationCoefficientBridge

#print axioms Research.DominationCoefficientBridge.coefficient_eq_generic
#print axioms Research.DominationCoefficientBridge.not_unimodal_of_outside_fraction
