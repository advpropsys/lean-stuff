import Research.DominationHardBandTransfer
import Research.DominationCoefficientBridge
import Research.DominationGadgetProperties

/-! A connected finite simple graph with a nonunimodal domination polynomial.
The coefficient function counts all ordinary dominating subsets. The imported
proofs establish the phase, counting, geometry and numerical bounds. -/
namespace Research.DominationCounterexample

open DominationCanonicalPartition DominationIntervalMass DominationSizeIntervals
open DominationHardBandTransfer DominationParameters

theorem canonical_not_unimodal :
    ¬ DominationValley.Unimodal DominationCanonicalPartition.coefficient := by
  apply DominationCoefficientBridge.not_unimodal_of_outside_fraction
  · simpa only [Prob, Fintype.card_eq_nat_card] using
      left_interval_gt_third left_band_fraction
  · simpa only [Prob, Fintype.card_eq_nat_card] using
      right_interval_gt_third right_band_fraction
  · have h := (outside_intervals_bound bad_band_fraction).trans_lt
      (combined_error_bound _ _ _ le_rfl le_rfl le_rfl)
    simpa only [Prob, not_or, Fintype.card_eq_nat_card] using h

theorem canonical_connected_counterexample :
    DominationGadgetGraph.finalGraph.Connected ∧
      Fintype.card DominationGadgetGraph.Vertex = 15211807199220036387538871517957 ∧
      ¬ DominationValley.Unimodal DominationCanonicalPartition.coefficient := by
  exact ⟨DominationGadgetGraph.final_connected,
    DominationGadgetGraph.final_vertex_card.trans n_value, canonical_not_unimodal⟩

#print axioms canonical_not_unimodal
#print axioms canonical_connected_counterexample

end Research.DominationCounterexample
