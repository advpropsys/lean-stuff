import Research.DominationHardBandTransfer
import Research.DominationCoefficientCounts

/-! A verified reuse demonstration: the auxiliary ordinary control graph also
has a nonunimodal independence polynomial. Nonunimodality of independence
polynomials for general graphs is already known; this is not a new conjecture
resolution. -/
namespace Research.DominationIndependenceCorollary
open DominationParameters DominationGadgetGraph DominationCanonicalPartition
open DominationIntervalMass DominationHardBandTransfer
noncomputable section
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxSize 1024
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

/-- All ordinary independent subsets of the actual auxiliary graph. -/
abbrev IndependentSet := {P : Set Control //
  ∀ u ∈ P, ∀ v ∈ P, ¬ controlGraph.Adj u v}

def independentHardEquiv : IndependentSet ≃ HardControlSet :=
  Equiv.subtypeEquivRight (fun P => independent_iff P)

theorem independent_card : Nat.card IndependentSet = H := by
  rw [Nat.card_congr independentHardEquiv]
  exact Nat.card_eq_fintype_card

def sizeIndex (P : IndependentSet) : Fin (t+1) := ⟨Nat.card P.val, by
  have h := DominationSizeIntervals.control_subset_size_le P.val
  omega⟩

/-- Ordinary independence coefficients of controlGraph, including the empty set. -/
def coefficient (k : Fin (t+1)) : ℕ :=
  Nat.card {P : IndependentSet // Nat.card P.val = k.val}

theorem coefficient_eq_generic (k : Fin (t+1)) :
    coefficient k = DominationCoefficientCounts.coefficient sizeIndex k := by
  apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
  intro P
  constructor
  · intro h; exact Fin.ext h
  · intro h; exact congrArg Fin.val h

def lowIndices : Finset (Fin (t+1)) := Finset.univ.filter (fun i =>
  71*(b:ℝ)/100 ≤ i.val ∧ (i.val:ℝ) ≤ 80*(b:ℝ)/100)
def highIndices : Finset (Fin (t+1)) := Finset.univ.filter (fun i =>
  92*(b:ℝ)/100 ≤ i.val ∧ (i.val:ℝ) ≤ 108*(b:ℝ)/100)
def middle : Fin (t+1) := ⟨43*b/50, by norm_num [t,b,q]⟩

theorem low_before_middle (i : Fin (t+1)) (hi : i ∈ lowIndices) : i < middle := by
  have hi' := (Finset.mem_filter.mp hi).2.2
  have hs : 80*(b:ℝ)/100 < (middle.val:ℝ) := by norm_num [middle,b,q]
  have h : (i.val:ℝ) < middle.val := lt_of_le_of_lt hi' hs
  exact_mod_cast h

theorem high_after_middle (i : Fin (t+1)) (hi : i ∈ highIndices) : middle < i := by
  have hi' := (Finset.mem_filter.mp hi).2.1
  have hs : (middle.val:ℝ) < 92*(b:ℝ)/100 := by norm_num [middle,b,q]
  have h : (middle.val:ℝ) < i.val := lt_of_lt_of_le hs hi'
  exact_mod_cast h

theorem low_event_count : Nat.card {P : IndependentSet // sizeIndex P ∈ lowIndices} =
    Nat.card {P : HardControlSet // RightBand P.val} := by
  apply Nat.card_congr (independentHardEquiv.subtypeEquiv ?_)
  intro P
  simp only [lowIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    sizeIndex, RightBand, independentHardEquiv, Equiv.subtypeEquivRight_apply]

theorem high_event_count : Nat.card {P : IndependentSet // sizeIndex P ∈ highIndices} =
    Nat.card {P : HardControlSet // LeftBand P.val} := by
  apply Nat.card_congr (independentHardEquiv.subtypeEquiv ?_)
  intro P
  simp only [highIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    sizeIndex, LeftBand, independentHardEquiv, Equiv.subtypeEquivRight_apply]

theorem center_outside_bands (P : IndependentSet) (hP : sizeIndex P = middle) :
    ¬ (LeftBand P.val ∨ RightBand P.val) := by
  have hp : Nat.card P.val = 43*b/50 := congrArg Fin.val hP
  unfold LeftBand RightBand
  rw [hp]
  norm_num [b,q]

theorem center_count_bound : Nat.card {P : IndependentSet // sizeIndex P = middle} ≤
    Nat.card {P : HardControlSet // ¬ (LeftBand P.val ∨ RightBand P.val)} := by
  let f : {P : IndependentSet // sizeIndex P = middle} →
      {P : HardControlSet // ¬ (LeftBand P.val ∨ RightBand P.val)} :=
    fun P => ⟨independentHardEquiv P.val, center_outside_bands P.val P.property⟩
  apply Nat.card_le_card_of_injective f
  intro P Q h
  apply Subtype.ext
  apply independentHardEquiv.injective
  exact congrArg Subtype.val h

theorem interval_gap (I : Finset (Fin (t+1))) :
    (I.card:ℝ)*(1/(2:ℝ)^300) < 1/3 := by
  have hi : I.card ≤ 2^65 := by
    have h : I.card ≤ t+1 := by simpa only [Fintype.card_fin] using Finset.card_le_univ I
    exact h.trans (by have := controls_bound; omega)
  have hi' : (I.card:ℝ) ≤ (2:ℝ)^65 := by exact_mod_cast hi
  calc
    _ ≤ (2:ℝ)^65*(1/(2:ℝ)^300) := mul_le_mul_of_nonneg_right hi' (by positivity)
    _ < _ := by norm_num

/-- A closed reuse corollary about the ordinary independence polynomial. -/
theorem control_independence_not_unimodal : ¬ DominationValley.Unimodal coefficient := by
  letI : Nonempty IndependentSet := ⟨⟨∅, by simp⟩⟩
  have he : coefficient = DominationCoefficientCounts.coefficient sizeIndex :=
    funext coefficient_eq_generic
  rw [he]
  apply DominationCoefficientCounts.not_unimodal_of_event_counts sizeIndex
    lowIndices highIndices middle (1/3) (1/(2:ℝ)^300)
  · exact low_before_middle
  · exact high_after_middle
  · rw [low_event_count, independent_card]
    have h := right_band_fraction
    simp only [HardProb, Fintype.card_eq_nat_card] at h
    exact le_trans (by norm_num) h
  · rw [high_event_count, independent_card]
    have h := left_band_fraction
    simp only [HardProb, Fintype.card_eq_nat_card] at h
    exact le_trans (by norm_num) h
  · rw [independent_card]
    have h := bad_band_fraction
    simp only [HardProb, Fintype.card_eq_nat_card] at h
    have hc : (Nat.card {P : IndependentSet // sizeIndex P = middle}:ℝ) ≤
        Nat.card {P : HardControlSet // ¬ (LeftBand P.val ∨ RightBand P.val)} :=
      Nat.cast_le.mpr center_count_bound
    exact le_trans (div_le_div_of_nonneg_right hc H_real_pos.le) h
  · exact interval_gap lowIndices
  · exact interval_gap highIndices

#print axioms control_independence_not_unimodal
end
end Research.DominationIndependenceCorollary
