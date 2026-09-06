import Research.DominationGadgetStates
import Research.DominationHardPhaseBounds
import Research.DominationIntervalMass

/-! Hard-control size-band bounds from the four-state bijection and
the canonical phase estimates. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option synthInstance.maxSize 1024

namespace Research.DominationHardBandTransfer

open DominationGadgetGraph DominationGadgetStates DominationHardPhases
open DominationCanonicalPartition DominationIntervalMass

theorem hard_count_eq : H = DominationHardPhaseBounds.hardCount := by
  change Fintype.card {P : Set Control // EdgeFree P} =
    Nat.card {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p}
  rw [Nat.card_eq_fintype_card]
  exact hard_card_eq.symm

theorem encoded_size_real (p : Config Cell) :
    (Nat.card (encoded p) : ℝ) =
      DominationHardPhaseBounds.leftTotal p + DominationHardPhaseBounds.rightTotal p := by
  rw [encoded_card]
  simp only [Nat.cast_add, Nat.cast_sum]
  rfl

theorem encoded_goodA (p : Config Cell) (hp : DominationHardPhaseBounds.GoodA p) :
    LeftBand (encoded p) := by
  have h := DominationHardPhaseBounds.goodA_omitted_bounds p hp
  change _ ≤ (Nat.card (encoded p) : ℝ) ∧ (Nat.card (encoded p) : ℝ) ≤ _
  rwa [encoded_size_real]

theorem encoded_goodC (p : Config Cell) (hp : DominationHardPhaseBounds.GoodC p) :
    RightBand (encoded p) := by
  have h := DominationHardPhaseBounds.goodC_omitted_bounds p hp
  change _ ≤ (Nat.card (encoded p) : ℝ) ∧ (Nat.card (encoded p) : ℝ) ≤ _
  rwa [encoded_size_real]

theorem good_count_le_band (A : Config Cell → Prop) (B : Set Control → Prop)
    (hA : ∀ p, A p → Compatible DominationProjectiveGeometry.Inc p)
    (hB : ∀ p, A p → B (encoded p)) :
    Nat.card {p // A p} ≤ Fintype.card {P : HardControlSet // B P.val} := by
  let f : {p // A p} → {P : HardControlSet // B P.val} := fun p =>
    ⟨⟨encoded p.val, (encoded_free_iff p.val).mpr (hA p.val p.property)⟩,
      hB p.val p.property⟩
  have hf : Function.Injective f := by
    intro p r h
    apply Subtype.ext
    exact encoded_injective (congrArg (fun x => x.val.val) h)
  simpa only [Nat.card_eq_fintype_card] using Nat.card_le_card_of_injective f hf

theorem left_band_fraction : 1 / 2 - 1 / (2 : ℝ) ^ 300 ≤ HardProb LeftBand := by
  have h := good_count_le_band DominationHardPhaseBounds.GoodA LeftBand
    (fun p hp => hp.1.1) encoded_goodA
  have hr : (DominationHardPhaseBounds.goodACount : ℝ) ≤
      Fintype.card {P : HardControlSet // LeftBand P.val} := by exact_mod_cast h
  have hd := div_le_div_of_nonneg_right hr H_real_pos.le
  rw [hard_count_eq] at hd
  exact DominationHardPhaseBounds.goodA_fraction_lower.trans (by
    simpa only [HardProb, hard_count_eq] using hd)

theorem right_band_fraction : 1 / 2 - 1 / (2 : ℝ) ^ 300 ≤ HardProb RightBand := by
  have h := good_count_le_band DominationHardPhaseBounds.GoodC RightBand
    (fun p hp => hp.1.1) encoded_goodC
  have hr : (DominationHardPhaseBounds.goodCCount : ℝ) ≤
      Fintype.card {P : HardControlSet // RightBand P.val} := by exact_mod_cast h
  have hd := div_le_div_of_nonneg_right hr H_real_pos.le
  rw [hard_count_eq] at hd
  exact DominationHardPhaseBounds.goodC_fraction_lower.trans (by
    simpa only [HardProb, hard_count_eq] using hd)

theorem bad_band_count_le :
    Fintype.card {P : HardControlSet // ¬ (LeftBand P.val ∨ RightBand P.val)} ≤
      DominationHardPhaseBounds.badCount := by
  rw [← Nat.card_eq_fintype_card]
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (DominationPartition.Hard left right)
    (fun P => ¬ (LeftBand P ∨ RightBand P)))]
  change Nat.card {P : Set Control // EdgeFree P ∧ ¬ (LeftBand P ∨ RightBand P)} ≤ _
  rw [DominationGadgetStates.hard_event_count]
  let f : {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p ∧
      ¬ (LeftBand (encoded p) ∨ RightBand (encoded p))} →
      {p : Config Cell // DominationHardPhaseBounds.Bad p} := fun p =>
    ⟨p.val,p.property.1,
      (fun h => p.property.2 (Or.inl (encoded_goodA p.val h))),
      (fun h => p.property.2 (Or.inr (encoded_goodC p.val h)))⟩
  exact Nat.card_le_card_of_injective f (by
    intro p r h
    apply Subtype.ext
    exact congrArg (fun z : {p : Config Cell // DominationHardPhaseBounds.Bad p} => z.val) h)

theorem bad_band_fraction :
    HardProb (fun P => ¬ (LeftBand P ∨ RightBand P)) ≤ 1 / (2 : ℝ) ^ 300 := by
  have hr : (Fintype.card {P : HardControlSet // ¬ (LeftBand P.val ∨ RightBand P.val)} : ℝ) ≤
      DominationHardPhaseBounds.badCount := Nat.cast_le.mpr bad_band_count_le
  simp only [Fintype.card_eq_nat_card] at hr
  have hd := div_le_div_of_nonneg_right hr H_real_pos.le
  simp only [HardProb, Fintype.card_eq_nat_card]
  apply hd.trans
  rw [hard_count_eq]
  exact DominationHardPhaseBounds.bad_fraction_small.le

#print axioms left_band_fraction
#print axioms right_band_fraction
#print axioms bad_band_fraction

end Research.DominationHardBandTransfer
