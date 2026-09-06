import Research.DominationProjectiveInstance
import Research.DominationHardPhases
import Research.DominationBitEncoding
import Research.DominationParameters
import Research.DominationPhaseBalance

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Research.DominationHardPhaseBounds
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024
open DominationParameters DominationProjectiveInstance DominationProjectiveGeometry
open DominationHardPhases

def cutoff : ℕ := (b + 9999) / 10000

theorem cutoff_large (s : ℕ) (hs : cutoff ≤ s) : b ≤ 10000 * s := by
  norm_num [cutoff, b_value] at hs ⊢
  omega

theorem cutoff_small (s : ℕ) (hs : s < cutoff) : (s : ℝ) ≤ (b : ℝ) / 10000 := by
  have hh : 10000 * s ≤ b := by
    norm_num [cutoff, b_value] at hs ⊢
    omega
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mpr
  exact_mod_cast (by simpa [Nat.mul_comm] using hh)

theorem canonical_rectangle : NoLargeRectangle (Inc (F := Scalar)) cutoff := by
  intro S T hS hT
  exact canonical_disperser_integer S T (cutoff_large _ hS) (cutoff_large _ hT)

def leftTotal (p : Config Point) : ℝ := ∑ i, (leftSize (p.1 i) : ℝ)
def rightTotal (p : Config Point) : ℝ := ∑ i, (rightSize (p.2 i) : ℝ)

def Hard (p : Config Point) : Prop := Compatible (Inc (F := Scalar)) p
def PhaseA (p : Config Point) : Prop := Hard p ∧ cutoff ≤ (occupied p.1).card
def PhaseC (p : Config Point) : Prop := Hard p ∧ cutoff ≤ (occupied p.2).card
def GoodA (p : Config Point) : Prop := PhaseA p ∧
  (94 : ℝ) * b / 100 ≤ leftTotal p ∧ leftTotal p ≤ (106 : ℝ) * b / 100
def GoodC (p : Config Point) : Prop := PhaseC p ∧
  (71 : ℝ) * b / 100 ≤ rightTotal p ∧ rightTotal p ≤ (79 : ℝ) * b / 100

theorem phase_disjoint (p : Config Point) : ¬ (PhaseA p ∧ PhaseC p) := by
  rintro ⟨hA, hC⟩
  exact not_both_large canonical_rectangle p hA.1 ⟨hA.2, hC.2⟩

theorem phase_count_eq : Fintype.card {p // PhaseA p} = Fintype.card {p // PhaseC p} := by
  have h := phase_card_eq (C := Point) (B := Inc (F := Scalar))
    (fun i j h ↦ (inc_symm i j).mp h) cutoff
  simp only [← Nat.card_eq_fintype_card] at h ⊢
  exact h

theorem hard_count_lower : 4 ^ b ≤ Fintype.card {p // Hard p} := by
  have h := hard_card_lower (C := Point) (Inc (F := Scalar))
  rw [point_card] at h
  simp only [← Nat.card_eq_fintype_card] at h ⊢
  exact h

theorem word_stat_card_reindex {C : Type*} [Fintype C]
    (g : Fin 4 → ℝ) (P : ℝ → Prop) :
    Fintype.card {w : Word C // P (∑ i, g (w i))} =
      Fintype.card {w : Word (Fin (Fintype.card C)) // P (∑ i, g (w i))} := by
  let e := Equiv.arrowCongr (Fintype.equivFin C) (Equiv.refl (Fin 4))
  have hs (w : Word C) : (∑ i, g (e w i)) = ∑ i, g (w i) := by
    exact (Fintype.equivFin C).symm.sum_comp (fun i ↦ g (w i))
  exact Fintype.card_congr (e.subtypeEquiv (by intro w; rw [hs]))

theorem left_word_tail_index {C : Type*} [Fintype C] (hr : 0 < Fintype.card C)
    (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {w : Word C // u ≤ |(∑ i, (leftSize (w i) : ℝ)) - Fintype.card C|} : ℝ) /
      4 ^ Fintype.card C ≤ 2 * Real.exp (-u ^ 2 / Fintype.card C) := by
  rw [word_stat_card_reindex (fun s ↦ (leftSize s : ℝ))
    (fun x ↦ u ≤ |x - Fintype.card C|)]
  exact DominationBitEncoding.left_word_tail (Fintype.card C) hr u hu

theorem right_word_tail_index {C : Type*} [Fintype C] (hr : 0 < Fintype.card C)
    (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {w : Word C //
      u ≤ |(∑ i, (rightSize (w i) : ℝ)) - (3 : ℝ) * Fintype.card C / 4|} : ℝ) /
      4 ^ Fintype.card C ≤ 2 * Real.exp (-2 * u ^ 2 / Fintype.card C) := by
  rw [word_stat_card_reindex (fun s ↦ (rightSize s : ℝ))
    (fun x ↦ u ≤ |x - (3 : ℝ) * Fintype.card C / 4|)]
  simpa only [rightSize, Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using
    DominationFiniteTails.four_state_tail (Fintype.card C) hr u hu

theorem right_sum_occupied {C : Type*} [Fintype C] (v : Word C) :
    (∑ i, (rightSize (v i) : ℝ)) = (occupied v).card := by
  rw [← Nat.cast_sum]
  congr 1
  simp only [rightSize_eq_indicator, sum_boole, occupied]
  norm_cast

theorem left_sum_le_occupied {C : Type*} [Fintype C] (v : Word C) :
    (∑ i, (leftSize (v i) : ℝ)) ≤ 2 * (occupied v).card := by
  rw [← right_sum_occupied, mul_sum]
  apply sum_le_sum
  intro i _
  unfold leftSize rightSize
  split_ifs <;> norm_num

theorem goodA_omitted_bounds (p : Config Point) (hp : GoodA p) :
    (92 : ℝ) * b / 100 ≤ leftTotal p + rightTotal p ∧
      leftTotal p + rightTotal p ≤ (108 : ℝ) * b / 100 := by
  have hminor : (occupied p.2).card < cutoff := by
    have h := not_both_large canonical_rectangle p hp.1.1
    have ha := hp.1.2
    omega
  have ht : rightTotal p ≤ (b : ℝ) / 10000 := by
    unfold rightTotal
    rw [right_sum_occupied]
    exact cutoff_small _ hminor
  have hn : 0 ≤ rightTotal p := sum_nonneg (fun i _ ↦ Nat.cast_nonneg _)
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  constructor <;> linarith [hp.2.1, hp.2.2]

theorem goodC_omitted_bounds (p : Config Point) (hp : GoodC p) :
    (71 : ℝ) * b / 100 ≤ leftTotal p + rightTotal p ∧
      leftTotal p + rightTotal p ≤ (80 : ℝ) * b / 100 := by
  have hminor : (occupied p.1).card < cutoff := by
    have h := not_both_large canonical_rectangle p hp.1.1
    have hc := hp.1.2
    omega
  have ht : leftTotal p ≤ 2 * ((b : ℝ) / 10000) :=
    (left_sum_le_occupied p.1).trans
      (mul_le_mul_of_nonneg_left (cutoff_small _ hminor) (by norm_num))
  have hn : 0 ≤ leftTotal p := sum_nonneg (fun i _ ↦ Nat.cast_nonneg _)
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  constructor <;> linarith [hp.2.1, hp.2.2]

def minorityCount : ℕ := Nat.card {v : Word Point // (occupied v).card < cutoff}

theorem minority_count_bound : (minorityCount : ℝ) ≤ Real.exp ((3 : ℝ) * b / 2500) := by
  have hn := small_words_binomial_bound (C := Point) cutoff
  rw [point_card] at hn
  simp only [← Nat.card_eq_fintype_card] at hn
  have hr : (minorityCount : ℝ) ≤
      ∑ i ∈ (range (b + 1)).filter (fun i ↦ i < cutoff),
        (b.choose i : ℝ) * (3 : ℝ) ^ i := by exact_mod_cast hn
  calc
    _ ≤ _ := hr
    _ ≤ ∑ i ∈ (range (b + 1)).filter (fun i : ℕ ↦ (i : ℝ) ≤ (b : ℝ) / 10000),
        (b.choose i : ℝ) * (3 : ℝ) ^ i := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact mem_filter.mpr ⟨(mem_filter.mp hi).1, cutoff_small i (mem_filter.mp hi).2⟩
      · intro i _ _
        exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
    _ ≤ _ := DominationConcentration.minority_states_bound b

def LeftTail (v : Word Point) : Prop :=
  (3 : ℝ) * b / 50 ≤ |(∑ i, (leftSize (v i) : ℝ)) - b|
def RightTail (v : Word Point) : Prop :=
  (1 : ℝ) * b / 25 ≤ |(∑ i, (rightSize (v i) : ℝ)) - (3 : ℝ) * b / 4|
def leftTailCount : ℕ := Nat.card {v // LeftTail v}
def rightTailCount : ℕ := Nat.card {v // RightTail v}
def hardCount : ℕ := Nat.card {p // Hard p}
def leftExceptionalCount : ℕ := Nat.card {p : Config Point // PhaseA p ∧ LeftTail p.1}
def rightExceptionalCount : ℕ := Nat.card {p : Config Point // PhaseC p ∧ RightTail p.2}
def outsidePhaseCount : ℕ := Nat.card {p : Config Point // Hard p ∧
  (occupied p.1).card < cutoff ∧ (occupied p.2).card < cutoff}

theorem b_pos_real : (0 : ℝ) < b := by rw [b_value]; norm_num

theorem left_tail_count_bound : (leftTailCount : ℝ) / 4 ^ b ≤
    2 * Real.exp (-(9 : ℝ) * b / 2500) := by
  have h := left_word_tail_index (C := Point)
    (by rw [point_card, b_value]; norm_num) ((3 : ℝ) * b / 50)
    (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg b)) (by norm_num))
  rw [point_card] at h
  simp only [← Nat.card_eq_fintype_card] at h
  have he : -((3 : ℝ) * b / 50) ^ 2 / b = -(9 : ℝ) * b / 2500 := by
    field_simp [ne_of_gt b_pos_real]
    ring
  rw [he] at h
  exact h

theorem right_tail_count_bound : (rightTailCount : ℝ) / 4 ^ b ≤
    2 * Real.exp (-(2 : ℝ) * b / 625) := by
  have h := right_word_tail_index (C := Point)
    (by rw [point_card, b_value]; norm_num) ((1 : ℝ) * b / 25)
    (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg b)) (by norm_num))
  rw [point_card] at h
  simp only [← Nat.card_eq_fintype_card] at h
  have he : -2 * ((1 : ℝ) * b / 25) ^ 2 / b = -(2 : ℝ) * b / 625 := by
    field_simp [ne_of_gt b_pos_real]
    ring
  rw [he] at h
  exact h

theorem left_exceptional_product : leftExceptionalCount ≤ leftTailCount * minorityCount := by
  have h := left_bad_card_le canonical_rectangle LeftTail
  simp only [← Nat.card_eq_fintype_card] at h
  have he : Nat.card {p : Config Point // PhaseA p ∧ LeftTail p.1} =
      Nat.card {p : Config Point // Compatible (Inc (F := Scalar)) p ∧
        cutoff ≤ (occupied p.1).card ∧ LeftTail p.1} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ ↦ and_assoc)
  unfold leftExceptionalCount
  rw [he]
  exact h

theorem right_exceptional_product : rightExceptionalCount ≤ minorityCount * rightTailCount := by
  have h := right_bad_card_le canonical_rectangle RightTail
  simp only [← Nat.card_eq_fintype_card] at h
  have he : Nat.card {p : Config Point // PhaseC p ∧ RightTail p.2} =
      Nat.card {p : Config Point // Compatible (Inc (F := Scalar)) p ∧
        cutoff ≤ (occupied p.2).card ∧ RightTail p.2} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun _ ↦ and_assoc)
  unfold rightExceptionalCount
  rw [he]
  exact h

theorem outside_phase_product : outsidePhaseCount ≤ minorityCount ^ 2 := by
  have h := both_small_card_le (C := Point) (Inc (F := Scalar)) cutoff
  simp only [← Nat.card_eq_fintype_card] at h
  exact h

theorem hard_count_lower_real : (4 : ℝ) ^ b ≤ hardCount := by
  have h := hard_count_lower
  simp only [← Nat.card_eq_fintype_card] at h
  exact_mod_cast h

theorem hard_count_pos : (0 : ℝ) < hardCount :=
  lt_of_lt_of_le (pow_pos (by norm_num) _) hard_count_lower_real

theorem ratio_product_bound (N U T a H v t : ℝ)
    (ha : 0 < a) (hH : 0 < H) (haH : a ≤ H)
    (hN : N ≤ U * T) (hU : U / a ≤ v) (hT : T ≤ t)
    (hT0 : 0 ≤ T) (hv : 0 ≤ v) (ht : 0 ≤ t) : N / H ≤ v * t := by
  apply (div_le_iff₀ hH).mpr
  have hUa := (div_le_iff₀ ha).mp hU
  calc
    N ≤ U * T := hN
    _ ≤ (v * a) * t := mul_le_mul hUa hT hT0 (mul_nonneg hv ha.le)
    _ = (v * t) * a := by ring
    _ ≤ (v * t) * H := mul_le_mul_of_nonneg_left haH (mul_nonneg hv ht)

theorem left_exceptional_fraction : (leftExceptionalCount : ℝ) / hardCount ≤
    2 * Real.exp (-(3 : ℝ) * b / 1250) := by
  have hn : (leftExceptionalCount : ℝ) ≤ (leftTailCount : ℝ) * minorityCount :=
    by exact_mod_cast left_exceptional_product
  have h := ratio_product_bound _ _ _ _ _ _ _ (pow_pos (by norm_num) b)
    hard_count_pos hard_count_lower_real hn left_tail_count_bound minority_count_bound
    (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Real.exp_pos _).le) (Real.exp_pos _).le
  have he : (2 * Real.exp (-(9 : ℝ) * b / 2500)) *
      Real.exp ((3 : ℝ) * b / 2500) = 2 * Real.exp (-(3 : ℝ) * b / 1250) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [he] at h

theorem right_exceptional_fraction : (rightExceptionalCount : ℝ) / hardCount ≤
    2 * Real.exp (-(1 : ℝ) * b / 500) := by
  have hn : (rightExceptionalCount : ℝ) ≤ (rightTailCount : ℝ) * minorityCount := by
    exact_mod_cast (right_exceptional_product.trans_eq (Nat.mul_comm _ _))
  have h := ratio_product_bound _ _ _ _ _ _ _ (pow_pos (by norm_num) b)
    hard_count_pos hard_count_lower_real hn right_tail_count_bound minority_count_bound
    (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Real.exp_pos _).le) (Real.exp_pos _).le
  have he : (2 * Real.exp (-(2 : ℝ) * b / 625)) *
      Real.exp ((3 : ℝ) * b / 2500) = 2 * Real.exp (-(1 : ℝ) * b / 500) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [he] at h

theorem outside_phase_fraction : (outsidePhaseCount : ℝ) / hardCount ≤
    Real.exp (-(1 : ℝ) * b / 500) := by
  have hn : (outsidePhaseCount : ℝ) ≤ (minorityCount : ℝ) * minorityCount := by
    exact_mod_cast (outside_phase_product.trans_eq (pow_two _))
  have he : Real.exp (b : ℝ) ≤ (4 : ℝ) ^ b := by
    calc
      _ = (Real.exp 1) ^ b := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := by gcongr; linarith [Real.exp_one_lt_three]
  apply (div_le_iff₀ hard_count_pos).mpr
  calc
    _ ≤ (minorityCount : ℝ) * minorityCount := hn
    _ ≤ Real.exp ((3 : ℝ) * b / 2500) * Real.exp ((3 : ℝ) * b / 2500) :=
      mul_le_mul minority_count_bound minority_count_bound (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-(1 : ℝ) * b / 500) * Real.exp (b : ℝ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [b_pos_real]
    _ ≤ Real.exp (-(1 : ℝ) * b / 500) * hardCount :=
      mul_le_mul_of_nonneg_left (he.trans hard_count_lower_real) (Real.exp_pos _).le

def Bad (p : Config Point) : Prop := Hard p ∧ ¬GoodA p ∧ ¬GoodC p
def badCount : ℕ := Nat.card {p // Bad p}

theorem not_goodA_tail (p : Config Point) (hA : PhaseA p) (hnot : ¬GoodA p) : LeftTail p.1 := by
  unfold LeftTail
  by_contra hh
  have h := abs_lt.mp (lt_of_not_ge hh)
  apply hnot
  refine ⟨hA, ?_, ?_⟩ <;> unfold leftTotal <;> linarith [h.1, h.2]

theorem not_goodC_tail (p : Config Point) (hC : PhaseC p) (hnot : ¬GoodC p) : RightTail p.2 := by
  unfold RightTail
  by_contra hh
  have h := abs_lt.mp (lt_of_not_ge hh)
  apply hnot
  refine ⟨hC, ?_, ?_⟩ <;> unfold rightTotal <;> linarith [h.1, h.2]

theorem card_le_three {Ω : Type*} [Fintype Ω] (P Q R S : Ω → Prop)
    (hcover : ∀ x, P x → Q x ∨ R x ∨ S x) :
    Nat.card {x // P x} ≤ Nat.card {x // Q x} + Nat.card {x // R x} + Nat.card {x // S x} := by
  have hs : univ.filter P ⊆ (univ.filter Q ∪ univ.filter R) ∪ univ.filter S := by
    intro x hx
    rcases hcover x (mem_filter.mp hx).2 with h | h | h
    · simp only [mem_union, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inl h)
    · simp only [mem_union, mem_filter, mem_univ, true_and]; exact Or.inl (Or.inr h)
    · simp only [mem_union, mem_filter, mem_univ, true_and]; exact Or.inr h
  have h := (card_le_card hs).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem bad_count_cover : badCount ≤ outsidePhaseCount + leftExceptionalCount + rightExceptionalCount := by
  apply card_le_three Bad
    (fun p ↦ Hard p ∧ (occupied p.1).card < cutoff ∧ (occupied p.2).card < cutoff)
    (fun p ↦ PhaseA p ∧ LeftTail p.1) (fun p ↦ PhaseC p ∧ RightTail p.2)
  intro p hp
  by_cases ha : cutoff ≤ (occupied p.1).card
  · exact Or.inr (Or.inl ⟨⟨hp.1, ha⟩, not_goodA_tail p ⟨hp.1, ha⟩ hp.2.1⟩)
  · by_cases hc : cutoff ≤ (occupied p.2).card
    · exact Or.inr (Or.inr ⟨⟨hp.1, hc⟩, not_goodC_tail p ⟨hp.1, hc⟩ hp.2.2⟩)
    · exact Or.inl ⟨hp.1, Nat.lt_of_not_ge ha, Nat.lt_of_not_ge hc⟩

theorem bad_fraction_bound : (badCount : ℝ) / hardCount ≤ 5 * Real.exp (-(b : ℝ) / 500) := by
  have hn : (badCount : ℝ) ≤ outsidePhaseCount + leftExceptionalCount + rightExceptionalCount :=
    by exact_mod_cast bad_count_cover
  have hleft : (leftExceptionalCount : ℝ) / hardCount ≤ 2 * Real.exp (-(b : ℝ) / 500) := by
    apply left_exceptional_fraction.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    nlinarith [b_pos_real]
  have hout := outside_phase_fraction
  have hright := right_exceptional_fraction
  have hdiv := div_le_div_of_nonneg_right hn hard_count_pos.le
  rw [add_div, add_div] at hdiv
  simp only [neg_mul, one_mul] at hout hright
  linarith

theorem bad_fraction_small : (badCount : ℝ) / hardCount < 1 / (2 : ℝ) ^ 300 :=
  bad_fraction_bound.trans_lt hard_error_bound

def hardEvent {Ω : Type*} [Fintype Ω] (H P : Ω → Prop) : Finset {p // H p} :=
  univ.filter (fun p ↦ P p.val)

theorem mem_hardEvent {Ω : Type*} [Fintype Ω] (H P : Ω → Prop) (p : {p // H p}) :
    p ∈ hardEvent H P ↔ P p.val := by
  simp only [hardEvent, mem_filter, mem_univ, true_and]

theorem hard_event_card {Ω : Type*} [Fintype Ω] (H P : Ω → Prop)
    (hP : ∀ p, P p → H p) : (hardEvent H P).card = Nat.card {p // P p} := by
  let E : {p : {p // H p} // P p.val} ≃ {p // P p} :=
    { toFun := fun p ↦ ⟨p.val.val, p.property⟩
      invFun := fun p ↦ ⟨⟨p.val, hP p.val p.property⟩, p.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have h := Nat.card_congr E
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, hardEvent] using h

theorem predicate_balance {Ω : Type*} [Fintype Ω] (H A C GA GC B : Ω → Prop)
    (hAH : ∀ p, A p → H p) (hCH : ∀ p, C p → H p)
    (hGA : ∀ p, GA p → A p) (hGC : ∀ p, GC p → C p)
    (hBH : ∀ p, B p → H p) (hdis : ∀ p, A p → C p → False)
    (heq : Nat.card {p // A p} = Nat.card {p // C p})
    (hcover : ∀ p, H p → GA p ∨ GC p ∨ B p) :
    Nat.card {p // H p} ≤ 2 * Nat.card {p // GA p} + 2 * Nat.card {p // B p} ∧
    Nat.card {p // H p} ≤ 2 * Nat.card {p // GC p} + 2 * Nat.card {p // B p} := by
  have hd : Disjoint (hardEvent H A) (hardEvent H C) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact hdis p.val ((mem_hardEvent H A p).mp hp) ((mem_hardEvent H C p).mp hq)
  have he : (hardEvent H A).card = (hardEvent H C).card := by
    rw [hard_event_card H A hAH, hard_event_card H C hCH]
    exact heq
  have hga : hardEvent H GA ⊆ hardEvent H A := by
    intro p hp
    exact (mem_hardEvent H A p).mpr (hGA p.val ((mem_hardEvent H GA p).mp hp))
  have hgc : hardEvent H GC ⊆ hardEvent H C := by
    intro p hp
    exact (mem_hardEvent H C p).mpr (hGC p.val ((mem_hardEvent H GC p).mp hp))
  have hc : ∀ p : {p // H p}, p ∈ hardEvent H GA ∨
      p ∈ hardEvent H GC ∨ p ∈ hardEvent H B := by
    intro p
    rcases hcover p.val p.property with ha | hc | hb
    · exact Or.inl ((mem_hardEvent H GA p).mpr ha)
    · exact Or.inr (Or.inl ((mem_hardEvent H GC p).mpr hc))
    · exact Or.inr (Or.inr ((mem_hardEvent H B p).mpr hb))
  have h := DominationPhaseBalance.both_good_card_lower
    (hardEvent H A) (hardEvent H C) (hardEvent H GA) (hardEvent H GC) (hardEvent H B)
    hd he hga hgc hc
  rw [hard_event_card H GA (fun p hp ↦ hAH p (hGA p hp)),
    hard_event_card H GC (fun p hp ↦ hCH p (hGC p hp)), hard_event_card H B hBH] at h
  simpa only [← Nat.card_eq_fintype_card] using h

def goodACount : ℕ := Nat.card {p // GoodA p}
def goodCCount : ℕ := Nat.card {p // GoodC p}

theorem good_counts_balance : hardCount ≤ 2 * goodACount + 2 * badCount ∧
    hardCount ≤ 2 * goodCCount + 2 * badCount := by
  apply predicate_balance Hard PhaseA PhaseC GoodA GoodC Bad
    (fun _ h ↦ h.1) (fun _ h ↦ h.1) (fun _ h ↦ h.1) (fun _ h ↦ h.1)
    (fun _ h ↦ h.1) (fun p ha hc ↦ phase_disjoint p ⟨ha, hc⟩)
  · have h := phase_count_eq
    simpa only [← Nat.card_eq_fintype_card] using h
  · intro p hp
    by_cases ha : GoodA p
    · exact Or.inl ha
    · by_cases hc : GoodC p
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr ⟨hp, ha, hc⟩)

theorem goodA_fraction_lower : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ 300 ≤
    (goodACount : ℝ) / hardCount := by
  have hn : (hardCount : ℝ) ≤ 2 * goodACount + 2 * badCount :=
    by exact_mod_cast good_counts_balance.1
  have hdiv := (div_le_div_of_nonneg_right hn hard_count_pos.le)
  rw [div_self (ne_of_gt hard_count_pos), add_div] at hdiv
  have hb := bad_fraction_small
  have h1 : ((2 : ℝ) * goodACount) / hardCount = 2 * ((goodACount : ℝ) / hardCount) := by ring
  have h2 : ((2 : ℝ) * badCount) / hardCount = 2 * ((badCount : ℝ) / hardCount) := by ring
  rw [h1, h2] at hdiv
  linarith

theorem goodC_fraction_lower : (1 : ℝ) / 2 - 1 / (2 : ℝ) ^ 300 ≤
    (goodCCount : ℝ) / hardCount := by
  have hn : (hardCount : ℝ) ≤ 2 * goodCCount + 2 * badCount :=
    by exact_mod_cast good_counts_balance.2
  have hdiv := (div_le_div_of_nonneg_right hn hard_count_pos.le)
  rw [div_self (ne_of_gt hard_count_pos), add_div] at hdiv
  have hb := bad_fraction_small
  have h1 : ((2 : ℝ) * goodCCount) / hardCount = 2 * ((goodCCount : ℝ) / hardCount) := by ring
  have h2 : ((2 : ℝ) * badCount) / hardCount = 2 * ((badCount : ℝ) / hardCount) := by ring
  rw [h1, h2] at hdiv
  linarith

end Research.DominationHardPhaseBounds

#print axioms Research.DominationHardPhaseBounds.bad_fraction_small
#print axioms Research.DominationHardPhaseBounds.goodA_omitted_bounds
#print axioms Research.DominationHardPhaseBounds.goodC_omitted_bounds
#print axioms Research.DominationHardPhaseBounds.goodA_fraction_lower
#print axioms Research.DominationHardPhaseBounds.goodC_fraction_lower
