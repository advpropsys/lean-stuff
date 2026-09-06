import Research.DominationCanonicalPartition
import Research.DominationSizeIntervals

namespace Research.DominationIntervalMass
open DominationParameters DominationCanonicalPartition DominationGadgetGraph
open DominationIncidenceGraph DominationPartition DominationCloneSizes DominationSizeIntervals
noncomputable section
attribute [local instance] Classical.propDecidable
set_option synthInstance.maxSize 1024
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

def Prob (A : DomSet → Prop) : ℝ := (Fintype.card {S // A S} : ℝ)/D
def HardProb (A : Set Control → Prop) : ℝ :=
  (Fintype.card {P : HardControlSet // A P.val} : ℝ)/H
def CloneProb (B : Set Clone → Prop) : ℝ :=
  (Nat.card {C : Set Clone // B C} : ℝ)/2^L

def Joint (A : Set Control → Prop) (B : Set Clone → Prop) (S : DomSet) : Prop :=
  IsHard S ∧ A (omitted S.val) ∧ B (clonePart S.val)

def LeftBand (P : Set Control) : Prop :=
  92*(b : ℝ)/100 ≤ Nat.card P ∧ (Nat.card P : ℝ) ≤ 108*(b : ℝ)/100

def RightBand (P : Set Control) : Prop :=
  71*(b : ℝ)/100 ≤ Nat.card P ∧ (Nat.card P : ℝ) ≤ 80*(b : ℝ)/100

def CloneGood (C : Set Clone) : Prop := |(Nat.card C : ℝ)-(L : ℝ)/2| ≤ (b : ℝ)/100

theorem H_pos : 0 < H := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨∅, by intro e; simp⟩⟩

theorem H_real_pos : (0 : ℝ) < H := by exact_mod_cast H_pos

theorem prob_nonneg (A : DomSet → Prop) : 0 ≤ Prob A := by unfold Prob; positivity

theorem prob_mono {A B : DomSet → Prop} (h : ∀ S, A S → B S) : Prob A ≤ Prob B := by
  unfold Prob
  apply div_le_div_of_nonneg_right _ D_real_pos.le
  exact_mod_cast Fintype.card_subtype_mono A B h

theorem prob_union (A B : DomSet → Prop) :
    Prob (fun S => A S ∨ B S) ≤ Prob A + Prob B := by
  unfold Prob
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ D_real_pos.le
  have hn := Fintype.card_subtype_or A B
  simp only [Fintype.card_eq_nat_card] at hn ⊢
  exact_mod_cast hn

theorem hard_fraction_bounds : 1-1/(2:ℝ)^190 ≤ Prob IsHard ∧ Prob IsHard ≤ 1 := by
  have hsum : Fintype.card NonhardDomSet + Fintype.card HardDomSet = D := by
    rw [nonhard_count]
    exact Nat.sub_add_cancel hard_count_le_D
  have hr : (Fintype.card NonhardDomSet : ℝ)/D + Prob IsHard = 1 := by
    unfold Prob
    rw [← add_div]
    have hc : (Fintype.card NonhardDomSet : ℝ) + Fintype.card HardDomSet = D := by exact_mod_cast hsum
    rw [hc, div_self (ne_of_gt D_real_pos)]
  constructor
  · linarith [nonhard_fraction_lt]
  · have hn : 0 ≤ (Fintype.card NonhardDomSet : ℝ)/D :=
      div_nonneg (Nat.cast_nonneg _) D_real_pos.le
    linarith

theorem joint_count (A : Set Control → Prop) (B : Set Clone → Prop) :
    Nat.card {S : DomSet // Joint A B S} =
      Nat.card {P : HardControlSet // A P.val} * Nat.card {C : Set Clone // B C} := by
  simp only [Joint, IsHard]
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun S : Set DominationGadgetGraph.Vertex => Dominates finalGraph S)
    (fun S => Hard left right (omitted S) ∧ A (omitted S) ∧ B (clonePart S)))]
  have hh := hard_event_count left right (by norm_num [w]) no_isolated_controls A B
  change Nat.card {S : Set DominationGadgetGraph.Vertex // Dominates finalGraph S ∧
    Hard left right (omitted S) ∧ A (omitted S) ∧ B (clonePart S)} = _
  calc
    _ = Nat.card {P : Set Control // Hard left right P ∧ A P} *
        Nat.card {C : Set Clone // B C} := by simpa only [finalGraph] using hh
    _ = _ := ?_
  congr 1
  exact (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun P : Set Control => Hard left right P) A)).symm

theorem joint_prob (A : Set Control → Prop) (B : Set Clone → Prop) :
    Prob (Joint A B) = Prob IsHard * HardProb A * CloneProb B := by
  unfold Prob HardProb CloneProb
  rw [← Nat.card_eq_fintype_card (α := {S : DomSet // Joint A B S}), joint_count,
    Nat.cast_mul, Nat.card_eq_fintype_card]
  change _ = (Fintype.card HardDomSet : ℝ)/D * _ * _
  rw [hard_count, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hh := ne_of_gt H_real_pos
  have hd := ne_of_gt D_real_pos
  have hp : (2:ℝ)^L ≠ 0 := by positivity
  generalize (Fintype.card {P : HardControlSet // A P.val} : ℝ) = a
  generalize (Nat.card {C : Set Clone // B C} : ℝ) = c
  generalize (2:ℝ)^L = z at *
  generalize (H:ℝ) = x at *
  generalize (D:ℝ) = y at *
  field_simp

@[simp] theorem hardProb_true : HardProb (fun _ => True) = 1 := by
  unfold HardProb
  have hc : Fintype.card {P : HardControlSet // True} = H := by
    simp only [Fintype.card_subtype_true, H]
  have hc' : Fintype.card {P : HardControlSet // (fun _ : Set Control => True) P.val} = H :=
    (Fintype.card_congr (Equiv.refl _)).trans hc
  simp only [Fintype.card_eq_nat_card] at hc' ⊢
  rw [hc']
  exact div_self (ne_of_gt H_real_pos)

@[simp] theorem cloneProb_true : CloneProb (fun _ => True) = 1 := by
  unfold CloneProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_true, Fintype.card_set, clone_card]
  rw [Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (by positivity : (2:ℝ)^L ≠ 0)

theorem cloneProb_nonneg (B : Set Clone → Prop) : 0 ≤ CloneProb B := by
  unfold CloneProb
  positivity

theorem clone_bad_bound : CloneProb (fun C => ¬ CloneGood C) ≤ 1/(2:ℝ)^278 := by
  have hm : Nat.card {C : Set Clone // ¬ CloneGood C} ≤
      Nat.card {C : Set Clone // (b:ℝ)/100 ≤ |(Nat.card C:ℝ)-(L:ℝ)/2|} := by
    rw [Nat.card_eq_fintype_card (α := {C : Set Clone // ¬ CloneGood C}),
      Nat.card_eq_fintype_card (α := {C : Set Clone // (b:ℝ)/100 ≤ |(Nat.card C:ℝ)-(L:ℝ)/2|})]
    apply Fintype.card_subtype_mono
    intro C h
    exact le_of_lt (lt_of_not_ge h)
  unfold CloneProb
  apply le_trans _ canonical_clone_tail.le
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hm

theorem clone_good_bound : 1-1/(2:ℝ)^278 ≤ CloneProb CloneGood := by
  have hc : Nat.card {C : Set Clone // ¬ CloneGood C} + Nat.card {C : Set Clone // CloneGood C} = 2^L := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [Nat.sub_add_cancel (Fintype.card_subtype_le _), Fintype.card_set, clone_card]
  have hr : CloneProb (fun C => ¬ CloneGood C) + CloneProb CloneGood = 1 := by
    unfold CloneProb
    rw [← add_div, ← Nat.cast_add, hc]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact div_self (by positivity : (2:ℝ)^L ≠ 0)
  linarith [clone_bad_bound]

theorem joint_left_implies_interval (S : DomSet) (h : Joint LeftBand CloneGood S) :
    LeftInterval (size S) := by
  have hh := selected_in_left (omitted S.val) (clonePart S.val) h.2.1.1 h.2.1.2 h.2.2
  simpa only [size, omitted, clonePart, selected_representation] using hh

theorem joint_right_implies_interval (S : DomSet) (h : Joint RightBand CloneGood S) :
    RightInterval (size S) := by
  have hh := selected_in_right (omitted S.val) (clonePart S.val) h.2.1.1 h.2.1.2 h.2.2
  simpa only [size, omitted, clonePart, selected_representation] using hh

private theorem product_lower (a c d : ℝ)
    (ha : 1-1/(2:ℝ)^190 ≤ a) (hc : 1/2-1/(2:ℝ)^300 ≤ c)
    (hd : 1-1/(2:ℝ)^278 ≤ d) :
    (1-1/(2:ℝ)^190)*(1/2-1/(2:ℝ)^300)*(1-1/(2:ℝ)^278) ≤ a*c*d := by
  have hp : 0 ≤ (1-1/(2:ℝ)^190) := by norm_num
  have hq : 0 ≤ (1/2-1/(2:ℝ)^300) := by norm_num
  have hr : 0 ≤ (1-1/(2:ℝ)^278) := by norm_num
  have ha0 := le_trans hp ha
  have hc0 := le_trans hq hc
  exact mul_le_mul (mul_le_mul ha hc hq ha0) hd hr (mul_nonneg ha0 hc0)

/-- Conditional only on the exact left hard-control band fraction. -/
theorem left_interval_mass
    (hA : 1/2-1/(2:ℝ)^300 ≤ HardProb LeftBand) :
    (1-1/(2:ℝ)^190)*(1/2-1/(2:ℝ)^300)*(1-1/(2:ℝ)^278) ≤
      Prob (fun S => LeftInterval (size S)) := by
  calc
    _ ≤ Prob IsHard * HardProb LeftBand * CloneProb CloneGood := by
      exact product_lower _ _ _ hard_fraction_bounds.1 hA clone_good_bound
    _ = Prob (Joint LeftBand CloneGood) := (joint_prob _ _).symm
    _ ≤ _ := prob_mono joint_left_implies_interval

/-- Conditional only on the exact right hard-control band fraction. -/
theorem right_interval_mass
    (hA : 1/2-1/(2:ℝ)^300 ≤ HardProb RightBand) :
    (1-1/(2:ℝ)^190)*(1/2-1/(2:ℝ)^300)*(1-1/(2:ℝ)^278) ≤
      Prob (fun S => RightInterval (size S)) := by
  calc
    _ ≤ Prob IsHard * HardProb RightBand * CloneProb CloneGood := by
      exact product_lower _ _ _ hard_fraction_bounds.1 hA clone_good_bound
    _ = Prob (Joint RightBand CloneGood) := (joint_prob _ _).symm
    _ ≤ _ := prob_mono joint_right_implies_interval

theorem mass_constant_gt_third :
    (1/3:ℝ) < (1-1/(2:ℝ)^190)*(1/2-1/(2:ℝ)^300)*(1-1/(2:ℝ)^278) := by
  norm_num

theorem left_interval_gt_third (hA : 1/2-1/(2:ℝ)^300 ≤ HardProb LeftBand) :
    (1/3:ℝ) < Prob (fun S => LeftInterval (size S)) :=
  lt_of_lt_of_le mass_constant_gt_third (left_interval_mass hA)

theorem right_interval_gt_third (hA : 1/2-1/(2:ℝ)^300 ≤ HardProb RightBand) :
    (1/3:ℝ) < Prob (fun S => RightInterval (size S)) :=
  lt_of_lt_of_le mass_constant_gt_third (right_interval_mass hA)

/-- Conditional only on the hard-control mass outside the two omitted-size bands. -/
theorem outside_intervals_bound
    (hBad : HardProb (fun P => ¬ (LeftBand P ∨ RightBand P)) ≤ 1/(2:ℝ)^300) :
    Prob (fun S => ¬ (LeftInterval (size S) ∨ RightInterval (size S))) ≤
      1/(2:ℝ)^190 + 1/(2:ℝ)^300 + 1/(2:ℝ)^278 := by
  let A : DomSet → Prop := fun S => ¬ IsHard S
  let B : DomSet → Prop := Joint (fun P => ¬ (LeftBand P ∨ RightBand P)) (fun _ => True)
  let C : DomSet → Prop := Joint (fun _ => True) (fun C => ¬ CloneGood C)
  have hcover : ∀ S : DomSet, ¬ (LeftInterval (size S) ∨ RightInterval (size S)) →
      A S ∨ B S ∨ C S := by
    intro S hS
    by_cases hh : IsHard S
    · by_cases hb : LeftBand (omitted S.val) ∨ RightBand (omitted S.val)
      · by_cases hc : CloneGood (clonePart S.val)
        · rcases hb with hl | hr
          · exact (hS (Or.inl (joint_left_implies_interval S ⟨hh,hl,hc⟩))).elim
          · exact (hS (Or.inr (joint_right_implies_interval S ⟨hh,hr,hc⟩))).elim
        · exact Or.inr (Or.inr ⟨hh,trivial,hc⟩)
      · exact Or.inr (Or.inl ⟨hh,hb,trivial⟩)
    · exact Or.inl hh
  have ha : Prob A ≤ 1/(2:ℝ)^190 := by
    have he : Fintype.card {S : DomSet // A S} = Fintype.card NonhardDomSet :=
      Fintype.card_congr (Equiv.refl _)
    unfold Prob
    have hh := nonhard_fraction_lt.le
    simp only [Fintype.card_eq_nat_card] at he hh ⊢
    rw [he]
    exact hh
  have hb : Prob B ≤ 1/(2:ℝ)^300 := by
    dsimp [B]
    rw [joint_prob, cloneProb_true, mul_one]
    have hp : 0 ≤ HardProb (fun P => ¬ (LeftBand P ∨ RightBand P)) := by
      unfold HardProb; positivity
    exact le_trans (mul_le_of_le_one_left hp hard_fraction_bounds.2) hBad
  have hc : Prob C ≤ 1/(2:ℝ)^278 := by
    dsimp [C]
    rw [joint_prob, hardProb_true, mul_one]
    exact le_trans (mul_le_of_le_one_left (cloneProb_nonneg _) hard_fraction_bounds.2) clone_bad_bound
  have h1 := prob_mono hcover
  have h2 := prob_union A (fun S => B S ∨ C S)
  have h3 := prob_union B C
  linarith

#print axioms left_interval_mass
#print axioms right_interval_mass
#print axioms outside_intervals_bound
#print axioms joint_prob
#print axioms clone_good_bound
end
end Research.DominationIntervalMass
