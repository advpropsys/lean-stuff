import Research.DominationCloneSizes

namespace Research.DominationSizeIntervals
open DominationParameters
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option synthInstance.maxSize 1024

/-- The left coefficient interval, centered near K-b. -/
def LeftInterval (k : ℕ) : Prop :=
  (K : ℝ) - 109*(b : ℝ)/100 ≤ k ∧ (k : ℝ) ≤ (K : ℝ) - 91*(b : ℝ)/100

/-- The right coefficient interval, centered near K-3b/4. -/
def RightInterval (k : ℕ) : Prop :=
  (K : ℝ) - 81*(b : ℝ)/100 ≤ k ∧ (k : ℝ) ≤ (K : ℝ) - 70*(b : ℝ)/100

def LeftIndex (i : Fin (n+1)) : Prop := LeftInterval i.val
def RightIndex (i : Fin (n+1)) : Prop := RightInterval i.val

def valleyIndex : Fin (n+1) := ⟨j, by have := valley_valid; omega⟩

@[simp] theorem valleyIndex_val : valleyIndex.val = j := rfl

theorem K_cast : (K : ℝ) = (t : ℝ) + (L : ℝ)/2 := by
  norm_num [K, t, L, w, m, b, q]

/-- Omitted-control size in [0.92b,1.08b] and clone-count deviation at most b/100
place the total selected size in the left interval. -/
theorem left_of_sizes (p k : ℕ) (hp : p ≤ t)
    (hlo : 92*(b : ℝ)/100 ≤ p) (hhi : (p : ℝ) ≤ 108*(b : ℝ)/100)
    (hk : |(k : ℝ) - (L : ℝ)/2| ≤ (b : ℝ)/100) :
    LeftInterval (t-p+k) := by
  have hnoise := abs_le.mp hk
  unfold LeftInterval
  rw [Nat.cast_add, Nat.cast_sub hp, K_cast]
  constructor <;> linarith [hnoise.1, hnoise.2]

/-- Omitted-control size in [0.71b,0.80b] and clone-count deviation at most b/100
place the total selected size in the right interval. -/
theorem right_of_sizes (p k : ℕ) (hp : p ≤ t)
    (hlo : 71*(b : ℝ)/100 ≤ p) (hhi : (p : ℝ) ≤ 80*(b : ℝ)/100)
    (hk : |(k : ℝ) - (L : ℝ)/2| ≤ (b : ℝ)/100) :
    RightInterval (t-p+k) := by
  have hnoise := abs_le.mp hk
  unfold RightInterval
  rw [Nat.cast_add, Nat.cast_sub hp, K_cast]
  constructor <;> linarith [hnoise.1, hnoise.2]

open DominationGadgetGraph DominationIncidenceGraph

theorem control_subset_size_le (P : Set Control) : Nat.card P ≤ t := by
  rw [Nat.card_eq_fintype_card, ← control_card]
  exact Fintype.card_subtype_le _

theorem selected_in_left (P : Set Control) (C : Set DominationCloneSizes.Clone)
    (hlo : 92*(b : ℝ)/100 ≤ Nat.card P)
    (hhi : (Nat.card P : ℝ) ≤ 108*(b : ℝ)/100)
    (hC : |(Nat.card C : ℝ) - (L : ℝ)/2| ≤ (b : ℝ)/100) :
    LeftInterval (Nat.card (selected P C)) := by
  rw [DominationCloneSizes.selected_size, control_card]
  exact left_of_sizes _ _ (control_subset_size_le P) hlo hhi hC

theorem selected_in_right (P : Set Control) (C : Set DominationCloneSizes.Clone)
    (hlo : 71*(b : ℝ)/100 ≤ Nat.card P)
    (hhi : (Nat.card P : ℝ) ≤ 80*(b : ℝ)/100)
    (hC : |(Nat.card C : ℝ) - (L : ℝ)/2| ≤ (b : ℝ)/100) :
    RightInterval (Nat.card (selected P C)) := by
  rw [DominationCloneSizes.selected_size, control_card]
  exact right_of_sizes _ _ (control_subset_size_le P) hlo hhi hC

theorem left_before_valley {k : ℕ} (hk : LeftInterval k) : k < j := by
  have hsep : (K : ℝ) - 91*(b : ℝ)/100 < j := by
    norm_num [j, K, t, L, w, m, b, q]
  exact_mod_cast lt_of_le_of_lt hk.2 hsep

theorem right_after_valley {k : ℕ} (hk : RightInterval k) : j < k := by
  have hsep : (j : ℝ) < (K : ℝ) - 81*(b : ℝ)/100 := by
    norm_num [j, K, t, L, w, m, b, q]
  exact_mod_cast lt_of_lt_of_le hsep hk.1

theorem leftIndex_before_valley {i : Fin (n+1)} (hi : LeftIndex i) :
    i < valleyIndex := left_before_valley hi

theorem rightIndex_after_valley {i : Fin (n+1)} (hi : RightIndex i) :
    valleyIndex < i := right_after_valley hi

theorem valley_not_left : ¬ LeftInterval j := fun h => Nat.lt_irrefl j (left_before_valley h)
theorem valley_not_right : ¬ RightInterval j := fun h => Nat.lt_irrefl j (right_after_valley h)

theorem valleyIndex_not_left : ¬ LeftIndex valleyIndex := valley_not_left
theorem valleyIndex_not_right : ¬ RightIndex valleyIndex := valley_not_right

#print axioms selected_in_left
#print axioms selected_in_right
#print axioms leftIndex_before_valley
#print axioms rightIndex_after_valley
end
end Research.DominationSizeIntervals
