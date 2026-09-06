import Research.DominationPartition
import Research.DominationFiniteTails
import Research.DominationGadgetGraph

namespace Research.DominationCloneSizes
open DominationIncidenceGraph DominationPartition
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option synthInstance.maxSize 1024

/-- Selected controls and selected clones are disjoint summands. -/
theorem selected_size {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (P : Set C) (K : Set (E × Fin w)) :
    Nat.card (selected P K) = Fintype.card C - Nat.card P + Nat.card K := by
  rw [Nat.card_congr Equiv.subtypeSum, Nat.card_sum]
  change Nat.card {c : C // c ∉ P} + Nat.card K = _
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- All clone choices are valid for an edge-free omitted control set. -/
theorem hard_all_clones {C E : Type*} {w : ℕ} (left right : E → C)
    (hw : 0 < w) (hi : ∀ c, ∃ e, c = left e ∨ c = right e)
    (P : Set C) (hP : Hard left right P) (K : Set (E × Fin w)) :
    Dominates (graph w left right) (selected P K) := by
  apply (dominates_iff_forced left right hw hi P K).2
  intro e i hl hr
  exact (hP e ⟨hl,hr⟩).elim

/-- Restricting a hard control event and a clone event gives an exact product. -/
def hardEventEquiv {C E : Type*} {w : ℕ} (left right : E → C)
    (hw : 0 < w) (hi : ∀ c, ∃ e, c = left e ∨ c = right e)
    (A : Set C → Prop) (B : Set (E × Fin w) → Prop) :
    {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
      Hard left right (omitted S) ∧ A (omitted S) ∧ B (clonePart S)} ≃
    ({P : Set C // Hard left right P ∧ A P} × {K : Set (E × Fin w) // B K}) where
  toFun S := (⟨omitted S.val, S.property.2.1, S.property.2.2.1⟩,
    ⟨clonePart S.val,S.property.2.2.2⟩)
  invFun x := ⟨selected x.1.val x.2.val,
    hard_all_clones left right hw hi x.1.val x.1.property.1 x.2.val,
    by simpa using x.1.property.1,
    by simpa using x.1.property.2,
    by simpa using x.2.property⟩
  left_inv S := by
    apply Subtype.ext
    exact selected_representation S.val
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      exact omitted_selected _ _
    · apply Subtype.ext
      rfl

theorem hard_event_count {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hi : ∀ c, ∃ e, c = left e ∨ c = right e)
    (A : Set C → Prop) (B : Set (E × Fin w) → Prop) :
    Nat.card {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
      Hard left right (omitted S) ∧ A (omitted S) ∧ B (clonePart S)} =
    Nat.card {P : Set C // Hard left right P ∧ A P} *
      Nat.card {K : Set (E × Fin w) // B K} := by
  rw [Nat.card_congr (hardEventEquiv left right hw hi A B), Nat.card_prod]

private def setFinsetEquiv (J : Type*) [Fintype J] : Set J ≃ Finset J where
  toFun S := S.toFinset
  invFun T := (T : Set J)
  left_inv S := by simp
  right_inv T := by simp

/-- Explicit transport of arbitrary finite subsets to subsets of Fin(card J). -/
def subsetFinEquiv (J : Type*) [Fintype J] : Set J ≃ Finset (Fin (Fintype.card J)) :=
  (setFinsetEquiv J).trans (Fintype.equivFin J).finsetCongr

theorem subsetFinEquiv_card (J : Type*) [Fintype J] (S : Set J) :
    (subsetFinEquiv J S).card = Nat.card S := by
  simp [subsetFinEquiv, setFinsetEquiv, Equiv.finsetCongr, Nat.card_eq_fintype_card]

/-- Exact normalized subset-count tail for every finite ground type. -/
theorem finite_set_tail (J : Type*) [Fintype J] (hJ : 0 < Fintype.card J)
    (u : ℝ) (hu : 0 ≤ u) :
    (Nat.card {S : Set J // u ≤ |(Nat.card S : ℝ) - Fintype.card J / 2|} : ℝ) /
      2 ^ Fintype.card J ≤ 2 * Real.exp (-2 * u^2 / Fintype.card J) := by
  let e := subsetFinEquiv J
  let E : {S : Set J // u ≤ |(Nat.card S : ℝ) - Fintype.card J / 2|} ≃
      {T : Finset (Fin (Fintype.card J)) // u ≤ |(T.card : ℝ) - Fintype.card J / 2|} :=
    { toFun := fun S => ⟨e S.val, by
        change u ≤ |((subsetFinEquiv J S.val).card : ℝ) - Fintype.card J / 2|
        rw [subsetFinEquiv_card]
        exact S.property⟩
      invFun := fun T => ⟨e.symm T.val, by
        have h := subsetFinEquiv_card J (e.symm T.val)
        change (e (e.symm T.val)).card = _ at h
        rw [e.apply_symm_apply] at h
        rw [← h]
        exact T.property⟩
      left_inv := fun S => Subtype.ext (e.symm_apply_apply S.val)
      right_inv := fun T => Subtype.ext (e.apply_symm_apply T.val) }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card]
  exact DominationFiniteTails.subset_tail (Fintype.card J) hJ u hu

open DominationParameters
abbrev Clone := DominationGadgetGraph.Edge × Fin w

theorem clone_card : Fintype.card Clone = L := by
  rw [Fintype.card_prod, DominationGadgetGraph.edge_card, Fintype.card_fin]
  simp only [L, Nat.mul_comm]

/-- The canonical clone noise has probability strictly below 2^-278. -/
theorem canonical_clone_tail :
    (Nat.card {K : Set Clone // (b : ℝ)/100 ≤ |(Nat.card K : ℝ) - (L : ℝ)/2|} : ℝ) /
      2 ^ L < 1 / (2 : ℝ)^278 := by
  have h := finite_set_tail Clone (by rw [clone_card]; norm_num [L, w, m, b, q])
    ((b : ℝ)/100) (by positivity)
  rw [clone_card] at h
  have he : -2 * ((b : ℝ)/100)^2 / L = -(b : ℝ)/(5000*w*(6*q+9)) := by
    norm_num [L, w, m, b, q]
  rw [he] at h
  exact lt_of_le_of_lt h noise_error_bound

#print axioms selected_size
#print axioms hard_event_count
#print axioms canonical_clone_tail
end
end Research.DominationCloneSizes
