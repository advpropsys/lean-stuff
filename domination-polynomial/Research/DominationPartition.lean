import Research.DominationIncidenceGraph
import Research.DominationSoftComparison
import Mathlib

/-! Exact global counts for the split graph with indexed edge cohorts.
No distinctness assumption on endpoint pairs is made. -/
namespace Research.DominationPartition

open Research.DominationIncidenceGraph

noncomputable section
attribute [local instance] Classical.propDecidable

def omitted {C E : Type*} {w : ℕ} (S : Set (Vertex C E w)) : Set C :=
  {c | Sum.inl c ∉ S}

def clonePart {C E : Type*} {w : ℕ} (S : Set (Vertex C E w)) : Set (E × Fin w) :=
  {j | Sum.inr j ∈ S}

@[simp] theorem omitted_selected {C E : Type*} {w : ℕ}
    (P : Set C) (K : Set (E × Fin w)) : omitted (selected P K) = P := by
  ext c
  simp [omitted]

@[simp] theorem clonePart_selected {C E : Type*} {w : ℕ}
    (P : Set C) (K : Set (E × Fin w)) : clonePart (selected P K) = K := rfl

def dominatingEquivSigma {C E : Type*} (w : ℕ) (left right : E → C) :
    {S : Set (Vertex C E w) // Dominates (graph w left right) S} ≃
      (Σ P : Set C, {K : Set (E × Fin w) //
        Dominates (graph w left right) (selected P K)}) where
  toFun S := ⟨omitted S.val, ⟨clonePart S.val, by
    simpa [omitted, clonePart, selected_representation] using S.property⟩⟩
  invFun P := ⟨selected P.1 P.2.val, P.2.property⟩
  left_inv S := by
    apply Subtype.ext
    exact selected_representation S.val
  right_inv P := by
    rcases P with ⟨P, K, hK⟩
    refine Sigma.ext (omitted_selected P K) ?_
    apply (Subtype.heq_iff_coe_eq (by intro K'; simp only [omitted_selected])).2
    rfl

/-- The full dominating-set count, summed over every omitted-control fiber. -/
theorem dominating_count {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e) :
    Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S} =
      ∑ P : Set C, 2 ^ (Fintype.card E * w -
        Fintype.card (inducedEdges left right P) * w) := by
  rw [Fintype.card_congr (dominatingEquivSigma w left right), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro P hP
  exact dominating_fiber_count left right hw hincident P

def Hard {C E : Type*} (left right : E → C) (P : Set C) : Prop :=
  ∀ e, ¬ (left e ∈ P ∧ right e ∈ P)

theorem inducedEdges_empty_of_hard {C E : Type*} (left right : E → C)
    (P : Set C) (hP : Hard left right P) : inducedEdges left right P = ∅ := by
  ext e
  simp only [inducedEdges, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact hP e

def hardDominatingEquivSigma {C E : Type*} (w : ℕ) (left right : E → C) :
    {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
      Hard left right (omitted S)} ≃
      (Σ P : {P : Set C // Hard left right P}, {K : Set (E × Fin w) //
        Dominates (graph w left right) (selected P.val K)}) where
  toFun S := ⟨⟨omitted S.val, S.property.2⟩, ⟨clonePart S.val, by
    simpa [omitted, clonePart, selected_representation] using S.property.1⟩⟩
  invFun P := ⟨selected P.1.val P.2.val, P.2.property, by
    simpa using P.1.property⟩
  left_inv S := by
    apply Subtype.ext
    exact selected_representation S.val
  right_inv P := by
    rcases P with ⟨⟨P, hP⟩, K, hK⟩
    refine Sigma.ext (Subtype.ext (omitted_selected P K)) ?_
    apply (Subtype.heq_iff_coe_eq (by intro K'; simp only [omitted_selected])).2
    rfl

/-- Hard configurations have exactly all clone choices available. -/
theorem hard_dominating_count {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e) :
    Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
      Hard left right (omitted S)} =
      Fintype.card {P : Set C // Hard left right P} * 2 ^ (Fintype.card E * w) := by
  rw [Fintype.card_congr (hardDominatingEquivSigma w left right), Fintype.card_sigma]
  calc
    (∑ P : {P : Set C // Hard left right P}, Fintype.card
      {K : Set (E × Fin w) // Dominates (graph w left right) (selected P.val K)}) =
        ∑ _P : {P : Set C // Hard left right P}, 2 ^ (Fintype.card E * w) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [dominating_fiber_count left right hw hincident P.val,
        inducedEdges_empty_of_hard left right P.val P.property]
      simp
    _ = _ := by simp

/-- The soft-to-hard comparison for labeled edges. Repeated endpoint pairs and
even equal endpoints are permitted; removing all left endpoints is sufficient. -/
theorem labeled_soft_comparison {C E : Type*} [Fintype C] [Fintype E]
    (left right : E → C) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (∑ P : Set C, ρ ^ Fintype.card (inducedEdges left right P)) ≤
      (Fintype.card {P : Set C // Hard left right P} : ℝ) *
        (1 + ρ) ^ Fintype.card C := by
  classical
  let R : Set C → Finset C := fun P => (inducedEdges left right P).toFinset.image left
  have hR (P : Set C) : (↑(R P) : Set C) ⊆ P := by
    intro c hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hc
    exact (Set.mem_toFinset.mp he).1
  let clean : Set C → {P : Set C // Hard left right P} := fun P =>
    ⟨P \ (↑(R P) : Set C), by
      intro e he
      have hr : left e ∈ R P := Finset.mem_image.mpr
        ⟨e, Set.mem_toFinset.mpr ⟨he.1.1, he.2.1⟩, rfl⟩
      exact he.1.2 hr⟩
  have recover (P : Set C) : (clean P).val ∪ (↑(R P) : Set C) = P := by
    ext c
    change (c ∈ P ∧ c ∉ R P) ∨ c ∈ R P ↔ c ∈ P
    have hp : c ∈ R P → c ∈ P := fun h => hR P h
    tauto
  have hinj : Function.Injective (fun P => (clean P, R P)) := by
    intro P Q heq
    have hI : clean P = clean Q := congrArg Prod.fst heq
    have hR' : R P = R Q := congrArg Prod.snd heq
    calc
      P = (clean P).val ∪ (↑(R P) : Set C) := (recover P).symm
      _ = (clean Q).val ∪ (↑(R Q) : Set C) := by rw [hI, hR']
      _ = Q := recover Q
  have hcost (P : Set C) : (R P).card ≤ Fintype.card (inducedEdges left right P) := by
    calc
      (R P).card ≤ (inducedEdges left right P).toFinset.card := Finset.card_image_le
      _ = _ := Set.toFinset_card _
  exact Research.DominationSoftComparison.weighted_injection_bound clean R
    (fun P => Fintype.card (inducedEdges left right P)) hinj hcost ρ hρ0 hρ1

/-- Factoring out the common number of optional-clone configurations gives the
exact real partition function of the actual dominating subsets. -/
theorem dominating_count_normalized {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e) :
    (Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S} : ℝ) =
      (2 : ℝ) ^ (Fintype.card E * w) *
        ∑ P : Set C, (((2 : ℝ) ^ w)⁻¹) ^ Fintype.card (inducedEdges left right P) := by
  rw [dominating_count left right hw hincident]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  have he : Fintype.card (inducedEdges left right P) ≤ Fintype.card E :=
    Fintype.card_subtype_le _
  rw [pow_sub₀ (2 : ℝ) (by norm_num) (Nat.mul_le_mul_right w he), inv_pow, ← pow_mul]
  rw [Nat.mul_comm w]

/-- Upper bound on the total count in terms of the actual hard dominating sets. -/
theorem dominating_count_le_hard_factor {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e) :
    (Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S} : ℝ) ≤
      (Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
        Hard left right (omitted S)} : ℝ) *
      (1 + ((2 : ℝ) ^ w)⁻¹) ^ Fintype.card C := by
  have hsoft := labeled_soft_comparison left right (((2 : ℝ) ^ w)⁻¹)
    (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))
  rw [dominating_count_normalized left right hw hincident]
  calc
    _ ≤ (2 : ℝ) ^ (Fintype.card E * w) *
        ((Fintype.card {P : Set C // Hard left right P} : ℝ) *
          (1 + ((2 : ℝ) ^ w)⁻¹) ^ Fintype.card C) :=
      mul_le_mul_of_nonneg_left hsoft (by positivity)
    _ = _ := by
      rw [hard_dominating_count left right hw hincident]
      push_cast
      ring

theorem count_conjunction_complement {A : Type*} [Fintype A] (p q : A → Prop) :
    Fintype.card {a // p a ∧ ¬ q a} = Fintype.card {a // p a} -
      Fintype.card {a // p a ∧ q a} := by
  calc
    _ = Fintype.card {a : {a // p a} // ¬ q a.val} :=
      (Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p (fun a => ¬ q a))).symm
    _ = Fintype.card {a // p a} - Fintype.card {a : {a // p a} // q a.val} :=
      Fintype.card_subtype_compl _
    _ = _ := by rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q)]

/-- Exact finite uniform-measure soft error: the fraction of actual dominating
sets whose omitted controls contain an indexed edge is at most the claimed factor. -/
theorem nonhard_fraction_bound {C E : Type*} [Fintype C] [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e) :
    (Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
      ¬ Hard left right (omitted S)} : ℝ) /
      (Fintype.card {S : Set (Vertex C E w) // Dominates (graph w left right) S} : ℝ) ≤
        (1 + ((2 : ℝ) ^ w)⁻¹) ^ Fintype.card C - 1 := by
  let D := {S : Set (Vertex C E w) // Dominates (graph w left right) S}
  let H := {S : Set (Vertex C E w) // Dominates (graph w left right) S ∧
    Hard left right (omitted S)}
  have hle : Fintype.card H ≤ Fintype.card D := by
    apply Fintype.card_le_of_injective (fun S : H => (⟨S.val, S.property.1⟩ : D))
    intro S T h
    apply Subtype.ext
    exact congrArg (fun x : D => x.val) h
  have hposNat : 0 < Fintype.card D := by
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨Set.univ, ?_⟩⟩
    intro v
    exact Or.inl (Set.mem_univ _)
  have hpos : (0 : ℝ) < Fintype.card D := by exact_mod_cast hposNat
  have hleReal : (Fintype.card H : ℝ) ≤ Fintype.card D := by exact_mod_cast hle
  have hfactor : (1 : ℝ) ≤ (1 + ((2 : ℝ) ^ w)⁻¹) ^ Fintype.card C := by
    apply one_le_pow₀
    have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ w)⁻¹ := by positivity
    linarith
  rw [count_conjunction_complement, Nat.cast_sub hle]
  apply (div_le_iff₀ hpos).2
  have hb := dominating_count_le_hard_factor left right hw hincident
  change (Fintype.card D : ℝ) ≤ (Fintype.card H : ℝ) *
    (1 + ((2 : ℝ) ^ w)⁻¹) ^ Fintype.card C at hb
  have hmul := mul_nonneg (sub_nonneg.mpr hleReal) (sub_nonneg.mpr hfactor)
  change (Fintype.card D : ℝ) - Fintype.card H ≤
    ((1 + ((2 : ℝ) ^ w)⁻¹) ^ Fintype.card C - 1) * Fintype.card D
  nlinarith [hb, hmul]

end
end Research.DominationPartition

#print axioms Research.DominationPartition.dominating_count
#print axioms Research.DominationPartition.hard_dominating_count
#print axioms Research.DominationPartition.labeled_soft_comparison
#print axioms Research.DominationPartition.dominating_count_normalized
#print axioms Research.DominationPartition.nonhard_fraction_bound
