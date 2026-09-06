import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-! The split graph construction and its exact domination predicate.
This file does not prove a coefficient valley. -/
namespace Research.DominationIncidenceGraph

abbrev Vertex (C E : Type*) (w : ℕ) := C ⊕ (E × Fin w)

def adjacent {C E : Type*} {w : ℕ} (left right : E → C) :
    Vertex C E w → Vertex C E w → Prop
  | .inl c, .inl d => c ≠ d
  | .inl c, .inr (e, _) => c = left e ∨ c = right e
  | .inr (e, _), .inl c => c = left e ∨ c = right e
  | .inr _, .inr _ => False

def graph {C E : Type*} (w : ℕ) (left right : E → C) :
    SimpleGraph (Vertex C E w) where
  Adj := adjacent left right
  symm := by
    intro u v h
    cases u <;> cases v <;> simp_all [adjacent, ne_comm]
  loopless := ⟨by intro v; cases v <;> simp [adjacent]⟩

/-- Domination by closed neighborhoods. -/
def Dominates {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ v, v ∈ S ∨ ∃ u, u ∈ S ∧ G.Adj v u

/-- `P` is the omitted control set; `K` is the selected clone set. -/
def selected {C E : Type*} {w : ℕ} (P : Set C) (K : Set (E × Fin w)) :
    Set (Vertex C E w) :=
  {v | match v with
    | .inl c => c ∉ P
    | .inr j => j ∈ K}

def ForcedIncluded {C E : Type*} {w : ℕ} (left right : E → C)
    (P : Set C) (K : Set (E × Fin w)) : Prop :=
  ∀ e i, left e ∈ P → right e ∈ P → (e, i) ∈ K

@[simp] theorem selected_control {C E : Type*} {w : ℕ}
    (P : Set C) (K : Set (E × Fin w)) (c : C) :
    Sum.inl c ∈ selected P K ↔ c ∉ P := Iff.rfl

@[simp] theorem selected_clone {C E : Type*} {w : ℕ}
    (P : Set C) (K : Set (E × Fin w)) (j : E × Fin w) :
    Sum.inr j ∈ selected P K ↔ j ∈ K := Iff.rfl

theorem dominating_implies_forced {C E : Type*} {w : ℕ}
    (left right : E → C) (P : Set C) (K : Set (E × Fin w))
    (h : Dominates (graph w left right) (selected P K)) :
    ForcedIncluded left right P K := by
  intro e i hl hr
  rcases h (.inr (e, i)) with hmem | ⟨u, hu, hadj⟩
  · exact hmem
  · cases u with
    | inl c =>
      change c ∉ P at hu
      change c = left e ∨ c = right e at hadj
      rcases hadj with hc | hc
      · exact (hu (hc.symm ▸ hl)).elim
      · exact (hu (hc.symm ▸ hr)).elim
    | inr j =>
      change False at hadj
      exact hadj.elim

/-- With positive clone multiplicity and no isolated controls, forced-clone
membership is the full domination condition, even when all controls are omitted.
Distinct endpoints are not needed for this implication. -/
theorem dominates_iff_forced {C E : Type*} {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e)
    (P : Set C) (K : Set (E × Fin w)) :
    Dominates (graph w left right) (selected P K) ↔
      ForcedIncluded left right P K := by
  classical
  constructor
  · exact dominating_implies_forced left right P K
  · intro h v
    cases v with
    | inl c =>
      by_cases hc : c ∈ P
      · right
        by_cases hex : ∃ z : C, z ∉ P
        · obtain ⟨z, hz⟩ := hex
          refine ⟨.inl z, hz, ?_⟩
          change c ≠ z
          intro heq
          exact hz (heq ▸ hc)
        · have hall : ∀ z : C, z ∈ P := by
            intro z
            by_contra hz
            exact hex ⟨z, hz⟩
          obtain ⟨e, he⟩ := hincident c
          refine ⟨.inr (e, ⟨0, hw⟩), h e ⟨0, hw⟩ (hall _) (hall _), ?_⟩
          exact he
      · exact Or.inl hc
    | inr j =>
      obtain ⟨e, i⟩ := j
      by_cases hl : left e ∈ P
      · by_cases hr : right e ∈ P
        · exact Or.inl (h e i hl hr)
        · refine Or.inr ⟨.inl (right e), hr, ?_⟩
          exact Or.inr rfl
      · refine Or.inr ⟨.inl (left e), hl, ?_⟩
        exact Or.inl rfl

/-- If all controls are omitted, every clone must be selected. -/
theorem all_controls_omitted {C E : Type*} {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e)
    (K : Set (E × Fin w)) :
    Dominates (graph w left right) (selected Set.univ K) ↔ K = Set.univ := by
  rw [dominates_iff_forced left right hw hincident]
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    rintro ⟨e, i⟩
    exact h e i (Set.mem_univ _) (Set.mem_univ _)
  · intro h
    subst K
    intro e i _ _
    exact Set.mem_univ _

/-- Every vertex subset has the omitted-control/selected-clone representation. -/
theorem selected_representation {C E : Type*} {w : ℕ}
    (S : Set (Vertex C E w)) :
    selected {c | Sum.inl c ∉ S} {j | Sum.inr j ∈ S} = S := by
  classical
  ext v
  cases v <;> simp [selected]

/-- The characterization applied directly to an arbitrary vertex subset. -/
theorem dominates_iff_endpoints_or_clone {C E : Type*} {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e)
    (S : Set (Vertex C E w)) :
    Dominates (graph w left right) S ↔
      ∀ e i, Sum.inl (left e) ∉ S → Sum.inl (right e) ∉ S →
        Sum.inr (e, i) ∈ S := by
  have h := dominates_iff_forced left right hw hincident
    {c | Sum.inl c ∉ S} {j | Sum.inr j ∈ S}
  rw [selected_representation S] at h
  exact h

theorem vertex_count (C E : Type*) [Fintype C] [Fintype E] (w : ℕ) :
    Fintype.card (Vertex C E w) = Fintype.card C + Fintype.card E * w := by
  simp [Vertex]

#print axioms dominates_iff_forced
#print axioms all_controls_omitted
#print axioms dominates_iff_endpoints_or_clone
#print axioms vertex_count

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Supersets of a forced set correspond exactly to arbitrary subsets outside it. -/
def supersetsEquiv (J : Type*) (F : Set J) :
    {K : Set J // F ⊆ K} ≃ Set {j : J // j ∉ F} where
  toFun K := {j | j.val ∈ K.val}
  invFun T := ⟨{j | j ∈ F ∨ ∃ h : j ∉ F, (⟨j, h⟩ : {j // j ∉ F}) ∈ T},
    by intro j hj; exact Or.inl hj⟩
  left_inv K := by
    apply Subtype.ext
    ext j
    change (j ∈ F ∨ ∃ h : j ∉ F, j ∈ K.val) ↔ j ∈ K.val
    constructor
    · rintro (hj | ⟨_, hj⟩)
      · exact K.property hj
      · exact hj
    · intro hj
      by_cases h : j ∈ F
      · exact Or.inl h
      · exact Or.inr ⟨h, hj⟩
  right_inv T := by
    ext j
    change (j.val ∈ F ∨ ∃ h : j.val ∉ F, (⟨j.val, h⟩ : {j // j ∉ F}) ∈ T) ↔ j ∈ T
    constructor
    · rintro (hf | ⟨h, ht⟩)
      · exact (j.property hf).elim
      · exact ht
    · intro ht
      exact Or.inr ⟨j.property, ht⟩

theorem count_supersets (J : Type*) [Fintype J] (F : Set J) :
    Fintype.card {K : Set J // F ⊆ K} =
      2 ^ (Fintype.card J - Fintype.card F) := by
  rw [Fintype.card_congr (supersetsEquiv J F), Fintype.card_set,
    Fintype.card_subtype_compl]

/-- Indexed edges having both endpoints in the omitted control set. -/
def inducedEdges {C E : Type*} (left right : E → C) (P : Set C) : Set E :=
  {e | left e ∈ P ∧ right e ∈ P}

def forcedClones {C E : Type*} (w : ℕ) (left right : E → C) (P : Set C) :
    Set (E × Fin w) := {j | j.1 ∈ inducedEdges left right P}

def forcedClonesEquiv {C E : Type*} (w : ℕ) (left right : E → C) (P : Set C) :
    forcedClones w left right P ≃ (inducedEdges left right P × Fin w) where
  toFun j := (⟨j.val.1, j.property⟩, j.val.2)
  invFun j := ⟨(j.1.val, j.2), j.1.property⟩
  left_inv j := by cases j; rfl
  right_inv j := by cases j; rfl

theorem forcedClones_count {C E : Type*} [Fintype E]
    (w : ℕ) (left right : E → C) (P : Set C) :
    Fintype.card (forcedClones w left right P) =
      Fintype.card (inducedEdges left right P) * w := by
  rw [Fintype.card_congr (forcedClonesEquiv w left right P)]
  simp

theorem forcedIncluded_iff_subset {C E : Type*} {w : ℕ}
    (left right : E → C) (P : Set C) (K : Set (E × Fin w)) :
    ForcedIncluded left right P K ↔ forcedClones w left right P ⊆ K := by
  constructor
  · intro h j hj
    exact h j.1 j.2 hj.1 hj.2
  · intro h e i hl hr
    exact h (show (e, i) ∈ forcedClones w left right P from ⟨hl, hr⟩)

/-- Exact size of each omitted-control fiber of dominating sets. -/
theorem dominating_fiber_count {C E : Type*} [Fintype E] {w : ℕ}
    (left right : E → C) (hw : 0 < w)
    (hincident : ∀ c, ∃ e, c = left e ∨ c = right e) (P : Set C) :
    Fintype.card {K : Set (E × Fin w) //
      Dominates (graph w left right) (selected P K)} =
    2 ^ (Fintype.card E * w - Fintype.card (inducedEdges left right P) * w) := by
  have hp : (fun K : Set (E × Fin w) => Dominates (graph w left right) (selected P K)) =
      (fun K => forcedClones w left right P ⊆ K) := by
    funext K
    exact propext ((dominates_iff_forced left right hw hincident P K).trans
      (forcedIncluded_iff_subset left right P K))
  simp_rw [hp]
  rw [count_supersets, forcedClones_count]
  simp

#print axioms dominating_fiber_count
end
end Research.DominationIncidenceGraph

