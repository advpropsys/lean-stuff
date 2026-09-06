import Research.DominationProjectiveInstance
import Research.DominationIncidenceGraph

/-! The canonical control graph and the final edge-clone split graph.
The phase-distribution and coefficient-valley statements are separate. -/
set_option maxHeartbeats 200000
set_option synthInstance.maxSize 1024
namespace Research.DominationGadgetGraph

open DominationParameters DominationProjectiveGeometry
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Cell := DominationProjectiveInstance.Point
abbrev Control := (Cell × Fin 2) ⊕ (Cell × Fin 3)
abbrev Incidence := {pr : Cell × Cell // Inc pr.1 pr.2}
abbrev Edge := (Cell × Fin 3) ⊕ (Incidence × (Fin 2 × Fin 3))


def left : Edge → Control
  | .inl (p,j) => .inr (p,j)
  | .inr (pr,i,j) => .inl (pr.val.1,i)

def right : Edge → Control
  | .inl (p,j) => .inr (p,j+1)
  | .inr (pr,i,j) => .inr (pr.val.2,j)

theorem endpoints_distinct (e : Edge) : left e ≠ right e := by
  rcases e with ⟨p,j⟩ | ⟨pr,i,j⟩
  · fin_cases j <;> simp [left, right]
  · simp [left, right]

theorem control_card : Fintype.card Control = t := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin, DominationProjectiveInstance.point_card]
  unfold t
  ring

theorem incidence_card : Fintype.card Incidence = b * (q+1) := by
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun p r : Cell => Inc p r)),
    Fintype.card_sigma]
  simp_rw [incidence_degree, DominationProjectiveInstance.scalar_card]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    DominationProjectiveInstance.point_card]

theorem edge_card : Fintype.card Edge = m := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, DominationProjectiveInstance.point_card, incidence_card]
  norm_num only [Fintype.card_fin]
  unfold m
  ring

theorem cell_has_incidence (p : Cell) : ∃ r : Cell, Inc p r := by
  have hc : 0 < Fintype.card {r : Cell // Inc p r} := by
    rw [incidence_degree]
    omega
  obtain ⟨r⟩ := Fintype.card_pos_iff.mp hc
  exact ⟨r.val, r.property⟩

theorem no_isolated_controls (c : Control) : ∃ e : Edge, c = left e ∨ c = right e := by
  rcases c with ⟨p,i⟩ | ⟨p,j⟩
  · obtain ⟨r, hr⟩ := cell_has_incidence p
    exact ⟨.inr (⟨(p,r),hr⟩,i,0), Or.inl rfl⟩
  · exact ⟨.inl (p,j), Or.inl rfl⟩

/-- The ordinary simple control graph determined by the indexed edges. -/
def controlGraph : SimpleGraph Control where
  Adj u v := ∃ e : Edge, (u = left e ∧ v = right e) ∨
    (u = right e ∧ v = left e)
  symm := by
    rintro u v ⟨e, (⟨hu,hv⟩ | ⟨hu,hv⟩)⟩
    · exact ⟨e, Or.inr ⟨hv,hu⟩⟩
    · exact ⟨e, Or.inl ⟨hv,hu⟩⟩
  loopless := ⟨by
    rintro u ⟨e, (⟨hu,hv⟩ | ⟨hu,hv⟩)⟩
    · exact endpoints_distinct e (hu.symm.trans hv)
    · exact endpoints_distinct e (hv.symm.trans hu)⟩

theorem controlGraph_no_isolates (c : Control) : ∃ d, controlGraph.Adj c d := by
  obtain ⟨e, h | h⟩ := no_isolated_controls c
  · exact ⟨right e, e, Or.inl ⟨h,rfl⟩⟩
  · exact ⟨left e, e, Or.inr ⟨h,rfl⟩⟩

/-- Label-based independence is exactly ordinary graph independence. -/
theorem independent_iff (P : Set Control) :
    (∀ u ∈ P, ∀ v ∈ P, ¬ controlGraph.Adj u v) ↔
    ∀ e : Edge, ¬ (left e ∈ P ∧ right e ∈ P) := by
  constructor
  · intro h e he
    exact h (left e) he.1 (right e) he.2 ⟨e, Or.inl ⟨rfl,rfl⟩⟩
  · rintro h u hu v hv ⟨e, (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    · exact h e ⟨hu,hv⟩
    · exact h e ⟨hv,hu⟩

abbrev Vertex := DominationIncidenceGraph.Vertex Control Edge w

instance : Fintype Vertex := inferInstanceAs (Fintype (Control ⊕ (Edge × Fin w)))

def finalGraph : SimpleGraph Vertex := DominationIncidenceGraph.graph w left right

theorem final_vertex_card : Fintype.card Vertex = n := by
  have hc : Nat.card Control = t := by
    simpa only [Fintype.card_eq_nat_card] using control_card
  have he : Nat.card Edge = m := by
    simpa only [Fintype.card_eq_nat_card] using edge_card
  rw [Fintype.card_eq_nat_card]
  change Nat.card (Control ⊕ (Edge × Fin w)) = n
  rw [Nat.card_sum, Nat.card_prod, Nat.card_fin, hc, he]
  simp only [n, L, Nat.mul_comm]

/-- The canonical final graph inherits the exact domination characterization. -/
theorem final_dominates_iff (S : Set Vertex) :
    DominationIncidenceGraph.Dominates finalGraph S ↔
    ∀ e i, Sum.inl (left e) ∉ S → Sum.inl (right e) ∉ S →
      Sum.inr (e,i) ∈ S :=
  DominationIncidenceGraph.dominates_iff_endpoints_or_clone left right
    (by norm_num [w]) no_isolated_controls S

#print axioms edge_card
#print axioms final_vertex_card
#print axioms final_dominates_iff
end
end Research.DominationGadgetGraph
