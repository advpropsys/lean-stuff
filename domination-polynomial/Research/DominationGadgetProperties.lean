import Research.DominationGadgetGraph

namespace Research.DominationGadgetGraph
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
set_option synthInstance.maxSize 1024

/-- The controls induce a complete graph in the final split graph. -/
theorem final_controls_clique (c d : Control) :
    finalGraph.Adj (.inl c) (.inl d) ↔ c ≠ d := Iff.rfl

/-- The clone vertices induce an empty graph. -/
theorem final_clones_independent (e f : Edge) (i j : Fin DominationParameters.w) :
    ¬ finalGraph.Adj (.inr (e,i)) (.inr (f,j)) := by
  exact id

/-- Each clone has precisely its two distinct control neighbors. -/
theorem final_clone_neighbors (e : Edge) (i : Fin DominationParameters.w) (v : Vertex) :
    finalGraph.Adj (.inr (e,i)) v ↔ v = .inl (left e) ∨ v = .inl (right e) := by
  cases v with
  | inl c => simp [finalGraph, DominationIncidenceGraph.graph,
      DominationIncidenceGraph.adjacent]
  | inr j => simp [finalGraph, DominationIncidenceGraph.graph,
      DominationIncidenceGraph.adjacent]

theorem final_connected : finalGraph.Connected := by
  have hcontrols (c d : Control) : finalGraph.Reachable (.inl c) (.inl d) := by
    by_cases h : c = d
    · subst d; exact SimpleGraph.Reachable.rfl
    · exact (show finalGraph.Adj (.inl c) (.inl d) from h).reachable
  have hattach (v : Vertex) : ∃ c : Control, finalGraph.Reachable v (.inl c) := by
    cases v with
    | inl c => exact ⟨c, SimpleGraph.Reachable.rfl⟩
    | inr j =>
      exact ⟨left j.1,
        (show finalGraph.Adj (.inr j) (.inl (left j.1)) from Or.inl rfl).reachable⟩
  letI : Nonempty Vertex := ⟨.inl (.inl (.inr (.inr ()),0))⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨c, hc⟩ := hattach u
  obtain ⟨d, hd⟩ := hattach v
  exact hc.trans ((hcontrols c d).trans hd.symm)

/-- Edge indices do not duplicate an unordered pair of controls. -/
theorem endpoint_pair_unique (e f : Edge)
    (h : (left e = left f ∧ right e = right f) ∨
      (left e = right f ∧ right e = left f)) : e = f := by
  rcases e with ⟨p,j⟩ | ⟨pr,i,j⟩ <;>
    rcases f with ⟨r,k⟩ | ⟨rs,k,l⟩
  · fin_cases j <;> fin_cases k <;> simp_all [left, right]
  · simp [left, right] at h
  · simp [left, right] at h
  · simp only [left, right, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, or_false] at h
    obtain ⟨⟨hp, hi⟩, hr, hj⟩ := h
    have hpr : pr = rs := by
      apply Subtype.ext
      exact Prod.ext hp hr
    subst rs
    subst k
    subst l
    rfl

#print axioms final_connected
#print axioms endpoint_pair_unique
end
end Research.DominationGadgetGraph
