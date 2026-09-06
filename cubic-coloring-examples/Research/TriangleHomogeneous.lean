import Research.CubicHomogeneous

/-! A conditional structural lemma. It neither establishes existence of a proper
three-coloring nor proves the general cubic-graph conjecture. -/
namespace Research.TriangleHomogeneous
open Research.CubicHomogeneous

/-- A proper three-coloring is 2-homogeneous if every vertex has two adjacent
neighbors. This applies, in particular, when every vertex lies in a triangle.
The statement does not require regularity. -/
theorem twoHomogeneous_of_adjacent_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 3)
    (hproper : ∀ u v, G.Adj u v → c u ≠ c v)
    (htri : ∀ v, ∃ x y, G.Adj v x ∧ G.Adj v y ∧ G.Adj x y) :
    TwoHomogeneous G c := by
  classical
  refine ⟨hproper, ?_⟩
  intro v
  obtain ⟨x, y, hvx, hvy, hxy⟩ := htri v
  have hx : c x ∈ (G.neighborFinset v).image c :=
    Finset.mem_image.mpr ⟨x, by simpa using hvx, rfl⟩
  have hy : c y ∈ (G.neighborFinset v).image c :=
    Finset.mem_image.mpr ⟨y, by simpa using hvy, rfl⟩
  have hpair : ({c x, c y} : Finset (Fin 3)) ⊆ (G.neighborFinset v).image c := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hlo : 2 ≤ ((G.neighborFinset v).image c).card := by
    have hh := Finset.card_le_card hpair
    simpa [hproper x y hxy] using hh
  have hsub : (G.neighborFinset v).image c ⊆ Finset.univ.erase (c v) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_erase.mpr ⟨(hproper v w (by simpa using hw)).symm, Finset.mem_univ _⟩
  have hhi : ((G.neighborFinset v).image c).card ≤ 2 := by
    have hh := Finset.card_le_card hsub
    simpa using hh
  omega

#print axioms twoHomogeneous_of_adjacent_neighbors
end Research.TriangleHomogeneous
