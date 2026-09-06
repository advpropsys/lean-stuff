import Research.DominationGadgetGraph
import Research.DominationParameters
import Research.DominationPartition

/-! Dominating subsets and the soft error bound for the canonical projective split
graph. Phase estimates are proved in separate modules. -/
namespace Research.DominationCanonicalPartition

set_option maxRecDepth 1024

open Research.DominationGadgetGraph Research.DominationParameters
open Research.DominationIncidenceGraph

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev DomSet := {S : Set DominationGadgetGraph.Vertex // Dominates finalGraph S}

def D : ℕ := Fintype.card DomSet

def size (S : DomSet) : ℕ := Nat.card S.val

def IsHard (S : DomSet) : Prop :=
  DominationPartition.Hard left right (DominationPartition.omitted S.val)

abbrev HardDomSet := {S : DomSet // IsHard S}
abbrev NonhardDomSet := {S : DomSet // ¬ IsHard S}
abbrev HardControlSet := {P : Set Control // DominationPartition.Hard left right P}

def H : ℕ := Fintype.card HardControlSet

theorem D_pos : 0 < D := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨Set.univ, ?_⟩⟩
  intro v
  exact Or.inl (Set.mem_univ _)

theorem D_real_pos : (0 : ℝ) < D := by exact_mod_cast D_pos

theorem size_le_n (S : DomSet) : size S ≤ n := by
  have h : Fintype.card S.val ≤ Fintype.card DominationGadgetGraph.Vertex :=
    Fintype.card_subtype_le _
  change Nat.card S.val ≤ n
  rw [Nat.card_eq_fintype_card]
  simpa only [final_vertex_card] using h

def sizeIndex (S : DomSet) : Fin (n + 1) := ⟨size S, Nat.lt_succ_of_le (size_le_n S)⟩

/-- The coefficient counts dominating vertex subsets of each size. -/
def coefficient (k : Fin (n + 1)) : ℕ := Fintype.card {S : DomSet // size S = k.val}

theorem hard_count : Fintype.card HardDomSet = H * 2 ^ L := by
  unfold HardDomSet IsHard DomSet
  rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun S : Set DominationGadgetGraph.Vertex => Dominates finalGraph S)
    (fun S => DominationPartition.Hard left right (DominationPartition.omitted S)))]
  have h := DominationPartition.hard_dominating_count left right
    (show 0 < w by norm_num [w]) no_isolated_controls
  have he : Fintype.card Edge * w = L := by
    rw [edge_card]
    change m * w = w * m
    exact Nat.mul_comm _ _
  rw [he] at h
  have hh : Fintype.card {P : Set Control // DominationPartition.Hard left right P} = H := rfl
  rw [hh] at h
  exact h

theorem nonhard_count : Fintype.card NonhardDomSet = D - Fintype.card HardDomSet := by
  have h := Fintype.card_subtype_compl IsHard
  have hd : Fintype.card DomSet = D := rfl
  have hn : Fintype.card {S : DomSet // ¬ IsHard S} = Fintype.card NonhardDomSet :=
    Fintype.card_congr (Equiv.refl _)
  have hh : Fintype.card {S : DomSet // IsHard S} = Fintype.card HardDomSet :=
    Fintype.card_congr (Equiv.refl _)
  rw [hn, hh] at h
  rw [hd] at h
  exact h

theorem hard_count_le_D : Fintype.card HardDomSet ≤ D :=
  Fintype.card_subtype_le _

/-- The finite soft error bound applied to the canonical graph gives an upper
bound on the fraction of non-hard dominating sets. -/
theorem nonhard_fraction_lt :
    (Fintype.card NonhardDomSet : ℝ) / D < 1 / (2 : ℝ) ^ 190 := by
  have hg := DominationPartition.nonhard_fraction_bound left right
    (show 0 < w by norm_num [w]) no_isolated_controls
  have hcard : Fintype.card NonhardDomSet =
      Fintype.card {S : Set DominationGadgetGraph.Vertex // Dominates finalGraph S ∧
        ¬ DominationPartition.Hard left right (DominationPartition.omitted S)} :=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun S : Set DominationGadgetGraph.Vertex => Dominates finalGraph S)
      (fun S => ¬ DominationPartition.Hard left right (DominationPartition.omitted S)))
  rw [hcard]
  have hs := soft_error_bound
  have hbound :
      (Fintype.card {S : Set DominationGadgetGraph.Vertex // Dominates finalGraph S ∧
        ¬ DominationPartition.Hard left right (DominationPartition.omitted S)} : ℝ) / D ≤
        (1 + 1 / (2 : ℝ) ^ 256) ^ t - 1 := by
    simpa only [D, DomSet, finalGraph, control_card, w, one_div] using hg
  exact lt_of_le_of_lt hbound hs

end
end Research.DominationCanonicalPartition

#print axioms Research.DominationCanonicalPartition.D_pos
#print axioms Research.DominationCanonicalPartition.hard_count
#print axioms Research.DominationCanonicalPartition.nonhard_fraction_lt
