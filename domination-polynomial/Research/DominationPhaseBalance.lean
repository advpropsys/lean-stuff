import Mathlib

/-! Finite balance survives discarding a bounded exceptional set. -/
namespace Research.DominationPhaseBalance

theorem good_card_lower {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A C GA GC Bad : Finset Ω) (hdis : Disjoint A C) (heq : A.card = C.card)
    (hGA : GA ⊆ A) (hGC : GC ⊆ C)
    (hcover : ∀ x, x ∈ GA ∨ x ∈ GC ∨ x ∈ Bad) :
    Fintype.card Ω ≤ 2 * GA.card + 2 * Bad.card := by
  have hACover : A ⊆ GA ∪ Bad := by
    intro x hx
    rcases hcover x with hg | hg | hb
    · exact Finset.mem_union_left _ hg
    · exact (Finset.disjoint_left.mp hdis hx (hGC hg)).elim
    · exact Finset.mem_union_right _ hb
  have hA : A.card ≤ GA.card + Bad.card :=
    le_trans (Finset.card_le_card hACover) (Finset.card_union_le _ _)
  have hC : GC.card ≤ GA.card + Bad.card := by
    have hh := Finset.card_le_card hGC
    omega
  have hAll : (Finset.univ : Finset Ω) ⊆ (GA ∪ GC) ∪ Bad := by
    intro x _
    rcases hcover x with hg | hg | hb
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hg)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hg)
    · exact Finset.mem_union_right _ hb
  have hcount : Fintype.card Ω ≤ GA.card + GC.card + Bad.card := by
    calc
      Fintype.card Ω = (Finset.univ : Finset Ω).card := (Finset.card_univ).symm
      _ ≤ ((GA ∪ GC) ∪ Bad).card := Finset.card_le_card hAll
      _ ≤ (GA ∪ GC).card + Bad.card := Finset.card_union_le _ _
      _ ≤ GA.card + GC.card + Bad.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
  omega

theorem both_good_card_lower {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (A C GA GC Bad : Finset Ω) (hdis : Disjoint A C) (heq : A.card = C.card)
    (hGA : GA ⊆ A) (hGC : GC ⊆ C)
    (hcover : ∀ x, x ∈ GA ∨ x ∈ GC ∨ x ∈ Bad) :
    Fintype.card Ω ≤ 2 * GA.card + 2 * Bad.card ∧
      Fintype.card Ω ≤ 2 * GC.card + 2 * Bad.card := by
  constructor
  · exact good_card_lower A C GA GC Bad hdis heq hGA hGC hcover
  · apply good_card_lower C A GC GA Bad hdis.symm heq.symm hGC hGA
    intro x
    rcases hcover x with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem good_fraction_lower {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (A C GA GC Bad : Finset Ω) (hdis : Disjoint A C) (heq : A.card = C.card)
    (hGA : GA ⊆ A) (hGC : GC ⊆ C)
    (hcover : ∀ x, x ∈ GA ∨ x ∈ GC ∨ x ∈ Bad) :
    1 / 2 - (Bad.card : ℝ) / Fintype.card Ω ≤ (GA.card : ℝ) / Fintype.card Ω := by
  have h := good_card_lower A C GA GC Bad hdis heq hGA hGC hcover
  have hr : (Fintype.card Ω : ℝ) ≤ 2 * GA.card + 2 * Bad.card := by exact_mod_cast h
  have hp : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  apply (le_div_iff₀ hp).mpr
  field_simp
  nlinarith

#print axioms good_fraction_lower
end Research.DominationPhaseBalance
