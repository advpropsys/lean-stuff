import Research.DominationValley

/-! From exact finite size events to the coefficient sequence they count.
These reusable lemmas do not assume a probability-to-coefficient identity. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace Research.DominationCoefficientCounts

def coefficient {Ω I : Type*} (size : Ω → I) (i : I) : ℕ :=
  Nat.card {ω // size ω = i}

def eventFibers {Ω I : Type*} (size : Ω → I) (S : Finset I) :
    {ω // size ω ∈ S} ≃ Σ i : S, {ω // size ω = i.val} where
  toFun ω := ⟨⟨size ω.val, ω.property⟩, ⟨ω.val, rfl⟩⟩
  invFun p := ⟨p.2.val, by rw [p.2.property]; exact p.1.property⟩
  left_inv ω := rfl
  right_inv p := by
    rcases p with ⟨⟨i,hi⟩,⟨ω,hω⟩⟩
    dsimp at hω
    subst i
    rfl

theorem sum_coefficients {Ω I : Type*} [Fintype Ω]
    (size : Ω → I) (S : Finset I) :
    (∑ i ∈ S, coefficient size i) = Nat.card {ω // size ω ∈ S} := by
  rw [Nat.card_congr (eventFibers size S), Nat.card_sigma]
  exact (Finset.sum_coe_sort S (fun i => coefficient size i)).symm

theorem sum_coefficients_real {Ω I : Type*} [Fintype Ω]
    (size : Ω → I) (S : Finset I) :
    (∑ i ∈ S, (coefficient size i : ℝ)) = (Nat.card {ω // size ω ∈ S} : ℝ) := by
  exact_mod_cast sum_coefficients size S

/-- A normalized finite-event certificate gives ordinary coefficient
nonunimodality, with the sharper actual-interval cardinality thresholds. -/
theorem not_unimodal_of_event_counts {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {n : ℕ} (size : Ω → Fin (n + 1))
    (S T : Finset (Fin (n + 1))) (j : Fin (n + 1)) (a c : ℝ)
    (hS : ∀ i ∈ S, i < j) (hT : ∀ k ∈ T, j < k)
    (hA : a ≤ (Nat.card {ω // size ω ∈ S} : ℝ) / Nat.card Ω)
    (hB : a ≤ (Nat.card {ω // size ω ∈ T} : ℝ) / Nat.card Ω)
    (hsmall : (Nat.card {ω // size ω = j} : ℝ) / Nat.card Ω ≤ c)
    (hgapS : (S.card : ℝ) * c < a) (hgapT : (T.card : ℝ) * c < a) :
    ¬ DominationValley.Unimodal (coefficient size) := by
  have hN : (0 : ℝ) < Nat.card Ω := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  apply DominationValley.not_unimodal_of_interval_mass_card
    (coefficient size) S T j (a * Nat.card Ω) (c * Nat.card Ω) hS hT
  · rw [sum_coefficients_real]
    exact (le_div_iff₀ hN).mp hA
  · rw [sum_coefficients_real]
    exact (le_div_iff₀ hN).mp hB
  · exact (div_le_iff₀ hN).mp hsmall
  · nlinarith [mul_lt_mul_of_pos_right hgapS hN]
  · nlinarith [mul_lt_mul_of_pos_right hgapT hN]

#print axioms sum_coefficients
#print axioms not_unimodal_of_event_counts

end Research.DominationCoefficientCounts
