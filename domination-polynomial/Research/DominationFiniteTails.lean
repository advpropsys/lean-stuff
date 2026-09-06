import Research.DominationConcentration

open MeasureTheory ProbabilityTheory Finset

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Research.DominationFiniteTails

theorem uniform_real_card {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (P : A → Prop) :
    (uniformOn (Set.univ : Set A)).real {x | P x} =
      (Fintype.card {x // P x} : ℝ) / Fintype.card A := by
  simp [Measure.real, uniformOn_univ, Measure.count_apply (Set.toFinite _).measurableSet,
    Set.encard, ENat.card_eq_coe_fintype_card, ENNReal.toReal_div]

theorem integral_uniform {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (g : A → ℝ) :
    (∫ x, g x ∂uniformOn (Set.univ : Set A)) =
      (∑ x, g x) / Fintype.card A := by
  simp [uniformOn, ProbabilityTheory.cond, integral_smul_measure, div_eq_mul_inv, mul_comm]

/-- Counting Hoeffding for a uniform word over any nonempty finite alphabet.
Every coordinate's observable is in [0,1]; its mean is computed explicitly
as an average over the alphabet. No independence assumption is left to the caller. -/
theorem alphabet_tail {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (g : A → ℝ) (hg : ∀ a, g a ∈ Set.Icc 0 1)
    (r : ℕ) (_hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {ω : Fin r → A //
      u ≤ |(∑ i, g (ω i)) - (r : ℝ) * ((∑ a, g a) / Fintype.card A)|} : ℝ) /
        (Fintype.card A : ℝ) ^ r ≤ 2 * Real.exp (-2 * u ^ 2 / r) := by
  let ν : Measure A := uniformOn Set.univ
  let μ : Measure (Fin r → A) := Measure.pi (fun _ ↦ ν)
  let p : ℝ := (∑ a, g a) / Fintype.card A
  let X : Fin r → (Fin r → A) → ℝ := fun i ω ↦ g (ω i) - p
  have hm : Measurable (fun a ↦ g a - p) := measurable_of_finite _
  have hind : iIndepFun X μ := iIndepFun_pi (fun _ ↦ hm.aemeasurable)
  have hμ : μ = uniformOn (Set.univ : Set (Fin r → A)) := by
    simpa [μ, ν] using (uniformOn_pi (f := fun _ : Fin r ↦ (Set.univ : Set A))).symm
  have hmeas : ∀ i ∈ (univ : Finset (Fin r)), AEMeasurable (X i) μ := by
    intro i _
    exact (hm.comp (measurable_pi_apply i)).aemeasurable
  have hbound : ∀ i ∈ (univ : Finset (Fin r)),
      ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-p) (-p + 1) := by
    intro i _
    exact ae_of_all _ (fun ω ↦ by have := hg (ω i); dsimp [X]; constructor <;> linarith [this.1, this.2])
  have hzero : ∀ i ∈ (univ : Finset (Fin r)), ∫ ω, X i ω ∂μ = 0 := by
    intro i _
    change (∫ ω, (fun a ↦ g a - p) (ω i) ∂Measure.pi (fun _ : Fin r ↦ ν)) = 0
    rw [integral_comp_eval (μ := fun _ : Fin r ↦ ν) (i := i)
      (f := fun a ↦ g a - p) hm.aestronglyMeasurable]
    rw [integral_sub Integrable.of_finite (integrable_const _)]
    simp [ν, integral_uniform, p]
  have h := DominationConcentration.bounded_sum_abs_tail hind univ (fun _ ↦ -p)
    hmeas hbound hzero hu
  have hsum (ω : Fin r → A) : (∑ i, X i ω) = (∑ i, g (ω i)) - (r : ℝ) * p := by
    simp [X, sum_sub_distrib]
  simp_rw [hsum] at h
  rw [hμ, uniform_real_card] at h
  simp only [card_univ, Fintype.card_fin, Fintype.card_fun, Nat.cast_pow] at h
  have he : -u ^ 2 / (2 * ((r : ℝ) / 4)) = -2 * u ^ 2 / r := by ring
  simpa [he, p] using h

/-- Binary words, with the number of true coordinates centered at r/2. -/
theorem binary_word_tail (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {ω : Fin r → Bool //
      u ≤ |(∑ i, if ω i then (1 : ℝ) else 0) - (r : ℝ) / 2|} : ℝ) /
      2 ^ r ≤ 2 * Real.exp (-2 * u ^ 2 / r) := by
  have h := alphabet_tail (A := Bool) (fun a ↦ if a then (1 : ℝ) else 0)
    (by intro a; cases a <;> norm_num) r hr u hu
  simpa [Fintype.sum_bool, div_eq_mul_inv] using h

/-- Four equiprobable states, three counted as nonempty, centered at 3r/4. -/
theorem four_state_tail (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {ω : Fin r → Fin 4 //
      u ≤ |(∑ i, if ω i = 0 then (0 : ℝ) else 1) - (3 : ℝ) * r / 4|} : ℝ) /
      4 ^ r ≤ 2 * Real.exp (-2 * u ^ 2 / r) := by
  have h := alphabet_tail (A := Fin 4) (fun a ↦ if a = 0 then (0 : ℝ) else 1)
    (by intro a; dsimp; split_ifs <;> norm_num) r hr u hu
  norm_num [Fin.sum_univ_succ] at h
  have he : (r : ℝ) * (3 / 4) = (3 : ℝ) * r / 4 := by ring
  simpa only [he, neg_mul] using h

def subsetWordEquiv (r : ℕ) : Finset (Fin r) ≃ (Fin r → Bool) where
  toFun S i := decide (i ∈ S)
  invFun ω := univ.filter (fun i ↦ ω i = true)
  left_inv S := by ext i; simp
  right_inv ω := by funext i; simp

theorem subset_word_sum (r : ℕ) (S : Finset (Fin r)) :
    (∑ i, if subsetWordEquiv r S i then (1 : ℝ) else 0) = (S.card : ℝ) := by
  simp [subsetWordEquiv]

/-- Hoeffding as an exact normalized count of subsets of Fin r. -/
theorem subset_tail (r : ℕ) (hr : 0 < r) (u : ℝ) (hu : 0 ≤ u) :
    (Fintype.card {S : Finset (Fin r) // u ≤ |(S.card : ℝ) - (r : ℝ) / 2|} : ℝ) /
      2 ^ r ≤ 2 * Real.exp (-2 * u ^ 2 / r) := by
  let e := subsetWordEquiv r
  let E : {S : Finset (Fin r) // u ≤ |(S.card : ℝ) - (r : ℝ) / 2|} ≃
      {ω : Fin r → Bool //
        u ≤ |(∑ i, if ω i then (1 : ℝ) else 0) - (r : ℝ) / 2|} :=
    { toFun := fun S ↦ ⟨e S, by
        change u ≤ |(∑ i, if subsetWordEquiv r S.val i then (1 : ℝ) else 0) - (r : ℝ) / 2|
        rw [subset_word_sum]
        exact S.property⟩
      invFun := fun ω ↦ ⟨e.symm ω, by
        have hh := subset_word_sum r (e.symm ω)
        change (∑ i, if e (e.symm ω) i then (1 : ℝ) else 0) = _ at hh
        rw [e.apply_symm_apply] at hh
        simpa only [hh] using ω.property⟩
      left_inv := fun S ↦ Subtype.ext (e.symm_apply_apply S)
      right_inv := fun ω ↦ Subtype.ext (e.apply_symm_apply ω) }
  rw [Fintype.card_congr E]
  exact binary_word_tail r hr u hu

end Research.DominationFiniteTails

#print axioms Research.DominationFiniteTails.alphabet_tail
#print axioms Research.DominationFiniteTails.subset_tail
#print axioms Research.DominationFiniteTails.four_state_tail
