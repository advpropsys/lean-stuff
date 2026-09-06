import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic
import Mathlib.LinearAlgebra.CrossProduct
import Research.DominationExpansion

/-! Concrete normalized projective-plane coordinates over a finite field.
No projective-plane existence axiom is used. -/
namespace Research.DominationProjectiveGeometry

abbrev Point (F : Type*) := (F × F) ⊕ (F ⊕ Unit)

def coord {F : Type*} [Field F] : Point F → Fin 3 → F
  | .inl (a,b) => ![1,a,b]
  | .inr (.inl a) => ![0,1,a]
  | .inr (.inr _) => ![0,0,1]

theorem coord_ne_zero {F : Type*} [Field F] (p : Point F) : coord p ≠ 0 := by
  rcases p with ⟨a,b⟩ | (a | u)
  · intro h; have := congrFun h 0; simp [coord] at this
  · intro h; have := congrFun h 1; simp [coord] at this
  · intro h; have := congrFun h 2; simp [coord] at this

theorem point_count (F : Type*) [Fintype F] :
    Fintype.card (Point F) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  simp [Point, pow_two]; omega

/-- Symmetric point/polar-line incidence, allowing absolute points. -/
def Inc {F : Type*} [Field F] (p r : Point F) : Prop :=
  ∑ i : Fin 3, coord p i * coord r i = 0

theorem inc_symm {F : Type*} [Field F] (p r : Point F) : Inc p r ↔ Inc r p := by
  simp only [Inc, mul_comm]

/-- Every nonzero vector has a normalized representative in the finite point type. -/
theorem normalized_exists {F : Type*} [Field F] (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ (p : Point F) (s : F), s ≠ 0 ∧ v = s • coord p := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨.inr (.inr ()), v 2, h2, ?_⟩
      ext i
      fin_cases i <;> simp [coord, h0, h1]
    · refine ⟨.inr (.inl (v 2 / v 1)), v 1, h1, ?_⟩
      ext i
      fin_cases i <;> simp [coord, h0, mul_div_cancel₀ _ h1]
  · refine ⟨.inl (v 1 / v 0, v 2 / v 0), v 0, h0, ?_⟩
    ext i
    fin_cases i <;> simp [coord, mul_div_cancel₀ _ h0]

/-- Normalization does not identify two distinct projective points. -/
theorem normalized_unique {F : Type*} [Field F] (p r : Point F) (s : F)
    (h : coord p = s • coord r) : p = r := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  rcases p with ⟨a,b⟩ | (a | u) <;>
    rcases r with ⟨c,d⟩ | (c | v) <;>
    simp [coord] at h0 h1 h2 ⊢ <;> aesop

#print axioms normalized_exists
#print axioms normalized_unique
noncomputable section
attribute [local instance] Classical.propDecidable

private def equationRightEquiv {F : Type*} [Field F] (a b c : F) (hb : b ≠ 0) :
    {z : F × F // a * z.1 + b * z.2 = c} ≃ F where
  toFun z := z.val.1
  invFun x := ⟨(x, (c - a*x)/b), by field_simp; ring⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      apply (div_eq_iff hb).2
      have := z.property
      try dsimp at this
      linear_combination -this
  right_inv x := rfl

private theorem equation_right_count {F : Type*} [Field F] [Fintype F]
    (a b c : F) (hb : b ≠ 0) :
    Fintype.card {z : F × F // a*z.1 + b*z.2 = c} = Fintype.card F :=
  Fintype.card_congr (equationRightEquiv a b c hb)

private def equationLeftEquiv {F : Type*} [Field F] (a b c : F) (ha : a ≠ 0) :
    {z : F × F // a * z.1 + b * z.2 = c} ≃ F where
  toFun z := z.val.2
  invFun y := ⟨((c - b*y)/a, y), by field_simp; ring⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      apply (div_eq_iff ha).2
      have := z.property
      try dsimp at this
      linear_combination -this
    · rfl
  right_inv y := rfl

private theorem equation_left_count {F : Type*} [Field F] [Fintype F]
    (a b c : F) (ha : a ≠ 0) :
    Fintype.card {z : F × F // a*z.1 + b*z.2 = c} = Fintype.card F :=
  Fintype.card_congr (equationLeftEquiv a b c ha)

private theorem linear_count {F : Type*} [Field F] [Fintype F]
    (a c : F) (ha : a ≠ 0) :
    Fintype.card {x : F // a*x = c} = 1 := by
  have hp : (fun x : F => a*x = c) = (fun x => x = c/a) := by
    funext x
    apply propext
    constructor
    · intro h; apply (eq_div_iff ha).2; simpa [mul_comm] using h
    · intro h; rw [h]; field_simp
  simp_rw [hp]
  simp

/-- Every normalized point has exactly q+1 incident polar lines. -/
theorem incidence_degree {F : Type*} [Field F] [Fintype F] (p : Point F) :
    Fintype.card {r : Point F // Inc p r} = Fintype.card F + 1 := by
  rw [Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum,
    Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
  rcases p with ⟨a,b⟩ | (a | u)
  · simp only [Inc, coord, Fin.sum_univ_three]
    change Fintype.card {z : F × F // 1*1 + a*z.1 + b*z.2 = 0} +
      (Fintype.card {x : F // 1*0 + a*1 + b*x = 0} +
        Fintype.card {u : Unit // 1*0 + a*0 + b*1 = 0}) = _
    simp only [one_mul, mul_zero, mul_one, zero_add, add_zero]
    by_cases hb : b = 0
    · subst b
      by_cases ha : a = 0
      · subst a
        simp
      · simp only [zero_mul, add_zero]
        have he' : (fun z : F × F => 1 + a*z.1 = 0) =
            (fun z => a*z.1 + 0*z.2 = -1) := by funext z; apply propext; simp; constructor <;> intro h <;> linear_combination h
        simp_rw [he']
        rw [equation_left_count a 0 (-1) ha]
        simp [ha]
    · have he : (fun z : F × F => 1 + a*z.1 + b*z.2 = 0) =
          (fun z => a*z.1 + b*z.2 = -1) := by funext z; apply propext; constructor <;> intro h <;> linear_combination h
      have hl : (fun x : F => a + b*x = 0) = (fun x => b*x = -a) := by
        funext x; apply propext; constructor <;> intro h <;> linear_combination h
      simp_rw [he, hl]
      rw [equation_right_count a b (-1) hb, linear_count b (-a) hb]
      simp [hb]
  · simp only [Inc, coord, Fin.sum_univ_three]
    change Fintype.card {z : F × F // 0*1 + 1*z.1 + a*z.2 = 0} +
      (Fintype.card {x : F // 0*0 + 1*1 + a*x = 0} +
        Fintype.card {u : Unit // 0*0 + 1*0 + a*1 = 0}) = _
    simp only [zero_mul, zero_add, one_mul, mul_one, mul_zero, add_zero]
    have he : (fun z : F × F => z.1 + a*z.2 = 0) =
        (fun z => 1*z.1 + a*z.2 = 0) := by simp
    simp_rw [he]
    rw [equation_left_count 1 a 0 one_ne_zero]
    by_cases ha : a = 0
    · simp [ha]
    · have hl : (fun x : F => 1 + a*x = 0) = (fun x => a*x = -1) := by
        funext x; apply propext; constructor <;> intro h <;> linear_combination h
      simp_rw [hl]
      rw [linear_count a (-1) ha]
      simp [ha]
  · simp only [Inc, coord, Fin.sum_univ_three]
    change Fintype.card {z : F × F // 0*1 + 0*z.1 + 1*z.2 = 0} +
      (Fintype.card {x : F // 0*0 + 0*1 + 1*x = 0} +
        Fintype.card {u : Unit // 0*0 + 0*0 + 1*1 = 0}) = _
    simp only [zero_mul, zero_add, one_mul]
    have he : (fun z : F × F => z.2 = 0) =
        (fun z => 0*z.1 + 1*z.2 = 0) := by simp
    simp_rw [he]
    rw [equation_right_count 0 1 0 one_ne_zero]
    simp

/-- Distinct normalized representatives are linearly independent. -/
theorem coord_pair_independent {F : Type*} [Field F] (p r : Point F) (hpr : p ≠ r) :
    LinearIndependent F ![coord p, coord r] := by
  rw [LinearIndependent.pair_iff' (coord_ne_zero p)]
  intro a ha
  apply hpr
  exact (normalized_unique r p a ha.symm).symm

/-- Distinct points have a unique common incident polar line. -/
theorem common_neighbor_unique {F : Type*} [Field F] (p r : Point F) (hpr : p ≠ r) :
    ∃! z : Point F, Inc p z ∧ Inc r z := by
  let c := crossProduct (coord p) (coord r)
  have hc : c ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr
    (coord_pair_independent p r hpr)
  obtain ⟨z, s, hs, hcz⟩ := normalized_exists c hc
  have hpz : Inc p z := by
    have h := dot_self_cross (coord p) (coord r)
    change (∑ i, coord p i * c i) = 0 at h
    rw [hcz] at h
    have he : (∑ i, coord p i * (s • coord z) i) = s * (∑ i, coord p i * coord z i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [he] at h
    exact (mul_eq_zero.mp h).resolve_left hs
  have hrz : Inc r z := by
    have h := dot_cross_self (coord p) (coord r)
    change (∑ i, coord r i * c i) = 0 at h
    rw [hcz] at h
    have he : (∑ i, coord r i * (s • coord z) i) = s * (∑ i, coord r i * coord z i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [he] at h
    exact (mul_eq_zero.mp h).resolve_left hs
  refine ⟨z, ⟨hpz, hrz⟩, ?_⟩
  intro y hy
  obtain ⟨hpy, hry⟩ := hy
  have hcross : crossProduct c (coord y) = 0 := by
    have h := cross_cross_eq_smul_sub_smul (coord p) (coord r) (coord y)
    change crossProduct c (coord y) = _ at h
    change (∑ i, coord p i * coord y i) = 0 at hpy
    change (∑ i, coord r i * coord y i) = 0 at hry
    simpa only [dotProduct, hpy, hry, zero_smul, sub_self] using h
  have hnot : ¬ LinearIndependent F ![c, coord y] := by
    intro hi
    exact (crossProduct_ne_zero_iff_linearIndependent.mpr hi) hcross
  rw [LinearIndependent.pair_iff' hc] at hnot
  push Not at hnot
  obtain ⟨a, ha⟩ := hnot
  apply normalized_unique y z (a*s)
  rw [← ha, hcz, smul_smul]

theorem common_neighbor_count {F : Type*} [Field F] [Fintype F]
    (p r : Point F) (hpr : p ≠ r) :
    Fintype.card {z : Point F // Inc p z ∧ Inc r z} = 1 := by
  obtain ⟨z, hz, hu⟩ := common_neighbor_unique p r hpr
  have he : (fun y : Point F => Inc p y ∧ Inc r y) = (fun y => y = z) := by
    funext y
    exact propext ⟨hu y, fun h => h ▸ hz⟩
  simp_rw [he]
  simp

/-- The concrete real 0/1 incidence matrix. -/
def incidenceMatrix {F : Type*} [Field F] (p r : Point F) : ℝ :=
  if Inc p r then 1 else 0

private theorem sum_indicator {J : Type*} [Fintype J] (P : J → Prop) :
    (∑ j, if P j then (1 : ℝ) else 0) = Fintype.card {j // P j} := by
  simp [Fintype.card_subtype]

theorem incidence_row_sum {F : Type*} [Field F] [Fintype F] (p : Point F) :
    (∑ r, incidenceMatrix p r) = (Fintype.card F : ℝ) + 1 := by
  unfold incidenceMatrix
  rw [sum_indicator, incidence_degree]
  norm_cast

theorem incidence_gram {F : Type*} [Field F] [Fintype F] (p r : Point F) :
    (∑ z, incidenceMatrix p z * incidenceMatrix r z) =
      if p = r then (Fintype.card F : ℝ) + 1 else 1 := by
  have he : (∑ z, incidenceMatrix p z * incidenceMatrix r z) =
      ∑ z, if Inc p z ∧ Inc r z then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro z hz
    unfold incidenceMatrix
    split_ifs <;> simp_all
  rw [he]
  trans (Fintype.card {z : Point F // Inc p z ∧ Inc r z} : ℝ)
  · simp [Fintype.card_subtype]
  by_cases h : p = r
  · subst r
    simp only [and_self]
    rw [incidence_degree]
    simp
  · rw [common_neighbor_count p r h]
    simp [h]

/-- Concrete finite-field projective planes satisfy the disperser estimate. -/
theorem incidence_between_large_sets {F : Type*} [Field F] [Fintype F]
    (S T : Finset (Point F)) (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : (Fintype.card F : ℝ) < ((Fintype.card F : ℝ) + 1)^2 * ε^2)
    (hS : ε * Fintype.card (Point F) ≤ S.card)
    (hT : ε * Fintype.card (Point F) ≤ T.card) :
    ∃ p ∈ S, ∃ r ∈ T, Inc p r := by
  have hbcard : (Fintype.card (Point F) : ℝ) =
      (Fintype.card F : ℝ)^2 + Fintype.card F + 1 := by
    exact_mod_cast point_count F
  have hb : 0 < (Fintype.card (Point F) : ℝ) := by
    rw [hbcard]
    positivity
  have hd : ((Fintype.card F : ℝ) + 1)^2 =
      (Fintype.card F : ℝ) + Fintype.card (Point F) := by
    rw [hbcard]
    ring
  obtain ⟨p, hp, r, hr, hn⟩ := DominationExpansion.exists_incidence_of_large_sets
    incidenceMatrix S T ((Fintype.card F : ℝ) + 1) (Fintype.card F : ℝ) ε
    (by positivity) hε hb hd incidence_row_sum incidence_gram hgap hS hT
  refine ⟨p, hp, r, hr, ?_⟩
  by_contra h
  exact hn (by simp [incidenceMatrix, h])

#print axioms incidence_between_large_sets
#print axioms incidence_gram
#print axioms common_neighbor_unique

#print axioms incidence_degree
end
end Research.DominationProjectiveGeometry

