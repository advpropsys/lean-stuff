import Mathlib

/-!
Finite empty-rectangle estimates from incidence moments. These statements do not
construct a projective plane or establish its incidence identities.
-/

namespace Research.DominationExpansion

/-- Centered second moments bound a set on which an incidence-count function
vanishes. This is the squared, division-free form of the required mixing bound. -/
theorem empty_rectangle_of_moments {Y : Type*} [Fintype Y]
    (f : Y → ℝ) (T : Finset Y) (s d q : ℝ)
    (hs : 0 ≤ s) (hq : 0 ≤ q)
    (hd : d ^ 2 = q + Fintype.card Y)
    (hfirst : (∑ y, f y) = d * s)
    (hsecond : (∑ y, (f y) ^ 2) = q * s + s ^ 2)
    (hzero : ∀ y ∈ T, f y = 0) :
    d ^ 2 * s * T.card ≤ q * (Fintype.card Y : ℝ) ^ 2 := by
  classical
  let b : ℝ := Fintype.card Y
  have hb : 0 ≤ b := by positivity
  have hcenter : (∑ y, (b * f y - d * s) ^ 2) =
      q * b ^ 2 * s - q * b * s ^ 2 := by
    calc
      (∑ y, (b * f y - d * s) ^ 2) =
          ∑ y, (b ^ 2 * (f y) ^ 2 - (2 * b * d * s) * f y + (d * s) ^ 2) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = b ^ 2 * (q * s + s ^ 2) - (2 * b * d * s) * (d * s) +
          b * (d * s) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hfirst, hsecond]
        simp [b]
      _ = b ^ 2 * (q * s + s ^ 2) - b * d ^ 2 * s ^ 2 := by ring
      _ = q * b ^ 2 * s - q * b * s ^ 2 := by
        rw [hd]
        dsimp [b]
        ring
  have hpart : (T.card : ℝ) * (d * s) ^ 2 ≤ ∑ y, (b * f y - d * s) ^ 2 := by
    calc
      (T.card : ℝ) * (d * s) ^ 2 = ∑ y ∈ T, (b * f y - d * s) ^ 2 := by
        calc
          _ = ∑ _y ∈ T, (d * s) ^ 2 := by simp
          _ = _ := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hzero y hy]
            ring
      _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun y => sq_nonneg _)
  rw [hcenter] at hpart
  by_cases hs0 : s = 0
  · simp only [hs0, mul_zero, zero_mul]
    positivity
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hnonneg : 0 ≤ q * b * s ^ 2 := by positivity
    have hmul : (d ^ 2 * s * T.card) * s ≤ (q * b ^ 2) * s := by
      nlinarith [hpart, hnonneg]
    exact le_of_mul_le_mul_right hmul hsp

/-- Double counting row incidences and pairwise common neighbors supplies the
moments. No symmetry hypothesis is needed once the row Gram identity is given. -/
theorem empty_rectangle_of_incidence {X Y : Type*} [DecidableEq X] [Fintype Y]
    (N : X → Y → ℝ) (S : Finset X) (T : Finset Y) (d q : ℝ)
    (hq : 0 ≤ q) (hd : d ^ 2 = q + Fintype.card Y)
    (hrow : ∀ x, (∑ y, N x y) = d)
    (hgram : ∀ x x', (∑ y, N x y * N x' y) =
      if x = x' then q + 1 else 1)
    (hempty : ∀ x ∈ S, ∀ y ∈ T, N x y = 0) :
    d ^ 2 * (S.card : ℝ) * T.card ≤ q * (Fintype.card Y : ℝ) ^ 2 := by
  classical
  let f : Y → ℝ := fun y => ∑ x ∈ S, N x y
  have hfirst : (∑ y, f y) = d * S.card := by
    dsimp [f]
    rw [Finset.sum_comm]
    simp [hrow, mul_comm]
  have hsecond : (∑ y, (f y) ^ 2) = q * S.card + (S.card : ℝ) ^ 2 := by
    calc
      (∑ y, (f y) ^ 2) = ∑ y, ∑ x ∈ S, ∑ x' ∈ S, N x y * N x' y := by
        apply Finset.sum_congr rfl
        intro y hy
        simpa [f, pow_two] using Finset.sum_mul_sum S S (fun x => N x y) (fun x => N x y)
      _ = ∑ x ∈ S, ∑ x' ∈ S, ∑ y, N x y * N x' y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_comm]
      _ = ∑ x ∈ S, ∑ x' ∈ S, (if x = x' then q + 1 else 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro x' hx'
        exact hgram x x'
      _ = ∑ x ∈ S, (q + (S.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        calc
          (∑ x' ∈ S, if x = x' then q + 1 else 1) =
              ∑ x' ∈ S, ((if x = x' then q else 0) + 1) := by
            apply Finset.sum_congr rfl
            intro x' hx'
            split_ifs <;> ring
          _ = q + S.card := by
            rw [Finset.sum_add_distrib]
            simp [hx]
      _ = q * S.card + (S.card : ℝ) ^ 2 := by
        simp
        ring
  apply empty_rectangle_of_moments f T (S.card : ℝ) d q (by positivity) hq hd hfirst hsecond
  intro y hy
  exact Finset.sum_eq_zero (fun x hx => hempty x hx y hy)

/-- The generic disperser consequence: two sufficiently large vertex sets
cannot form an empty incidence rectangle. -/
theorem exists_incidence_of_large_sets {X Y : Type*} [DecidableEq X] [Fintype Y]
    (N : X → Y → ℝ) (S : Finset X) (T : Finset Y) (d q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 ≤ ε) (hb : 0 < (Fintype.card Y : ℝ))
    (hd : d ^ 2 = q + Fintype.card Y)
    (hrow : ∀ x, (∑ y, N x y) = d)
    (hgram : ∀ x x', (∑ y, N x y * N x' y) =
      if x = x' then q + 1 else 1)
    (hgap : q < d ^ 2 * ε ^ 2)
    (hS : ε * Fintype.card Y ≤ S.card)
    (hT : ε * Fintype.card Y ≤ T.card) :
    ∃ x ∈ S, ∃ y ∈ T, N x y ≠ 0 := by
  classical
  by_contra hempty
  push Not at hempty
  have hbound := empty_rectangle_of_incidence N S T d q hq hd hrow hgram hempty
  have hprod : (ε * Fintype.card Y) * (ε * Fintype.card Y) ≤
      (S.card : ℝ) * T.card :=
    mul_le_mul hS hT (mul_nonneg hε (le_of_lt hb)) (by positivity)
  have hweighted := mul_le_mul_of_nonneg_left hprod (sq_nonneg d)
  have hstrict := mul_lt_mul_of_pos_right hgap (sq_pos_of_pos hb)
  nlinarith [hbound, hweighted, hstrict]

end Research.DominationExpansion

#print axioms Research.DominationExpansion.empty_rectangle_of_moments
#print axioms Research.DominationExpansion.empty_rectangle_of_incidence
#print axioms Research.DominationExpansion.exists_incidence_of_large_sets
