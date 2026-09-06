import Mathlib

/-!
# Conditional algebraic obstructions for the Šoltés family analysis

This file verifies integer arithmetic used in `soltes_biregular_analysis.md`.
It does not formalize arc graphs, transmissions, deletion distances, apartments,
or the derivation of either deficit polynomial from a graph. In particular,
these lemmas are not a formal proof of the graph-family exclusion or a disproof
of any open conjecture.
-/

namespace SoltesFamilyObstruction

/-- An integer congruent to one modulo an integer at least two is nonzero. -/
theorem one_add_mul_ne_zero (q k : ℤ) (hq : 2 ≤ q) :
    1 + q * k ≠ 0 := by
  intro hzero
  by_cases hk : 0 ≤ k
  · have hprod : 0 ≤ q * k := mul_nonneg (by omega) hk
    omega
  · have hk' : k ≤ -1 := by omega
    have hprod : q * k ≤ q * (-1) :=
      mul_le_mul_of_nonneg_left hk' (by omega)
    nlinarith

/-- Conditional on the displayed factorization, two zero deficits force the
    two integer parameters to be equal. -/
theorem equal_parameters_of_zero_deficits
    (s t P deltaX deltaY : ℤ)
    (hP : 0 < P)
    (hfactor : deltaX - deltaY = 8 * (t - s) * P)
    (hx : deltaX = 0) (hy : deltaY = 0) : s = t := by
  have hzero : 8 * (t - s) * P = 0 := by
    simpa [hx, hy] using hfactor.symm
  have hfirst : 8 * (t - s) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hP)
  have hdiff : t - s = 0 :=
    (mul_eq_zero.mp hfirst).resolve_left (by norm_num)
  omega

/-- The quadrangle expression asserted by the separate distance analysis. -/
def quadrangleDeficit (q : ℤ) : ℤ :=
  9 * q ^ 4 - 14 * q ^ 3 - 30 * q ^ 2 - 14 * q + 1

/-- The hexagon expression asserted by the separate distance analysis. -/
def hexagonDeficit (q : ℤ) : ℤ :=
  13 * q ^ 6 - 30 * q ^ 5 - 78 * q ^ 4 - 94 * q ^ 3 -
    78 * q ^ 2 - 30 * q + 1

theorem quadrangle_factorization (q : ℤ) :
    quadrangleDeficit q = 1 + q * (9 * q ^ 3 - 14 * q ^ 2 - 30 * q - 14) := by
  unfold quadrangleDeficit
  ring

theorem hexagon_factorization (q : ℤ) :
    hexagonDeficit q =
      1 + q * (13 * q ^ 5 - 30 * q ^ 4 - 78 * q ^ 3 -
        94 * q ^ 2 - 78 * q - 30) := by
  unfold hexagonDeficit
  ring

theorem quadrangle_at_one : quadrangleDeficit 1 = -48 := by
  norm_num [quadrangleDeficit]

theorem hexagon_at_one : hexagonDeficit 1 = -296 := by
  norm_num [hexagonDeficit]

/-- The quadrangle polynomial has no positive integer root. -/
theorem quadrangle_no_positive_integer_root (q : ℤ) (hq : 0 < q) :
    quadrangleDeficit q ≠ 0 := by
  by_cases hqone : q = 1
  · subst q
    rw [quadrangle_at_one]
    norm_num
  · rw [quadrangle_factorization]
    exact one_add_mul_ne_zero q _ (by omega)

/-- The hexagon polynomial has no positive integer root. -/
theorem hexagon_no_positive_integer_root (q : ℤ) (hq : 0 < q) :
    hexagonDeficit q ≠ 0 := by
  by_cases hqone : q = 1
  · subst q
    rw [hexagon_at_one]
    norm_num
  · rw [hexagon_factorization]
    exact one_add_mul_ne_zero q _ (by omega)

end SoltesFamilyObstruction
