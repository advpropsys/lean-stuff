import Mathlib.Tactic.NormNum

/-!
Exact integer certificates extending the alternating-Motzkin root inequality
to centers 6 through 9 and showing its failure at center 5.

For positive consecutive terms, the root inequality at center n is equivalent
to comparing aₙ^(2*(n-1)*(n+1)) and aₙ₋₁^(n*(n+1))*aₙ₊₁^(n*(n-1)).
The bridge to real logarithms is formalized separately.
-/

namespace Research.MotzkinFinite

theorem center6 :
    (14 : ℕ) ^ 42 * 90 ^ 30 < 37 ^ 70 := by norm_num

theorem center7 :
    (37 : ℕ) ^ 56 * 233 ^ 42 < 90 ^ 96 := by norm_num

theorem center8 :
    (90 : ℕ) ^ 72 * 602 ^ 56 < 233 ^ 126 := by norm_num

theorem center9 :
    (233 : ℕ) ^ 90 * 1586 ^ 72 < 602 ^ 160 := by norm_num

theorem center5_reverse :
    (14 : ℕ) ^ 48 < 7 ^ 30 * 37 ^ 20 := by norm_num

#print axioms center6
#print axioms center7
#print axioms center8
#print axioms center9
#print axioms center5_reverse

end Research.MotzkinFinite
