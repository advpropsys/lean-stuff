import Research.DominationFiniteTails

open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

namespace Research.DominationHardPhases

abbrev Word (C : Type*) := C → Fin 4
abbrev Config (C : Type*) := Word C × Word C

def occupied {C : Type*} [Fintype C] (w : Word C) : Finset C :=
  univ.filter (fun i ↦ w i ≠ 0)

def Compatible {C : Type*} (B : C → C → Prop) (p : Config C) : Prop :=
  ∀ i j, B i j → p.1 i = 0 ∨ p.2 j = 0

def NoLargeRectangle {C : Type*} [Fintype C] (B : C → C → Prop) (k : ℕ) : Prop :=
  ∀ S T : Finset C, k ≤ S.card → k ≤ T.card → ∃ i ∈ S, ∃ j ∈ T, B i j

theorem compatible_swap {C : Type*} {B : C → C → Prop}
    (hB : ∀ i j, B i j → B j i) (p : Config C) :
    Compatible B p.swap ↔ Compatible B p := by
  constructor <;> intro h i j hij
  · exact (h j i (hB i j hij)).symm
  · exact (h j i (hB i j hij)).symm

theorem not_both_large {C : Type*} [Fintype C] {B : C → C → Prop}
    {k : ℕ} (hrect : NoLargeRectangle B k) (p : Config C)
    (hp : Compatible B p) :
    ¬ (k ≤ (occupied p.1).card ∧ k ≤ (occupied p.2).card) := by
  rintro ⟨hl, hr⟩
  obtain ⟨i, hi, j, hj, hij⟩ := hrect (occupied p.1) (occupied p.2) hl hr
  have hni : p.1 i ≠ 0 := (mem_filter.mp hi).2
  have hnj : p.2 j ≠ 0 := (mem_filter.mp hj).2
  rcases hp i j hij with h | h
  · exact hni h
  · exact hnj h

/-- Exact phase balance; the state labels are preserved by the swap. -/
theorem phase_card_eq {C : Type*} [Fintype C] {B : C → C → Prop}
    (hB : ∀ i j, B i j → B j i) (k : ℕ) :
    Fintype.card {p : Config C // Compatible B p ∧ k ≤ (occupied p.1).card} =
    Fintype.card {p : Config C // Compatible B p ∧ k ≤ (occupied p.2).card} := by
  apply Fintype.card_congr
  exact
    { toFun := fun p ↦ ⟨p.val.swap, (compatible_swap hB p.val).mpr p.property.1, p.property.2⟩
      invFun := fun p ↦ ⟨p.val.swap, (compatible_swap hB p.val).mpr p.property.1, p.property.2⟩
      left_inv := fun p ↦ Subtype.ext (Prod.swap_swap p.val)
      right_inv := fun p ↦ Subtype.ext (Prod.swap_swap p.val) }

/-- Restricting both words and requiring compatibility can only decrease the
product count. This is the counting injection used for exceptional phases. -/
theorem constrained_card_le_product {C : Type*} [Fintype C]
    (B : C → C → Prop) (P Q : Word C → Prop) :
    Fintype.card {p : Config C // Compatible B p ∧ P p.1 ∧ Q p.2} ≤
      Fintype.card {w : Word C // P w} * Fintype.card {w : Word C // Q w} := by
  let f : {p : Config C // Compatible B p ∧ P p.1 ∧ Q p.2} →
      {w : Word C // P w} × {w : Word C // Q w} :=
    fun p ↦ (⟨p.val.1, p.property.2.1⟩, ⟨p.val.2, p.property.2.2⟩)
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h)
  simpa using Fintype.card_le_of_injective f hf

theorem hard_card_lower {C : Type*} [Fintype C] (B : C → C → Prop) :
    4 ^ Fintype.card C ≤ Fintype.card {p : Config C // Compatible B p} := by
  let f : Word C → {p : Config C // Compatible B p} :=
    fun w ↦ ⟨(w, fun _ ↦ 0), by intro i j h; exact Or.inr rfl⟩
  have hf : Function.Injective f := by
    intro w v h
    exact congrArg (fun p ↦ p.val.1) h
  simpa [Word] using Fintype.card_le_of_injective f hf

theorem both_small_card_le {C : Type*} [Fintype C]
    (B : C → C → Prop) (k : ℕ) :
    Fintype.card {p : Config C // Compatible B p ∧
      (occupied p.1).card < k ∧ (occupied p.2).card < k} ≤
      (Fintype.card {w : Word C // (occupied w).card < k}) ^ 2 := by
  let f : {p : Config C // Compatible B p ∧
      (occupied p.1).card < k ∧ (occupied p.2).card < k} →
      {w : Word C // (occupied w).card < k} ×
      {w : Word C // (occupied w).card < k} :=
    fun p ↦ (⟨p.val.1, p.property.2.1⟩, ⟨p.val.2, p.property.2.2⟩)
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h)
  simpa [pow_two] using Fintype.card_le_of_injective f hf

/-- A bad left-majority configuration injects into an unrestricted bad left
word and a small right word. `P` may be the subset-size tail event. -/
theorem left_bad_card_le {C : Type*} [Fintype C] {B : C → C → Prop}
    {k : ℕ} (hrect : NoLargeRectangle B k) (P : Word C → Prop) :
    Fintype.card {p : Config C // Compatible B p ∧
      k ≤ (occupied p.1).card ∧ P p.1} ≤
      Fintype.card {w : Word C // P w} *
      Fintype.card {w : Word C // (occupied w).card < k} := by
  let f : {p : Config C // Compatible B p ∧ k ≤ (occupied p.1).card ∧ P p.1} →
      {w : Word C // P w} × {w : Word C // (occupied w).card < k} :=
    fun p ↦ (⟨p.val.1, p.property.2.2⟩, ⟨p.val.2, by
      have h := not_both_large hrect p.val p.property.1
      omega⟩)
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h)
  simpa using Fintype.card_le_of_injective f hf

def leftSize (s : Fin 4) : ℕ := if s = 0 then 0 else if s = 3 then 2 else 1
def rightSize (s : Fin 4) : ℕ := if s = 0 then 0 else 1

theorem right_bad_card_le {C : Type*} [Fintype C] {B : C → C → Prop}
    {k : ℕ} (hrect : NoLargeRectangle B k) (P : Word C → Prop) :
    Fintype.card {p : Config C // Compatible B p ∧
      k ≤ (occupied p.2).card ∧ P p.2} ≤
      Fintype.card {w : Word C // (occupied w).card < k} *
      Fintype.card {w : Word C // P w} := by
  let f : {p : Config C // Compatible B p ∧ k ≤ (occupied p.2).card ∧ P p.2} →
      {w : Word C // (occupied w).card < k} × {w : Word C // P w} :=
    fun p ↦ (⟨p.val.1, by
      have h := not_both_large hrect p.val p.property.1
      omega⟩, ⟨p.val.2, p.property.2.2⟩)
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z ↦ z.1.val) h) (congrArg (fun z ↦ z.2.val) h)
  simpa using Fintype.card_le_of_injective f hf

/-- Explicit support-label upper bound for minority words. This counts
support subsets and their three possible nonzero labels, with no assumed
binomial-distribution identity. -/
theorem small_words_support_bound {C : Type*} [Fintype C] (k : ℕ) :
    Fintype.card {w : Word C // (occupied w).card < k} ≤
      ∑ S : {S : Finset C // S.card < k}, 3 ^ S.val.card := by
  let T := Σ S : {S : Finset C // S.card < k}, S.val → Fin 3
  let f : {w : Word C // (occupied w).card < k} → T := fun w ↦
    ⟨⟨occupied w.val, w.property⟩, fun i ↦
      ⟨(w.val i.val).val - 1, by
        have hi : w.val i.val ≠ 0 := (mem_filter.mp i.property).2
        have hv := (w.val i.val).isLt
        have hn : (w.val i.val).val ≠ 0 := by intro hh; apply hi; exact Fin.ext hh
        omega⟩⟩
  let d : T → Word C := fun p i ↦
    if hi : i ∈ p.1.val then ⟨(p.2 ⟨i, hi⟩).val + 1, by have := (p.2 ⟨i, hi⟩).isLt; omega⟩ else 0
  have hd (w : {w : Word C // (occupied w).card < k}) : d (f w) = w.val := by
    funext i
    dsimp [d, f]
    split_ifs with hi
    · apply Fin.ext
      have hn : (w.val i).val ≠ 0 := by
        have hh : w.val i ≠ 0 := (mem_filter.mp hi).2
        intro hz
        apply hh
        exact Fin.ext hz
      simp only
      omega
    · have hh : w.val i = 0 := by simpa [occupied] using hi
      exact hh.symm
  have hf : Function.Injective f := by
    intro w v h
    apply Subtype.ext
    rw [← hd w, ← hd v, h]
  have h := Fintype.card_le_of_injective f hf
  simpa [T, Fintype.card_sigma] using h

theorem leftSize_le_two (s : Fin 4) : leftSize s ≤ 2 := by
  unfold leftSize
  split_ifs <;> norm_num

theorem rightSize_eq_indicator (s : Fin 4) : rightSize s = if s ≠ 0 then 1 else 0 := by
  by_cases h : s = 0 <;> simp [rightSize, h]

theorem support_sum_eq_binomial {C : Type*} [Fintype C] (k : ℕ) :
    (∑ S : {S : Finset C // S.card < k}, 3 ^ S.val.card) =
      ∑ i ∈ (range (Fintype.card C + 1)).filter (fun i ↦ i < k),
        (Fintype.card C).choose i * 3 ^ i := by
  rw [← sum_subtype (univ.filter (fun S : Finset C ↦ S.card < k)) (by simp)
    (fun S : Finset C ↦ (3 : ℕ) ^ S.card)]
  rw [sum_filter]
  change (∑ S ∈ (univ : Finset C).powerset, if S.card < k then 3 ^ S.card else 0) = _
  rw [sum_powerset]
  have hi (i : ℕ) : (∑ S ∈ powersetCard i (univ : Finset C),
      if S.card < k then (3 : ℕ) ^ S.card else 0) =
      (Fintype.card C).choose i * (if i < k then 3 ^ i else 0) := by
    simpa [nsmul_eq_mul] using sum_powersetCard i (univ : Finset C)
      (fun j ↦ if j < k then (3 : ℕ) ^ j else 0)
  simp_rw [hi]
  simp [sum_filter, mul_ite]

theorem small_words_binomial_bound {C : Type*} [Fintype C] (k : ℕ) :
    Fintype.card {w : Word C // (occupied w).card < k} ≤
      ∑ i ∈ (range (Fintype.card C + 1)).filter (fun i ↦ i < k),
        (Fintype.card C).choose i * 3 ^ i := by
  exact (small_words_support_bound k).trans_eq (support_sum_eq_binomial k)

/-- A flexible entropy bound for minority words. The cutoff hypothesis is
only an arithmetic relation between the integer cutoff and epsilon. -/
theorem small_words_entropy_bound {C : Type*} [Fintype C] (k : ℕ) (ε z : ℝ)
    (hz : 0 < z) (hz1 : z ≤ 1)
    (hcut : ∀ i : ℕ, i < k → (i : ℝ) ≤ ε * Fintype.card C) :
    (Fintype.card {w : Word C // (occupied w).card < k} : ℝ) ≤
      Real.exp ((Fintype.card C : ℝ) *
        (Real.log (1 + 3 * z) - ε * Real.log z)) := by
  have hnat := small_words_binomial_bound (C := C) k
  have hreal : (Fintype.card {w : Word C // (occupied w).card < k} : ℝ) ≤
      ∑ i ∈ (range (Fintype.card C + 1)).filter (fun i ↦ i < k),
        ((Fintype.card C).choose i : ℝ) * (3 : ℝ) ^ i := by
    exact_mod_cast hnat
  calc
    _ ≤ _ := hreal
    _ ≤ ∑ i ∈ (range (Fintype.card C + 1)).filter
        (fun i : ℕ ↦ (i : ℝ) ≤ ε * Fintype.card C),
        ((Fintype.card C).choose i : ℝ) * (3 : ℝ) ^ i := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact mem_filter.mpr ⟨(mem_filter.mp hi).1, hcut i (mem_filter.mp hi).2⟩
      · intro i _ _
        positivity
    _ ≤ _ := DominationConcentration.weighted_binomial_entropy
      (Fintype.card C) 3 z ε (by norm_num) hz hz1

end Research.DominationHardPhases

#print axioms Research.DominationHardPhases.phase_card_eq
#print axioms Research.DominationHardPhases.left_bad_card_le
#print axioms Research.DominationHardPhases.hard_card_lower
#print axioms Research.DominationHardPhases.small_words_entropy_bound
