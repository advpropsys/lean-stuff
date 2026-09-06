import Research.DominationGadgetGraph
import Research.DominationBitEncoding

/-! Exact identification of compatible four-state words with independent
subsets of the concrete control graph. -/
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

namespace Research.DominationGadgetStates

open DominationGadgetGraph DominationHardPhases DominationBitEncoding

def rightCode (s : Fin 4) (j : Fin 3) : Bool := decide (s.val = j.val + 1)

theorem rightCode_injective : Function.Injective rightCode := by decide

theorem twoBits_nonzero (s : Fin 4) : s ≠ 0 ↔ ∃ i, twoBits s i = true := by
  revert s
  decide

theorem rightCode_nonzero (s : Fin 4) : s ≠ 0 ↔ ∃ j, rightCode s j = true := by
  revert s
  decide

theorem rightCode_triangle (s : Fin 4) (j : Fin 3) :
    ¬ (rightCode s j = true ∧ rightCode s (j + 1) = true) := by
  revert s j
  decide

theorem rightCode_exists (v : Fin 3 → Bool)
    (hv : ∀ i j, v i = true → v j = true → i = j) :
    ∃ s, rightCode s = v := by
  revert v
  decide

def encoded (p : Config Cell) : Set Control
  | .inl (c,i) => twoBits (p.1 c) i = true
  | .inr (c,j) => rightCode (p.2 c) j = true

def EdgeFree (P : Set Control) : Prop :=
  ∀ e : Edge, ¬ (left e ∈ P ∧ right e ∈ P)

theorem encoded_free_iff (p : Config Cell) :
    EdgeFree (encoded p) ↔ Compatible DominationProjectiveGeometry.Inc p := by
  constructor
  · intro h c d hcd
    by_contra hn
    push Not at hn
    obtain ⟨i, hi⟩ := (twoBits_nonzero (p.1 c)).mp hn.1
    obtain ⟨j, hj⟩ := (rightCode_nonzero (p.2 d)).mp hn.2
    exact h (.inr (⟨(c,d),hcd⟩,i,j)) ⟨hi,hj⟩
  · intro h e
    rcases e with ⟨c,j⟩ | ⟨cd,i,j⟩
    · exact rightCode_triangle (p.2 c) j
    · rintro ⟨hl,hr⟩
      have hnl := (twoBits_nonzero (p.1 cd.val.1)).mpr ⟨i,hl⟩
      have hnr := (rightCode_nonzero (p.2 cd.val.2)).mpr ⟨j,hr⟩
      rcases h cd.val.1 cd.val.2 cd.property with hh | hh
      · exact hnl hh
      · exact hnr hh

theorem encoded_injective : Function.Injective encoded := by
  intro p r h
  apply Prod.ext
  · funext c
    apply twoBits.injective
    funext i
    have hi := Set.ext_iff.mp h (Sum.inl (c,i))
    change (twoBits (p.1 c) i = true ↔ twoBits (r.1 c) i = true) at hi
    exact Bool.eq_iff_iff.mpr hi
  · funext c
    apply rightCode_injective
    funext j
    have hj := Set.ext_iff.mp h (Sum.inr (c,j))
    change (rightCode (p.2 c) j = true ↔ rightCode (r.2 c) j = true) at hj
    exact Bool.eq_iff_iff.mpr hj

theorem right_members_equal (P : Set Control) (hP : EdgeFree P) (c : Cell)
    (i j : Fin 3) (hi : Sum.inr (c,i) ∈ P) (hj : Sum.inr (c,j) ∈ P) : i = j := by
  have h0 := hP (.inl (c,0))
  have h1 := hP (.inl (c,1))
  have h2 := hP (.inl (c,2))
  fin_cases i <;> fin_cases j <;> norm_num [left, right] at * <;> tauto

theorem encoded_surjective (P : Set Control) (hP : EdgeFree P) :
    ∃ p : Config Cell, Compatible DominationProjectiveGeometry.Inc p ∧ encoded p = P := by
  let vl (c : Cell) (i : Fin 2) := decide (Sum.inl (c,i) ∈ P)
  let vr (c : Cell) (j : Fin 3) := decide (Sum.inr (c,j) ∈ P)
  have hr (c : Cell) : ∃ s, rightCode s = vr c := by
    apply rightCode_exists
    intro i j hi hj
    exact right_members_equal P hP c i j (by simpa [vr] using hi) (by simpa [vr] using hj)
  let p : Config Cell := (fun c => twoBits.symm (vl c), fun c => (hr c).choose)
  have hp : encoded p = P := by
    ext v
    rcases v with ⟨c,i⟩ | ⟨c,j⟩
    · change twoBits (twoBits.symm (vl c)) i = true ↔ _
      rw [twoBits.apply_symm_apply]
      simp [vl]
    · change rightCode ((hr c).choose) j = true ↔ _
      rw [(hr c).choose_spec]
      simp [vr]
  refine ⟨p, ?_, hp⟩
  apply (encoded_free_iff p).mp
  rwa [hp]

def hardEquiv :
    {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p} ≃
      {P : Set Control // EdgeFree P} :=
  Equiv.ofBijective
    (fun p => ⟨encoded p.val, (encoded_free_iff p.val).mpr p.property⟩)
    ⟨by
      intro p r h
      apply Subtype.ext
      exact encoded_injective (congrArg Subtype.val h), by
      intro P
      obtain ⟨p,hp,he⟩ := encoded_surjective P.val P.property
      exact ⟨⟨p,hp⟩, Subtype.ext he⟩⟩

theorem hard_card_eq :
    Fintype.card {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p} =
      Fintype.card {P : Set Control // EdgeFree P} := Fintype.card_congr hardEquiv

theorem left_code_card (s : Fin 4) :
    Fintype.card {i : Fin 2 // twoBits s i = true} = leftSize s := by
  revert s
  decide

theorem right_code_card (s : Fin 4) :
    Fintype.card {j : Fin 3 // rightCode s j = true} = rightSize s := by
  revert s
  decide

theorem encoded_card (p : Config Cell) :
    Nat.card {v : Control // v ∈ encoded p} =
      (∑ c, leftSize (p.1 c)) + ∑ c, rightSize (p.2 c) := by
  rw [Nat.card_congr (Equiv.subtypeSum (p := fun v : Control => v ∈ encoded p)),
    Nat.card_sum]
  change Nat.card {ci : Cell × Fin 2 // twoBits (p.1 ci.1) ci.2 = true} +
    Nat.card {cj : Cell × Fin 3 // rightCode (p.2 cj.1) cj.2 = true} = _
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun c i => twoBits (p.1 c) i = true)),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun c j => rightCode (p.2 c) j = true))]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, left_code_card, right_code_card]

/-- The correspondence preserves arbitrary events of omitted control sets. -/
def hardEventEquiv (A : Set Control → Prop) :
    {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p ∧ A (encoded p)} ≃
      {P : Set Control // EdgeFree P ∧ A P} :=
  Equiv.ofBijective
    (fun p => ⟨encoded p.val, (encoded_free_iff p.val).mpr p.property.1, p.property.2⟩)
    ⟨by
      intro p r h
      apply Subtype.ext
      exact encoded_injective (congrArg Subtype.val h), by
      intro P
      obtain ⟨p,hp,he⟩ := encoded_surjective P.val P.property.1
      refine ⟨⟨p,hp,?_⟩,Subtype.ext he⟩
      rw [he]
      exact P.property.2⟩

theorem hard_event_count (A : Set Control → Prop) :
    Nat.card {P : Set Control // EdgeFree P ∧ A P} =
      Nat.card {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p ∧
        A (encoded p)} := (Nat.card_congr (hardEventEquiv A)).symm

/-- In particular, every omitted-size event has exactly its four-state count. -/
theorem hard_size_event_count (A : ℕ → Prop) :
    Nat.card {P : Set Control // EdgeFree P ∧ A (Nat.card P)} =
      Nat.card {p : Config Cell // Compatible DominationProjectiveGeometry.Inc p ∧
        A ((∑ c, leftSize (p.1 c)) + ∑ c, rightSize (p.2 c))} := by
  rw [hard_event_count (fun P => A (Nat.card P))]
  simp only [encoded_card]

#print axioms hard_card_eq
#print axioms encoded_free_iff
#print axioms encoded_card
#print axioms hard_size_event_count

end Research.DominationGadgetStates
