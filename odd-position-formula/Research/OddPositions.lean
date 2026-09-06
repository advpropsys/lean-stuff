import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-!
# Kimberling's odd-position conjecture

An operational breadth-first construction with first-occurrence duplicate deletion.
Binary suffixes are stored least-significant-bit first; the leading 1 is implicit.
The numerical interpretation below connects the implementation to x ↦ x+2, 2*x.

Source: Clark Kimberling and Peter J. C. Moses, Fibonacci Quarterly
52(5) (2014), pp. 136–150, https://www.mathstat.dal.ca/FQ/Papers1/52-5/Kimberling.pdf .
Corollary 2.2 and equation (2.9) establish the Fibonacci layer sizes and
binary digit-weight characterization for the add-one/double tree.
The odd-position formula is a corollary of those results. This file includes
proofs of the layer sizes and digit-weight characterization.
-/

namespace Kimberling

abbrev Bits := List Bool

def bitValue : Bits → ℕ
  | [] => 1
  | false :: bs => 2 * bitValue bs
  | true :: bs => 2 * bitValue bs + 1

def weight : Bits → ℕ
  | [] => 0
  | false :: bs => weight bs + 1
  | true :: bs => weight bs + 2

def increment : Bits → Bits
  | [] => [false]
  | false :: bs => true :: bs
  | true :: bs => false :: increment bs

@[simp] theorem bitValue_pos (bs : Bits) : 0 < bitValue bs := by
  induction bs with
  | nil => simp [bitValue]
  | cons b bs ih =>
    cases b <;> simp only [bitValue] <;> omega

@[simp] theorem bitValue_increment (bs : Bits) :
    bitValue (increment bs) = bitValue bs + 1 := by
  induction bs with
  | nil => simp [increment, bitValue]
  | cons b bs ih =>
    cases b
    · simp [increment, bitValue]
    · simp only [increment, bitValue, ih]; omega

theorem weight_increment (bs : Bits) : weight (increment bs) ≤ weight bs + 1 := by
  induction bs with
  | nil => simp [increment, weight]
  | cons b bs ih =>
    cases b
    · simp [increment, weight]
    · simp only [increment, weight]; omega

theorem bitValue_injective : Function.Injective bitValue := by
  intro a
  induction a with
  | nil =>
    intro b h
    cases b with
    | nil => rfl
    | cons c bs =>
      have hp := bitValue_pos bs
      cases c <;> simp only [bitValue] at h <;> omega
  | cons c a ih =>
    intro b h
    cases b with
    | nil =>
      have hp := bitValue_pos a
      cases c <;> simp only [bitValue] at h <;> omega
    | cons d b =>
      cases c <;> cases d <;> simp only [bitValue] at h
      · have hab : bitValue a = bitValue b := by omega
        exact congrArg (false :: ·) (ih hab)
      · omega
      · omega
      · have hab : bitValue a = bitValue b := by omega
        exact congrArg (true :: ·) (ih hab)

/-- The binary representation of k+1, built without division. -/
def ofIndex : ℕ → Bits
  | 0 => []
  | k + 1 => increment (ofIndex k)

@[simp] theorem bitValue_ofIndex (k : ℕ) : bitValue (ofIndex k) = k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ofIndex, ih]

theorem weight_ofIndex (k : ℕ) : weight (ofIndex k) ≤ k := by
  induction k with
  | zero => simp [ofIndex, weight]
  | succ k ih =>
    have h := weight_increment (ofIndex k)
    simp only [ofIndex]
    omega

inductive Vertex
  | odd : ℕ → Vertex
  | even : Bits → Vertex
  deriving DecidableEq, Repr

open Vertex

def value : Vertex → ℕ
  | odd k => 2*k+1
  | even bs => 2*bitValue bs

def rank : Vertex → ℕ
  | odd k => k
  | even bs => weight bs

def addTwo : Vertex → Vertex
  | odd k => odd (k+1)
  | even bs => even (increment bs)

def twice : Vertex → Vertex
  | odd 0 => even []
  | odd (k+1) => even (true :: ofIndex k)
  | even bs => even (false :: bs)

@[simp] theorem value_pos (v : Vertex) : 0 < value v := by
  cases v with
  | odd k => simp [value]
  | even bs => simp [value]

theorem value_injective : Function.Injective value := by
  intro a b h
  cases a with
  | odd k => cases b with
    | odd l =>
      simp only [value] at h
      have hkl : k = l := by omega
      exact congrArg odd hkl
    | even bs => simp only [value] at h; omega
  | even bs => cases b with
    | odd k => simp only [value] at h; omega
    | even cs =>
      simp only [value] at h
      have hbc : bitValue bs = bitValue cs := by omega
      exact congrArg even (bitValue_injective hbc)

@[simp] theorem value_addTwo (v : Vertex) : value (addTwo v) = value v + 2 := by
  cases v <;> simp [addTwo, value] <;> omega

@[simp] theorem value_twice (v : Vertex) : value (twice v) = 2*value v := by
  cases v with
  | odd k => cases k <;> simp [twice, value, bitValue]
  | even bs => simp [twice, value, bitValue]

theorem rank_addTwo (v : Vertex) : rank (addTwo v) ≤ rank v + 1 := by
  cases v with
  | odd k => simp [addTwo, rank]
  | even bs => exact weight_increment bs

theorem rank_twice (v : Vertex) : rank (twice v) ≤ rank v + 1 := by
  cases v with
  | odd k => cases k with
    | zero => simp [twice, rank, weight]
    | succ k =>
      have := weight_ofIndex k
      simp only [twice, rank, weight]
      omega
  | even bs => simp [twice, rank, weight]

/-- Child order is part of the sequence definition. -/
def children (v : Vertex) : List Vertex := [addTwo v, twice v]

theorem rank_child {v w : Vertex} (h : w ∈ children v) : rank w ≤ rank v + 1 := by
  simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact rank_addTwo v
  · exact rank_twice v

/-- Every nonseed vertex has a parent in the immediately preceding rank. -/
theorem exists_parent {v : Vertex} {n : ℕ} (h : rank v = n+1) :
    ∃ u, rank u = n ∧ v ∈ children u := by
  cases v with
  | odd k =>
    simp only [rank] at h
    subst k
    exact ⟨odd n, rfl, by simp [children, addTwo]⟩
  | even bs =>
    cases bs with
    | nil => simp [rank, weight] at h
    | cons b bs =>
      cases b
      · refine ⟨even bs, ?_, ?_⟩
        · simp only [rank, weight] at h ⊢; omega
        · simp [children, twice]
      · refine ⟨even (false :: bs), ?_, ?_⟩
        · simp only [rank, weight] at h ⊢; omega
        · simp [children, addTwo, increment]

/-- Remove previous entries and repeated proposals, preserving the first occurrence. -/
def fresh {α : Type*} [DecidableEq α] (seen : List α) : List α → List α
  | [] => []
  | v :: vs => if v ∈ seen then fresh seen vs
      else v :: fresh (v :: seen) vs

@[simp] theorem mem_fresh {α : Type*} [DecidableEq α] {seen xs : List α} {v : α} :
    v ∈ fresh seen xs ↔ v ∈ xs ∧ v ∉ seen := by
  induction xs generalizing seen with
  | nil => simp [fresh]
  | cons x xs ih =>
    by_cases hx : x ∈ seen <;> by_cases hv : v = x <;>
      simp_all [fresh]

theorem nodup_fresh {α : Type*} [DecidableEq α] (seen xs : List α) : (fresh seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => simp [fresh]
  | cons x xs ih =>
    by_cases hx : x ∈ seen
    · simpa [fresh, hx] using ih seen
    · simp [fresh, hx, ih]

/-- (all entries generated, current generation), starting at generation zero. -/
def run : ℕ → List Vertex × List Vertex
  | 0 => ([odd 0, even []], [odd 0, even []])
  | n+1 =>
    let (seen, current) := run n
    let next := fresh seen (current.flatMap children)
    (seen ++ next, next)

def seen (n : ℕ) : List Vertex := (run n).1

def generation (n : ℕ) : List Vertex := (run n).2

@[simp] theorem seen_zero : seen 0 = [odd 0, even []] := rfl
@[simp] theorem generation_zero : generation 0 = [odd 0, even []] := rfl
@[simp] theorem generation_succ (n : ℕ) :
    generation (n+1) = fresh (seen n) ((generation n).flatMap children) := rfl
@[simp] theorem seen_succ (n : ℕ) :
    seen (n+1) = seen n ++ generation (n+1) := rfl

@[simp] theorem weight_eq_zero (bs : Bits) : weight bs = 0 ↔ bs = [] := by
  cases bs with
  | nil => simp [weight]
  | cons b bs => cases b <;> simp [weight]

/-- Characterization of each generation in the sequence construction. -/
theorem run_membership (n : ℕ) :
    (∀ v, v ∈ seen n ↔ rank v ≤ n) ∧
    (∀ v, v ∈ generation n ↔ rank v = n) := by
  induction n with
  | zero =>
    constructor <;> intro v <;> cases v <;> simp [rank]
  | succ n ih =>
    have hnext : ∀ v, v ∈ generation (n+1) ↔ rank v = n+1 := by
      intro v
      rw [generation_succ, mem_fresh, ih.1]
      constructor
      · rintro ⟨hv, hnot⟩
        obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp hv
        have hu' := (ih.2 u).mp hu
        have := rank_child hv
        omega
      · intro hv
        obtain ⟨u, hu, huv⟩ := exists_parent hv
        exact ⟨List.mem_flatMap.mpr ⟨u, (ih.2 u).mpr hu, huv⟩, by omega⟩
    refine ⟨?_, hnext⟩
    intro v
    rw [seen_succ, List.mem_append, ih.1, hnext]
    omega

theorem mem_generation (n : ℕ) (v : Vertex) :
    v ∈ generation n ↔ rank v = n := (run_membership n).2 v

theorem mem_seen (n : ℕ) (v : Vertex) :
    v ∈ seen n ↔ rank v ≤ n := (run_membership n).1 v

theorem nodup_generation (n : ℕ) : (generation n).Nodup := by
  cases n with
  | zero => simp
  | succ n => exact nodup_fresh _ _

/-- The unique odd member is first, with the exact proposal-order implementation. -/
theorem generation_starts_odd (n : ℕ) : ∃ rest, generation n = odd n :: rest := by
  induction n with
  | zero => exact ⟨[even []], rfl⟩
  | succ n ih =>
    obtain ⟨rest, hrest⟩ := ih
    have hn : odd (n+1) ∉ seen n := by simp [mem_seen, rank]
    simp only [generation_succ, hrest, List.flatMap_cons, children,
      List.cons_append, List.nil_append, addTwo, fresh, hn, ↓reduceIte]
    exact ⟨_, rfl⟩

/-- All binary suffixes of the given weight, each once. -/
def words : ℕ → List Bits
  | 0 => [[]]
  | 1 => [[false]]
  | n+2 => (words (n+1)).map (false :: ·) ++ (words n).map (true :: ·)

@[simp] theorem mem_words (n : ℕ) (bs : Bits) : bs ∈ words n ↔ weight bs = n := by
  induction n using Nat.twoStepInduction generalizing bs with
  | zero => simp [words]
  | one =>
    cases bs with
    | nil => simp [words, weight]
    | cons b bs => cases b <;> simp [words, weight]
  | more n ih0 ih1 =>
    cases bs with
    | nil => simp [words, weight]
    | cons b bs =>
      cases b <;> simp [words, ih0, ih1, weight]

theorem nodup_words (n : ℕ) : (words n).Nodup := by
  induction n using Nat.twoStepInduction with
  | zero => simp [words]
  | one => simp [words]
  | more n ih0 ih1 =>
    rw [words, List.nodup_append']
    refine ⟨ih1.map (by intro a b h; simpa using h),
      ih0.map (by intro a b h; simpa using h), ?_⟩
    simp [List.disjoint_left]

@[simp] theorem length_words (n : ℕ) : (words n).length = Nat.fib (n+1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [words]
  | one => simp [words]
  | more n ih0 ih1 =>
    simp only [words, List.length_append, List.length_map, ih0, ih1]
    have hf := @Nat.fib_add_two (n+1)
    norm_num only [Nat.add_assoc] at *
    omega

theorem generation_perm (n : ℕ) :
    (generation n).Perm (odd n :: (words n).map even) := by
  apply (List.perm_ext_iff_of_nodup (nodup_generation n) ?_).mpr
  · intro v
    cases v <;> simp [mem_generation, rank, eq_comm]
  · exact List.nodup_cons.mpr ⟨by simp,
      (nodup_words n).map (by intro a b h; exact Vertex.even.inj h)⟩

@[simp] theorem length_generation (n : ℕ) :
    (generation n).length = 1 + Nat.fib (n+1) := by
  have h := (generation_perm n).length_eq
  simpa [Nat.add_comm] using h

/-- Subtraction-free count of all entries through generation n. -/
theorem length_seen (n : ℕ) : (seen n).length + 1 = n+1+Nat.fib (n+3) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [seen_succ, List.length_append, length_generation]
    have hf := @Nat.fib_add_two (n+2)
    norm_num only [Nat.add_assoc] at *
    omega

/-- Zero-based index of the odd number 2n+1 in the operational prefix. -/
theorem odd_index (n : ℕ) : (seen n).idxOf (odd n) + 1 = n + Nat.fib (n+2) := by
  cases n with
  | zero => simp
  | succ n =>
    have hn : odd (n+1) ∉ seen n := by simp [mem_seen, rank]
    obtain ⟨rest, hrest⟩ := generation_starts_odd (n+1)
    rw [seen_succ, List.idxOf_append, if_neg hn, hrest]
    simp only [List.idxOf_cons_self, Nat.zero_add]
    exact length_seen n

/-- Injective relabeling commutes with the operational duplicate-deletion rule. -/
theorem fresh_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (previous xs : List α) :
    fresh (previous.map f) (xs.map f) = (fresh previous xs).map f := by
  induction xs generalizing previous with
  | nil => simp [fresh]
  | cons x xs ih =>
    have hm : f x ∈ previous.map f ↔ x ∈ previous := by
      simp only [List.mem_map, hf.eq_iff]
      simp
    by_cases hx : x ∈ previous
    · simp [fresh, hx, hm, ih]
    · simp [fresh, hx, hm]
      exact ih (x :: previous)

/-- The original integer-valued child proposals, in the specified order. -/
def numericChildren (x : ℕ) : List ℕ := [x+2, 2*x]

/-- Direct implementation on natural numbers of the original sequence. -/
def numericRun : ℕ → List ℕ × List ℕ
  | 0 => ([1,2], [1,2])
  | n+1 =>
    let (previous, current) := numericRun n
    let next := fresh previous (current.flatMap numericChildren)
    (previous ++ next, next)

theorem map_children (xs : List Vertex) :
    (xs.map value).flatMap numericChildren = (xs.flatMap children).map value := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, numericChildren, children, ih]

/-- The binary-state implementation is exactly the original numerical implementation. -/
theorem numericRun_eq (n : ℕ) :
    numericRun n = ((seen n).map value, (generation n).map value) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [numericRun, ih, map_children, fresh_map value value_injective,
      seen_succ, generation_succ, List.map_append]

theorem idxOf_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (xs : List α) (x : α) :
    (xs.map f).idxOf (f x) = xs.idxOf x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.map_cons, List.idxOf_cons, cond_eq_ite, beq_iff_eq, hf.eq_iff, ih]

/-- The prefix through generation n, with generation zero equal to [1,2]. -/
def sequencePrefix (n : ℕ) : List ℕ := (numericRun n).1

/-- One-based position of 2n-1 in a prefix that contains it (n ≥ 1). -/
def oddPosition (n : ℕ) : ℕ := (sequencePrefix (n-1)).idxOf (2*n-1) + 1

theorem odd_mem_prefix (n : ℕ) : 2*n+1 ∈ sequencePrefix n := by
  rw [sequencePrefix, numericRun_eq]
  change 2*n+1 ∈ (seen n).map value
  apply List.mem_map.mpr
  exact ⟨odd n, (mem_seen n (odd n)).mpr (by simp [rank]), rfl⟩

/-- Kimberling's conjectured one-based odd-position formula, for the original algorithm. -/
theorem oddPosition_formula (n : ℕ) (hn : 1 ≤ n) :
    oddPosition n = n-1 + Nat.fib (n+1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hx : 2*(k+1)-1 = value (odd k) := by simp only [value]; omega
  simp only [oddPosition, Nat.succ_eq_add_one, Nat.add_sub_cancel, sequencePrefix, numericRun_eq, hx]
  rw [idxOf_map_injective value value_injective, odd_index]

@[simp] theorem sequencePrefix_succ (N : ℕ) :
    sequencePrefix (N+1) = sequencePrefix N ++ (numericRun (N+1)).2 := rfl

/-- Every prefix from the indicated generation onward contains the target odd number. -/
theorem odd_mem_later_prefix (n N : ℕ) (hn : 1 ≤ n) (hN : n-1 ≤ N) :
    2*n-1 ∈ sequencePrefix N := by
  rw [sequencePrefix, numericRun_eq]
  apply List.mem_map.mpr
  refine ⟨odd (n-1), (mem_seen N (odd (n-1))).mpr hN, ?_⟩
  simp only [value]
  omega

/-- The one-based odd position is independent of which later finite prefix is used.
Thus this is a position theorem for the entire concatenated sequence. -/
theorem oddPosition_stable (n N : ℕ) (hn : 1 ≤ n) (hN : n-1 ≤ N) :
    (sequencePrefix N).idxOf (2*n-1) + 1 = n-1 + Nat.fib (n+1) := by
  induction N, hN using Nat.le_induction with
  | base => exact oddPosition_formula n hn
  | succ N hN ih =>
    rw [sequencePrefix_succ, List.idxOf_append,
      if_pos (odd_mem_later_prefix n N hn hN), ih]

#print axioms oddPosition_formula
#print axioms oddPosition_stable

end Kimberling
