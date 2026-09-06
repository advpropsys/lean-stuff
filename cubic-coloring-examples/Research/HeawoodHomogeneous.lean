import Research.CubicHomogeneous

/-! Explicit Fano incidence graph coloring. This does not prove the general conjecture. -/
namespace Research.HeawoodHomogeneous
open Research.CubicHomogeneous

def neighbors : Fin 14 → Finset (Fin 14) :=
  ![{7,8,9}, {7,10,11}, {7,12,13}, {8,10,12}, {8,11,13},
    {9,10,13}, {9,11,12}, {0,1,2}, {0,3,4}, {0,5,6},
    {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}]

def Heawood : SimpleGraph (Fin 14) where
  Adj i j := j ∈ neighbors i ∧ i ∈ neighbors j
  symm := by intro i j h; exact h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel Heawood.Adj := by
  unfold Heawood
  infer_instance

def threeColoring : Fin 14 → Fin 3 :=
  ![0,0,2,0,2,1,0,1,1,2,2,1,1,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Heawood_cubic : ∀ v, Heawood.degree v = 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Heawood_three_colors : TwoHomogeneous Heawood threeColoring := by decide

def fanoLines : Fin 7 → Finset (Fin 7) :=
  ![{0,1,2}, {0,3,4}, {0,5,6}, {1,3,5}, {1,4,6}, {2,3,6}, {2,4,5}]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Fano_not_propertyB :
    ¬ ∃ c : Fin 7 → Fin 2, ∀ e, ((fanoLines e).image c).card = 2 := by
  decide +kernel

#print axioms Fano_not_propertyB
#print axioms Heawood_cubic
#print axioms Heawood_three_colors
end Research.HeawoodHomogeneous
