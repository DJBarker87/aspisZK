import PV_B3P_MaskPath132
namespace PV_B3P_MaskModel132
open PV_B3P_MaskShape132
set_option autoImplicit false

def valueUsed (r c : Nat) : Prop :=
  ((r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 8 ∨ r = 9 ∨ r = 12 ∨ r = 14) ∧ c ≤ 10) ∨
    (r = 6 ∧ c < 3) ∨ (r = 7 ∧ c < 2) ∨ (r = 10 ∧ c < 10)
def free (r c : Nat) : Prop :=
  if r < 912 then 13 ≤ r%16 else
    if r < 1008 then ¬ localUsed r c else ¬ valueUsed (r-1008) c
instance (r c : Nat) : Decidable (free r c) := by
  unfold free localUsed valueUsed
  infer_instance

def cells : List (Nat × Nat) :=
  (List.range 16).flatMap (fun c =>
    ((List.range 1024).filter (fun r => decide (free r c))).map (fun r => (r,c)))

theorem member_iff (r c : Nat) : (r,c) ∈ cells ↔ r < 1024 ∧ c < 16 ∧ free r c := by
  simp only [cells,List.mem_flatMap,List.mem_map,List.mem_filter,List.mem_range,decide_eq_true_eq]
  constructor
  · rintro ⟨c',hc,⟨r',⟨hr,hfree⟩,heq⟩⟩
    cases heq
    exact ⟨hr,hc,hfree⟩
  · rintro ⟨hr,hc,hfree⟩
    exact ⟨c,hc,r,⟨hr,hfree⟩,rfl⟩

theorem padding (r c : Nat) (hr : r < 912) : free r c ↔ 13 ≤ r%16 := by
  simp only [free,hr,↓reduceIte]

theorem path (r c : Nat) (lo : 912 ≤ r) (hi : r < 1008) :
    free r c ↔ ¬ pathUsed r c := by
  have hn : ¬ r < 912 := by omega
  simp only [free,hn,hi,↓reduceIte]
  exact not_congr (PV_B3P_MaskPath132.used_iff r c lo hi).symm

#print axioms member_iff
#print axioms padding
#print axioms path
end PV_B3P_MaskModel132
