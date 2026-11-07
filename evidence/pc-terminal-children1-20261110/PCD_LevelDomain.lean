import PCD_LaneModel
set_option autoImplicit false
namespace PCD_LaneModel
open Aeneas.Std

theorem level_value (level : Nat) (bounded : level < 20) :
    (levelWord level).val = level := by
  change (BitVec.ofNat 32 level).toNat = level
  simp only [BitVec.toNat_ofNat]
  omega

theorem level_domain (level : Nat) (bounded : level < 20) :
    levelWord level < 20#u32 := by
  change (levelWord level).val < 20
  rw [level_value level bounded]
  exact bounded

theorem running_bound (level remaining : Nat) (invariant : level+remaining=20)
    (running : remaining ≠ 0) : level < 20 := by omega

theorem next_invariant (level remaining : Nat) (invariant : level+(remaining+1)=20) :
    (level+1)+remaining=20 := by omega

#print axioms level_value
#print axioms level_domain
#print axioms running_bound
#print axioms next_invariant
end PCD_LaneModel
