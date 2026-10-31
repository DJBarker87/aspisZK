import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard237
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (limb pattern column : Nat) (hl : Emitted 16 limb) (hp : Emitted 14 pattern) (hc : column ∈ PV_B3Q_FrozenTables.columns) :
 limb < 16 ∧ pattern < 14 ∧ column < 16 := by
  exact ⟨hl.2,hp.2,PV_B3Q_FrozenTables.column_member_bound column hc⟩
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard237
