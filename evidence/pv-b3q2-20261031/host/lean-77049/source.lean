import PV_B3Q_LoopGuards
import PV_B3Q_TableGuards
namespace PV_B3Q_IndexGuard212
open Aeneas Aeneas.Std PV_B3Q_LoopGuards
set_option autoImplicit false
theorem dynamic_bounds (group output index : Nat) (hg : Emitted 4 group) (ho : Emitted 4 output) (hi : Emitted 16 index) :
 4*group < 16 ∧ 4*group+1 < 16 ∧ 4*group+2 < 16 ∧ 4*group+3 < 16 ∧ 4*group+output < 16 ∧ index < 16 := by
  have g := hg.2
  have o := ho.2
  have i := hi.2
  omega
#print axioms dynamic_bounds
end PV_B3Q_IndexGuard212
