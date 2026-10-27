import R1Z.PV_Inv_MapSlots
import R1Z.PV_Inv_RawInvoke
set_option autoImplicit false
namespace R1Z.PV_Inv_MapReached
open PV_Inv_RawSlots PV_Inv_RawInvoke
variable {V V' W : Type} [Zero W] [DecidableEq W]

theorem reached_map (f : V → V') (s : Slots V W) :
    reached (PV_Inv_MapSlots.slots f s) = (reached s).map f := by
  unfold reached
  simp only [PV_Inv_MapSlots.slots,PV_Inv_MapSlots.entry]
  by_cases h0 : (s 0).weight=0 <;> by_cases h1 : (s 1).weight=0 <;> simp [h0,h1]

#print axioms reached_map
end R1Z.PV_Inv_MapReached
