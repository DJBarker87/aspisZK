import NDO_JHj_CheckpointGuards
set_option autoImplicit false
namespace AspisR1.JHj_LaneGuards
open Aeneas Aeneas.Std Result

theorem master : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHg_AccountValues.lane.master JHj_Seeds.key=ok false := by
  have eq : JHg_AccountValues.lane.master=JHj_Seeds.key := by
    unfold JHj_Seeds.key JHg_World.e2
    rfl
  rw [eq]
  exact S2K.Equality.array_ne_self _ S2K.Equality.u8_ne_self _
#print axioms master

theorem lane : (JHg_AccountValues.lane.lane_id !=3#u8)=false := rfl
#print axioms lane
end AspisR1.JHj_LaneGuards
