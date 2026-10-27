import JHj_MasterGuards
import JHj_CheckpointGuards
import JHj_LaneGuards
set_option autoImplicit false
namespace AspisR1.JHj_GuardNonVacuity
open Aeneas Aeneas.Std Result

/-- Local guard non-vacuity only. No decoder/native success is a conjunct. -/
theorem source :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHg_AccountValues.master.identity.pool (JHg_World.e2.snapshot 1 384 384).key=ok false ∧
    (JHg_AccountValues.master.initialized_lane_mask !=255#u8)=false ∧
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHg_AccountValues.checkpoint.master JHj_Seeds.key=ok false ∧
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHg_AccountValues.checkpoint.deployment_domain JHg_AccountValues.master.identity.deployment_domain=ok false ∧
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      JHg_AccountValues.lane.master JHj_Seeds.key=ok false ∧
    (JHg_AccountValues.lane.lane_id !=3#u8)=false :=
  ⟨JHj_MasterGuards.pool,JHj_MasterGuards.mask_matches,JHj_CheckpointGuards.master,
    JHj_CheckpointGuards.domain,JHj_LaneGuards.master,JHj_LaneGuards.lane⟩
#print axioms source
end AspisR1.JHj_GuardNonVacuity
