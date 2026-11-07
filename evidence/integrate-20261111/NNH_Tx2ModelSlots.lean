import NNH_ModelConfig
import NGL_CheckpointModel
import LIBB_PoolLib
set_option autoImplicit false
noncomputable section
namespace NNH_Tx2ModelSlots
open Aeneas Aeneas.Std AdapterRw
/-- Pointwise source implementations used by the remaining TX2 model port.
These are source functions from the supplied libraries, not new library Values.
No total Missing or A2 is claimed by this partial adapter installation. -/
def install (base : Ops) (env : RSL.Env) : Ops :=
 {NGL_CheckpointModel.install (NNH_MRegistryOps.install (NNH_LaneModel.install base) LIB_Deployed.deployed env) with
  op9 := fun s=>.ok s.val.head?
  op16 := .ok 255#u8
  op17 := NMS_RequestModels.outputLane
  op20 := NMS_RequestModels.nullifier
  op51 := AspisR1.NFY_JHf_Scan.source
  op52 := AspisR1.NFY_JHf_ReconstructionSlot.source}

theorem selected (base : Ops) (env : RSL.Env) :
 (install base env).op16=.ok 255#u8 ∧
 (install base env).op51=AspisR1.NFY_JHf_Scan.source ∧
 (install base env).op52=AspisR1.NFY_JHf_ReconstructionSlot.source := ⟨rfl,rfl,rfl⟩
#print axioms selected
end NNH_Tx2ModelSlots
