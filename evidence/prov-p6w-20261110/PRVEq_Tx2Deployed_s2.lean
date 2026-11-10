-- PCVS_ items (2),(3): the deployed tx2 theorems with the externals tag, final_len, checkpoint_size and QM31::ZERO taken from the frozen 4bb3b3f emissions
-- (PCVS_E002, PCVS_E001) instead of the deployed CheckpointBytes4Ops values; the remaining yDep/op slots are unchanged deployed fields.
import Aeneas
import PRVEq_Tx2Deployed_s1
import PRVEq_CkptSmall_s4
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVS_Tx2Deployed2
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVN_Tx2Deployed PCVQ_Resumeq13 PCVQ_Tx2Deployedq5 PCVQ_Tx2Deployed6 PCVS_Ckpt

def yMix (reserved : Bool) (d : VTop_Stages.Ops) : Ext :=
  { yDep reserved d with
    transport_Variant_tag := fun v => PCVS_Fresh2.transport.Variant.tag (toF v)
    transport_Variant_final_len := fun v => PCVS_Fresh2.transport.Variant.final_len (toF v)
    verifier_checkpoint_size := fun v => PCVS_Fresh2.verifier.checkpoint_size (toF v)
    aspis_core_field_QM31_ZERO := ok ⟨⟨PCVS_Fresh.field.QM31.ZERO.c0.a, PCVS_Fresh.field.QM31.ZERO.c0.b⟩, ⟨PCVS_Fresh.field.QM31.ZERO.c1.a, PCVS_Fresh.field.QM31.ZERO.c1.b⟩⟩ }

theorem yMix_eq (reserved : Bool) (d : VTop_Stages.Ops) : yMix reserved d = yDep reserved d := by
  have h1 : (fun v => PCVS_Fresh2.transport.Variant.tag (toF v)) = (CheckpointBytes4Ops.ops reserved).tag := funext fun v => tag_eq v
  have h2 : (fun v => PCVS_Fresh2.transport.Variant.final_len (toF v)) = (CheckpointBytes4Ops.ops reserved).finalLen := funext fun v => final_len_eq v
  have h3 : (fun v => PCVS_Fresh2.verifier.checkpoint_size (toF v)) = (CheckpointBytes4Ops.ops reserved).checkpointSize := funext fun v => checkpoint_size_eq v
  have h4 := (zeroK_eq reserved).symm
  unfold yMix
  rw [h1, h2, h3, h4]
  rfl

section
variable {F CE : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

theorem deployed_tx2_common_m
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_common (xdep (yMix reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)) (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_common (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish) inst public_bytes proof checkpoint hash obs := by
  rw [yMix_eq]
  exact PCVS_Tx2Deployed.deployed_tx2_common_s reserved query geo base finish inst public_bytes proof checkpoint hash obs

theorem deployed_tx2_authenticated_m
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_authenticated (xdep (yMix reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)) (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_authenticated (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish) inst public_bytes proof checkpoint hash obs := by
  rw [yMix_eq]
  exact PCVS_Tx2Deployed.deployed_tx2_authenticated_s reserved query geo base finish inst public_bytes proof checkpoint hash obs
end

#print axioms yMix_eq
#print axioms deployed_tx2_common_m
#print axioms deployed_tx2_authenticated_m
end PCVS_Tx2Deployed2
