-- PCVU_ items (1)+(2): deployed_tx2_common / deployed_tx2_authenticated with the Ext slots QM31::from_le_bytes, read_checkpoint_semantic_alpha
-- and read_checkpoint_weights instantiated by the FROZEN 4bb3b3f emission text (PCVU_E001, PCVU_E002; overflow ON), not by deployed fields.
-- Still deployed-field-instantiated: the other Ext fields (see PCVU_REMAINING.json). read_checkpoint_weights stays deployed here (PCVU_REMAINING.json).
import Aeneas
import PRVEq_Rd_s4
import PRVEq_Tx2Deployed_s1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVU_Tx2Frozen
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1 PCVN_Tx2Deployed PCVQ_Resumeq13 PCVQ_Tx2Deployedq5 PCVQ_Tx2Deployed6

/-- The deployed Ext with the three frozen slots. -/
def yFrozen (reserved : Bool) (d : VTop_Stages.Ops) : Ext :=
  { yDep reserved d with
    aspis_core_field_QM31_from_le_bytes := PCVU_Rd.fle0
    verifier_read_checkpoint_semantic_alpha := fun b a =>
      PCVU_Rd.PCVU_Fresh2.verifier.read_checkpoint_semantic_alpha PCVU_Rd.fle0 b a }

section
variable (reserved : Bool) (d : VTop_Stages.Ops)

theorem leavesF (hE : E32 d) : Leaves (xdep (yFrozen reserved d) d) (CheckpointBytes4Ops.ops reserved) where
  size := (leaves reserved d hE).size
  tag := (leaves reserved d hE).tag
  final := (leaves reserved d hE).final
  ne := fun {T U N} inst => (leaves reserved d hE).ne inst
  any := fun D it => (leaves reserved d hE).any D it
  raw := (leaves reserved d hE).raw
  k := fun {B} r K => PCVU_Rd.frk r K
  e := fun {B} r K => (leaves reserved d hE).e r K
  validate := fun {B} q K => (leaves reserved d hE).validate q K
  sem := fun {B} b a K => by
    show (PCVU_Rd.PCVU_Fresh2.verifier.read_checkpoint_semantic_alpha PCVU_Rd.fle0 b a >>= K) = _
    rw [PCVU_Rd.sem_eq]
    simp only [bind_assoc, bind_tc_ok]
    rfl
  weights := fun {B} b a w K => (leaves reserved d hE).weights b a w K
  zero := (leaves reserved d hE).zero
  filled := fun {H B} D n q K => (leaves reserved d hE).filled D n q K

theorem h18F (hE : E32 d) :
    @Port4A_ReaderInstall.reader reserved = @verifier.resume (xdep (yFrozen reserved d) d) := by
  funext H D ck proof pub v hash
  have hs := resume_sim (xdep (yFrozen reserved d) d) (CheckpointBytes4Ops.ops reserved) (leavesF reserved d hE)
    (fun v n h => Port4A_ReaderInstall.size_bound reserved v n h) D ck proof pub v hash
  unfold Sim at hs
  rw [hs]
  unfold Port4A_ReaderInstall.reader
  congr 1; funext out
  cases out <;> rfl
end

section
variable {F CE : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
  (geo : Port3_NativeGeometryBody.Ops CE) (base : VTop_Stages.Ops)
  (finish : AspisR1Stage2.Stage2Finish.FinishOps F)

theorem h18F_deployed :
    @(Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish).op18 =
      @verifier.resume (xdep (yFrozen reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)) := by
  rw [slot_op18]
  exact h18F reserved _ (PCVS_Tx2Deployed.e32_deployed reserved query geo base finish)

theorem deployed_tx2_common_t
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_common
        (xdep (yFrozen reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
          (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_common (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)
        inst public_bytes proof checkpoint hash obs :=
  deployed_tx2_common NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish _
    (h18F_deployed reserved query geo base finish) inst public_bytes proof checkpoint hash obs

theorem deployed_tx2_authenticated_t
    {H : Type} (inst : aspis_core.digest.Digest32 H) (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    verifier.candidate.tx2_authenticated
        (xdep (yFrozen reserved (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
          (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish))
        inst public_bytes proof checkpoint hash obs =
      VTop_Stages.verifier.candidate.tx2_authenticated (Dep NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish)
        inst public_bytes proof checkpoint hash obs :=
  deployed_tx2_authenticated NJC_ClosedCalls.inactive NHV_ReleaseOps.mark reserved query geo base finish _
    (h18F_deployed reserved query geo base finish) inst public_bytes proof checkpoint hash obs
end

#print axioms leavesF
#print axioms h18F
#print axioms deployed_tx2_common_t
#print axioms deployed_tx2_authenticated_t
end PCVU_Tx2Frozen
