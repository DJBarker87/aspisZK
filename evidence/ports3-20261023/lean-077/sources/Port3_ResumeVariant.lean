import Port3_NativePendingPrefix
import Port3_FinishControl

/-! The variant is derived from the SAME complete source resume return,
without a saved-state provenance or independent decoder run. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_ResumeVariant
open Aeneas Aeneas.Std Result AspisR1Stage2

theorem source_variant (ops : ResumeOps) {H : Type} (D : aspis_core.digest.Digest32 H)
    (ck proof pub : Slice U8) (variant : transport.Variant) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (accepted : verifier.resumeWithOps ops D ck proof pub variant hash=ok (.Ok (p,a))) :
    p.variant=variant := by
  unfold verifier.resumeWithOps at accepted
  repeat' first
  | (solve | cases accepted)
  | (obtain ⟨x, hx, accepted⟩ := Port3_FinishControl.bind_success _ _ _ accepted)
  | split at accepted
  all_goals
    have same := core.result.Result.Ok.inj (Result.ok.inj accepted)
    exact (congrArg (fun pair : verifier.Prepared × verifier.Accumulator => pair.1.variant) same).symm

theorem installed_variant (reserved : Bool) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (accepted : Port3_CheckpointInstall.reader reserved D ck proof pub .S2 hash=ok (.Ok (p,a))) :
    p.variant=.S2 := by
  exact source_variant (CheckpointBytes4Ops.ops reserved) (VTop_Checkpoint.digest D)
    ck proof pub .S2 hash p a
    (Port3_CheckpointInstall.reader_success reserved D ck proof pub .S2 hash p a accepted)

#print axioms source_variant
#print axioms installed_variant
end AspisR1.Port3_ResumeVariant
end
