import F3V_SecondSlots
import SdkD_SecondRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3V_SecondRun
open Aeneas Aeneas.Std Result

theorem accepted {F C Hash : Type} (c : DrvC_Installation.Configuration F C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof ck : Slice U8)
    (success : VTop_Stages.verifier.candidate.tx2_authenticated
      (GExp_SecondCode.installed (DrvC_Installation.stage c) c.reserved) D pub proof ck hash none=ok (.Ok ())) :
    ∃ (p : AspisR1Stage2.verifier.Prepared) (a : AspisR1Stage2.verifier.Accumulator)
      (root : Array U8 32#usize) (view : Slice U8),
      AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops c.reserved)
        (VTop_Checkpoint.digest D) ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root) ∧
      Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize hash=ok (.Ok ()) := by
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ D hash pub proof ck none success
  obtain ⟨p,a,root,view,read,range,copy,batch⟩ := SdkD_SecondCut.common _ D hash pub proof ck rfl rfl rfl common
  have source := Port4A_ReaderInstall.accepted_source c.stageBase c.reserved D hash ck proof pub .S2 p a read
  exact ⟨p,a,root,view,source,range,copy,batch⟩

#print axioms accepted
end AspisR1.F3V_SecondRun
end
