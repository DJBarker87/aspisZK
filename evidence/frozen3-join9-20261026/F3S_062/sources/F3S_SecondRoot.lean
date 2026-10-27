import F3S_SecondProvenance
import F3S_Silent
import F3S_Residual
import F3R_Try
import GExq_SecondCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_SecondRoot
open Aeneas Aeneas.Std Result CheckpointBytes5Effect VTop_Stages
local instance : MonadLift Result Code where monadLift := CheckpointBytes5Effect.liftResult
attribute [local irreducible] GExq_RetainedReader.code GExq_BatchSource.stage
 theorem split {Hash : Type} (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (pub proof checkpoint : Slice U8) (hash : Hash)
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_SecondCode.code base reserved hashv D pub proof checkpoint hash)=ok (.Ok ())) :
    ∃ (p : verifier.Prepared) (acc : verifier.Accumulator) (root : Array U8 32#usize),
      erase (SdkC_Source.dictionary hashv) () (GExq_RetainedReader.code reserved checkpoint proof pub .S2)=ok (.Ok (p,acc)) ∧
      erase (SdkC_Source.dictionary hashv) () (GExq_BatchSource.stage D hash proof p root)=ok (.Ok ()) ∧
      (∃ (off0 off1 : Usize) (view : Slice U8) (raw : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError),
        (GExq_SecondCode.installed base reserved).op15=ok off0 ∧
        (GExq_SecondCode.installed base reserved).op14=ok off1 ∧
        core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          proof {start:=off0,«end»:=off1}=ok view ∧
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok raw ∧
        (GExq_SecondCode.installed base reserved).unwrap32 raw=ok root) ∧
      SdkC_Source.readLog (SdkC_Source.run hashv
        (GExq_SecondCode.code base reserved hashv D pub proof checkpoint hash) []).2=
        SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved checkpoint proof pub .S2) []).2 ++
        SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.stage D hash proof p root) []).2 := by
  unfold GExq_SecondCode.code at success ⊢
  obtain ⟨shape,hs,s0,l0⟩ := F3R_SdkPure.right hashv _ _ _ success
  have logs := l0
  obtain ⟨cf,hcf,s1,l1⟩ := F3R_SdkPure.right hashv _ _ _ s0
  erw [l1] at logs
  cases cf with
  | Break residual =>
    cases residual with
    | Ok u => cases u
    | Err e => exact False.elim (F3S_Residual.impossible hashv e () s1)
  | Continue shaped =>
    obtain ⟨mark,hm,s2,l2⟩ := F3R_SdkPure.right hashv _ _ _ s1
    erw [l2] at logs
    obtain ⟨p,acc,root,reader,batch,provenance,commonLog⟩ :=
      F3S_SecondProvenance.split base reserved hashv D pub proof checkpoint hash s2
    erw [commonLog] at logs
    exact ⟨p,acc,root,reader,batch,provenance,logs⟩
#print axioms split
end AspisR1.F3S_SecondRoot
end
