import P6C_Pair
import SdkD_BatchFixed
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Batches
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def extended (hashv : Parts → Result Digest) (H : Bytes → State) : Parts → Result Digest :=
  fun parts => ok (P6C_Extension.total hashv H parts)

/-- Changing the dictionary also preserves the complete fixed batch syntax:
there are no digest calls hidden in its pure steps. -/
theorem current (hashv : Parts → Result Digest) (H : Bytes → State)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared) (root : Array U8 32#usize)
    (accepted : (run hashv (SdkC_BatchSource.currentCode hashv proof p root) []).1 = ok (.Ok ())) :
    run (extended hashv H) (SdkC_BatchSource.currentCode (extended hashv H) proof p root) [] =
      run hashv (SdkC_BatchSource.currentCode hashv proof p root) [] := by
  rw [SdkD_BatchFixed.current (extended hashv H) hashv]
  exact P6C_Extension.source_preserved hashv H _ [] (.Ok ()) accepted

theorem stage (hashv : Parts → Result Digest) (H : Bytes → State)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (accepted : (run hashv (SdkC_BatchSource.stageCode hashv proof p root) []).1 = ok (.Ok ())) :
    run (extended hashv H) (SdkC_BatchSource.stageCode (extended hashv H) proof p root) [] =
      run hashv (SdkC_BatchSource.stageCode hashv proof p root) [] := by
  rw [SdkD_BatchFixed.stage (extended hashv H) hashv]
  exact P6C_Extension.source_preserved hashv H _ [] (.Ok ()) accepted

/-- Source success transfers to the TOTAL mathematical stage dictionary on
exactly the same physical inputs, with no P6Boundary hypothesis. -/
theorem stage_native (hashv : Parts → Result Digest) (H : Bytes → State)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared) (root : Array U8 32#usize)
    (accepted : Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize () = ok (.Ok ())) :
    Op5T_Install.stageBatch Port4B_Install.leaves
      (SdkC_Source.dictionary (extended hashv H)) proof p root 1#usize () = ok (.Ok ()) := by
  have success := (SdkC_BatchSource.stage_source hashv D source proof p root []).trans accepted
  have same := congrArg Prod.fst (stage hashv H proof p root success)
  have totalSource := SdkC_BatchSource.stage_source (extended hashv H)
    (SdkC_Source.dictionary (extended hashv H)) (fun _ => rfl) proof p root []
  exact totalSource.symm.trans (same.trans success)

#print axioms current
#print axioms stage
#print axioms stage_native
end AspisR1.P6C_Batches
end
