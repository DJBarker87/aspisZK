import BEf_Count
import BEf_Batches
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEf_BatchEffects
open Aeneas Aeneas.Std Result SdkC_Source

theorem current (hashv : Parts → Result Digest)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : AspisR1CurrentCaller.verifier.Prepared)
    (root : Array U8 32#usize) (count : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call hashv)
      (SdkC_BatchSource.currentCode hashv proof p root) count before =
      (Op5T_Install.currentBatch Port4B_Install.leaves D proof p root 0#usize (),
       count + (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p root) []).2.length,
       before ++ (SdkC_Source.run hashv (SdkC_BatchSource.currentCode hashv proof p root) []).2) := by
  rw [BEf_Count.exact,SdkC_BatchSource.current_source hashv D source proof p root []]

theorem stage (hashv : Parts → Result Digest)
    (D : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (source : ∀ parts, D.digest () parts = hashv parts)
    (proof : Slice U8) (p : VTop_Stages.verifier.Prepared)
    (root : Array U8 32#usize) (count : Nat) (before : Log) :
    BEf_Carrier.run (BEf_Count.call hashv)
      (SdkC_BatchSource.stageCode hashv proof p root) count before =
      (Op5T_Install.stageBatch Port4B_Install.leaves D proof p root 1#usize (),
       count + (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv proof p root) []).2.length,
       before ++ (SdkC_Source.run hashv (SdkC_BatchSource.stageCode hashv proof p root) []).2) := by
  rw [BEf_Count.exact,SdkC_BatchSource.stage_source hashv D source proof p root []]

#print axioms current
#print axioms stage
end AspisR1.BEf_BatchEffects
end
