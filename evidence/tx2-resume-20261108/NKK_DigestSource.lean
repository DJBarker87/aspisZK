import NKK_Compare
import NJU_ResumeObserved
import NKK_LogAlgebra
import NKK_LogReduce
set_option autoImplicit false
noncomputable section
namespace NKK_DigestSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def source {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (chunks : Slice (Slice U8)) (stored : Slice U8)
 (next : NJU_Log.Run Event (core.result.Result T verifier.Error)) :
 NJU_Log.Run Event (core.result.Result T verifier.Error) := do
 let reply ← recordDigest d hash chunks
 let different ← CheckpointBytes4Ops.ne core.cmp.PartialEqU8 stored reply
 if different then pure (.Err .Checkpoint) else next

def model {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (chunks : Slice (Slice U8)) (stored : Slice U8)
 (next : NJU_Log.Run Event (core.result.Result T verifier.Error)) :
 NJU_Log.Run Event (core.result.Result T verifier.Error) := do
 let reply ← recordDigest d hash chunks
 if stored.val=reply.val then next else pure (.Err .Checkpoint)

/-- Returning and rejected branches of the native digest comparison use the
exact child reply and actual ordered chunk slices. Abort prefixes bind as-is. -/
theorem source_eq_model {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (chunks : Slice (Slice U8)) (stored : Slice U8)
 (next : NJU_Log.Run Event (core.result.Result T verifier.Error)) :
 source d hash chunks stored next=model d hash chunks stored next := by
 unfold source model
 apply NKK_LogAlgebra.bind_congr
 intro reply
 rw [NKK_Compare.ne_result]
 simp only [NKK_LogReduce.lift_ok_bind]
 by_cases same : stored.val=reply.val <;> simp [same]

#print axioms source_eq_model
end NKK_DigestSource
