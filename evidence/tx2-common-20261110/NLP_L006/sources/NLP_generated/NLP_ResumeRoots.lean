import NKE_ResumeWidth
import CheckpointBytes4Layout
import Port3_BatchStage
set_option autoImplicit false
noncomputable section
namespace NLP_ResumeRoots
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
/-- This is a local inversion of a reached bind, never a root success premise.
The two Prepared roots are read from checkpoint, not from the proof slice. -/
theorem returned (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (entered : NJJ_Common.resume reservation d ck proof pub .S2 hash=ok (.Ok (p,a))) :
 (Port3_BatchStage.root0 p).val=(ck.val.drop 112).take 32 ∧
 (Port3_BatchStage.root1 p).val=(ck.val.drop 144).take 32 := by
 have size:=NKE_ResumeWidth.checkpoint reservation d ck proof pub hash p a entered
 unfold NJJ_Common.resume at entered
 rw [NJC_ResumeCalls.clause] at entered
 have same:=NKE_ResumeDomain.action_ok _ _ entered
 change AspisR1Stage2.verifier.resumeWithOps
  (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation))
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash=ok (.Ok (p,a)) at same
 obtain ⟨f⟩:=CheckpointBytes4Ops.successful_fields (NJC_FilledClause.reserved reservation)
  (NJC_ResumeCalls.digest d) ck proof pub .S2 hash p a same
 have flat:=CheckpointBytes4Layout.flat_fields (NJC_FilledClause.reserved reservation) ck p a f size
 constructor
 · simpa only [Port3_BatchStage.root0,f.roots,Array.make] using flat.root0Bytes
 · simpa only [Port3_BatchStage.root1,f.roots,Array.make] using flat.root1Bytes
#print returned
#print axioms returned
end NLP_ResumeRoots
