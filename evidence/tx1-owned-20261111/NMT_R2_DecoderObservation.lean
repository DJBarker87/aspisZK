import NMT_R2_DecoderAllProjection
import NMT_R2_EmittedData
import NMT_R2_Observation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecoderObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_345Observation NMT_R2_Observation

def reference (bytes : Bytes) : RS Statement :=
 RS.seq (RS.lift (Spec.allocIf (NMT_R2_DecoderInputs.firstAllocation bytes)))
  (RS.bind (RS.ofOption (NMT_R2_ConcreteS1.decode bytes) .invalidAccountData)
   (fun st => RS.seq (RS.lift Spec.alloc) (RS.pure st)))

def run (internal outer : Bool) (bytes : Slice U8) : Obs (Except ProgramError Statement) :=
 tryObs (allocationIf (NMT_R2_DecoderInputs.firstAllocation (bytes.val.map byte)) internal) fun _ =>
 tryObs (NMT_R2_EmittedData.observe id (decodeCall bytes)) fun st =>
 tryObs (allocation outer) fun _ => silent (.ok st)

theorem value_valid (bytes : Slice U8) (env : Env) :
 RS.ofOption (NMT_R2_ConcreteS1.decode (bytes.val.map byte)) .invalidAccountData env
  (NMT_R2_EmittedData.observe id (decodeCall bytes)) := by
 rw [NMT_R2_DecoderAllProjection.source]
 cases NMT_R2_ConcreteS1.decode (bytes.val.map byte) <;> rfl

/-- Full decoder observation law: rejecting runs retain any reached internal
Box allocation, successful runs also pass the outer Box allocation. -/
theorem law (internal outer : Bool) (bytes : Slice U8) (env : Env) :
 reference (bytes.val.map byte) env (run internal outer bytes) := by
 apply try_valid _ _ _ _ env (allocationIf_valid _ _ env)
 intro _
 apply try_valid _ _ _ _ env (value_valid bytes env)
 intro st
 apply try_valid _ _ _ _ env (allocation_valid outer env)
 intro _
 rfl
#print axioms value_valid
#print axioms law
end NMT_R2_DecoderObservation
end
