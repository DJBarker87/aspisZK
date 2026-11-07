import NMT_R2_ReachLibrary
import NMT_R2_DecoderObservation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_ReachObservation
open Aeneas Aeneas.Std NMT_345 RSL NMT_345Observation NMT_R2_Observation

def reference (bytes : Bytes) : RS Statement :=
 RS.seq (RS.lift (Spec.allocIf (NMT_R2_ReachLibrary.reaches bytes)))
  (RS.bind (RS.ofOption (NMT_R2_ConcreteS1.decode bytes) .invalidAccountData)
   (fun st => RS.seq (RS.lift Spec.alloc) (RS.pure st)))

def run (internal outer : Bool) (bytes : Slice U8) : Obs (Except ProgramError Statement) :=
 tryObs (allocationIf (NMT_R2_Reach.reaches bytes) internal) fun _ =>
 tryObs (NMT_R2_EmittedData.observe id (decodeCall bytes)) fun st =>
 tryObs (allocation outer) fun _ => silent (.ok st)

theorem law (internal outer : Bool) (bytes : Slice U8) (env : Env) :
 reference (bytes.val.map byte) env (run internal outer bytes) := by
 unfold reference
 rw [NMT_R2_ReachLibrary.from_native]
 apply try_valid _ _ _ _ env (allocationIf_valid _ _ env)
 intro _
 apply try_valid _ _ _ _ env (NMT_R2_DecoderObservation.value_valid bytes env)
 intro st
 apply try_valid _ _ _ _ env (allocation_valid outer env)
 intro _
 rfl
#print axioms law
end NMT_R2_ReachObservation
end
