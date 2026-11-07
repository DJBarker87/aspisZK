import NMT_R2_DecoderObservation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_DecoderInstall
open Aeneas Aeneas.Std NMT_345 RSL NMT_345Observation NMT_R2_Observation

/-- Concrete std allocation interpretation of CLOSED332. No field or outcome
is supplied as a premise. The first-site predicate's emitted-prefix proof is
recorded separately; this definition alone is not that proof. -/
def native (internal outer : Bool) (bytes : Slice U8) : Result (core.result.Result Statement PE) :=
 if NMT_R2_DecoderInputs.firstAllocation (bytes.val.map byte) && !internal then .fail .panic else do
 let r ← decodeCall bytes
 match r with
 | .Err e => .ok (.Err e)
 | .Ok st => if outer then .ok (.Ok st) else .fail .panic

theorem observation (internal outer : Bool) (bytes : Slice U8) :
 NMT_R2_EmittedData.observe id (native internal outer bytes) =
 NMT_R2_DecoderObservation.run internal outer bytes := by
 unfold native NMT_R2_DecoderObservation.run
 rw [NMT_R2_DecoderAllProjection.source]
 cases reach : NMT_R2_DecoderInputs.firstAllocation (bytes.val.map byte) <;>
  cases internal <;> cases outer <;>
  cases NMT_R2_ConcreteS1.decode (bytes.val.map byte) <;> rfl

theorem law (internal outer : Bool) (bytes : Slice U8) (env : Env) :
 NMT_R2_DecoderObservation.reference (bytes.val.map byte) env
  (NMT_R2_EmittedData.observe id (native internal outer bytes)) := by
 rw [observation]
 exact NMT_R2_DecoderObservation.law internal outer bytes env
#print axioms observation
#print axioms law
end NMT_R2_DecoderInstall
end
