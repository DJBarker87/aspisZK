import NLQ_TraceOfPacket
set_option autoImplicit false
noncomputable section
namespace NLQ_FirstMap
open Aeneas Aeneas.Std Result AspisR1 CheckpointBytes5Effect
/-- Mapper's COMPLETE outer Result is retained, including allocator/runtime
abort. The handler is an intermediate semantic boundary, not a row-root input. -/
def mapped {A E P : Type} (handler : E → Result P) : core.result.Result A E → Result (core.result.Result A P)
 | .Ok value => .ok (.Ok value)
 | .Err error => do let value ← handler error; ok (.Err value)
def continuation {A E P : Type} (handler : E → Result P) : core.result.Result A E → Code (core.result.Result A P)
 | .Ok value => .done (.Ok value)
 | .Err error => .step (handler error) (fun value => .done (.Err value))
def observed {A E P : Type} (handler : E → Result P)
 (child : NGP_L181.Observation (core.result.Result A E)) : NGP_L181.Observation (core.result.Result A P) :=
 ⟨child.result >>= mapped handler,child.attempted⟩
theorem mapper_cut {A E P : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (handler : E → Result P) (r : core.result.Result A E) :
 NHZ_DRIVER.Cuts hashv (continuation handler r) (mapped handler r) [] := by
 cases r with
 | Ok value => exact .leaf (.done (core.result.Result.Ok value))
 | Err error =>
   simp only [continuation,mapped]
   cases h : handler error with
   | ok value => exact .leaf (.stepOk _ _ value rfl _ _ (.done (core.result.Result.Err value)))
   | fail err => exact .leaf (.stepFail _ _ err rfl)
   | div => exact .leaf (.stepDiv _ _ rfl)
/-- SAME child observation and attempted events. This proves only the digest
and Result fold; it does not install a physical first_decoded parent cut or
replace the separately required error log/allocator frame certificate. -/
theorem fold {A E P : Type}
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (childCode : Code (core.result.Result A E)) (handler : E → Result P)
 (child : NGP_L181.Observation (core.result.Result A E))
 (associated : NGP_L181.NativeAssociation hashv childCode child) :
 NGP_L181.NativeAssociation hashv
  (CheckpointBytes5Effect.bind childCode (continuation handler)) (observed handler child) := by
 have head := NLQ_TraceOfPacket.child hashv childCode child associated
 apply NHZ_DRIVER.events_from_cuts hashv _ _ _ _ rfl
 cases h : child.result with
 | ok r =>
   have hc : NHZ_DRIVER.Cuts hashv childCode (.ok r) child.attempted := by simpa only [h] using head
   simpa only [observed,h,bind_tc_ok,List.append_nil] using
    (NHZ_DRIVER.Cuts.next hc (mapper_cut hashv handler r))
 | fail err =>
   have hc : NHZ_DRIVER.Cuts hashv childCode (.fail err) child.attempted := by simpa only [h] using head
   simpa only [observed,h,bind_tc_fail] using
    (NHZ_DRIVER.Cuts.fail hc (continuation handler))
 | div =>
   have hc : NHZ_DRIVER.Cuts hashv childCode .div child.attempted := by simpa only [h] using head
   simpa only [observed,h,bind_tc_div] using
    (NHZ_DRIVER.Cuts.div hc (continuation handler))
#check @fold
#print axioms mapper_cut
#print axioms fold
end NLQ_FirstMap
