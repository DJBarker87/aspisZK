import R1Z.PV_Src_NativeInput
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompilerPayload
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1

/-- The returned payload is not an argument to the source compiler. Merely
supplying it in Input cannot prove that this compiler returned it. -/
theorem run_update [ExternalLinear] [Records] (i : PV_Src_NativeInput.Input)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) :
    PV_Src_NativeInput.run {i with compiled := compiled} = PV_Src_NativeInput.run i := rfl

/-- Two successful same-source associations force the payloads to coincide;
this is deterministic execution, not an existence proof for either payload. -/
theorem unique [ExternalLinear] [Records] (i : PV_Src_NativeInput.Input)
    (a b : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (ha : PV_Src_NativeInput.run {i with compiled := a} = ok (.Ok a))
    (hb : PV_Src_NativeInput.run {i with compiled := b} = ok (.Ok b)) : a = b := by
  rw [run_update] at ha hb
  rw [ha] at hb
  exact core.result.Result.Ok.inj (Result.ok.inj hb)

#print axioms run_update
#print axioms unique
end R1Z.PV_RunJoin_CompilerPayload
