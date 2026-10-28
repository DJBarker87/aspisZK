import NBF_QueryLoop
import NBF_FinishTrace
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBO_FinishCaller
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Finish consumes the SAME query-produced raw state and SAME original
weight destination. Its entire Result is derived, with no finish-success
hypothesis and no independently selected destination contents. Native caller
association remains a separate obligation. -/
theorem from_query (base : VTop_Stages.Ops) (reserved : Bool)
 (ops : Ops) (field : NBF_PowerStep.NBC_Qm31Canonical ops)
 (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (rho : NBF_PowerStep.Canonical p.rho)
 (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
 (run : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g none geometry b 10#usize=ok (.Ok (out,bout))) :
 ∃ finished : Slice NBF_RowInstall.Q,
   Port3_FlushInstall.flush bout a.weights.deref=ok finished ∧
   finished.val.length=64 ∧
   finished.val=(bout.raw.val.take 64).map NBF_FinishTrace.value ∧
   (∀ q ∈ finished.val, Port3_FlushInstall.Canonical q) ∧
   out.next.val=10 ∧ bout.terms.val=10 ∧
   S7JoinRowsTrace.Progress 10 0 (Port3_RowsInstall.toBW bout) := by
 obtain ⟨next,terms,_,raw,progress⟩ := NBF_QueryLoop.from_constructors
   base reserved ops field proof p g geometry rho a out b bout initial pending run
 obtain ⟨_,good⟩ := NBF_QueryInitial.good base reserved a b initial pending
 obtain ⟨finished,hfinish,len,contents,canonical⟩ := NBB_Finish.source
   bout a.weights.deref raw good.weights
 exact ⟨finished,hfinish,len,contents,canonical,next,terms,progress⟩
#print axioms from_query
end NBO_FinishCaller
