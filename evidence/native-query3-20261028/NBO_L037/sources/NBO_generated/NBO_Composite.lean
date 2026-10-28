import NBO_LoopAssociation
set_option autoImplicit false
noncomputable section
namespace NBO_Composite
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev State:=NBB_QueryTrace.State
/-- Actual post-query shape: rejection/failure/divergence has no fabricated
finish call. Success finishes the SAME pending rows into the SAME returned
weight destination; all other accumulator fields are retained. -/
def finishResult (query : Result State) : Result State := do
 let result ← query
 match result with
 | .Err error => ok (.Err error)
 | .Ok (a,b) => do
   let finished ← Port3_FlushInstall.flush b a.weights.deref
   ok (.Ok ({a with weights:=⟨finished.val,finished.property⟩},b))
def source (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (b : verifier.BatchedWeights) : Result State :=
 finishResult (verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g none geometry b 10#usize)
def reference (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (b : verifier.BatchedWeights) : Result State :=
 finishResult (AspisR1Stage2.verifier.candidate.query_loop (NBO_LoopAssociation.referenceCall ops)
   proof p a g none geometry b 10#usize)
/-- Complete query/residue/accumulation/finish Result association to a concrete
checked reference instance, on SAME actual constructor outputs. No query or
finish success, selected final state, or whole-output equality is a premise. -/
theorem association (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b)) :
 source ops proof p a g geometry b=reference ops proof p a g geometry b :=
 congrArg finishResult (NBO_LoopAssociation.from_constructors base reserved ops lower bindings
   proof p prepared g geometry domain a b initial pending)
/-- A successful actual query needs no additional finish-success hypothesis.
The SAME returned rows derive the full finished contents and all final fields. -/
theorem accepted (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
 (query : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g none geometry b 10#usize=ok (.Ok (out,bout))) :
 ∃ finished : verifier.Accumulator,
 source ops proof p a g geometry b=ok (.Ok (finished,bout)) ∧
 finished.weights.val=(bout.raw.val.take 64).map NBF_FinishTrace.value ∧
 finished.weights.val.length=64 ∧ finished.rhs=out.rhs ∧ finished.power=out.power ∧
 finished.next.val=10 ∧ bout.terms.val=10 ∧
 (∀ q ∈ finished.weights.val, Port3_FlushInstall.Canonical q) ∧
 NBO_TailDomain.WideCanonical finished.rhs ∧ NBF_PowerStep.Canonical finished.power := by
 have fields:=NBO_FieldSemantics.fields ops bindings
 obtain ⟨next,terms,weights,raw,progress⟩ := NBF_QueryLoop.from_constructors
   base reserved ops fields.power proof p g geometry prepared.rho a out b bout initial pending query
 have good:=NBO_QueryRhs.from_constructors base reserved ops lower fields proof p prepared
   g geometry domain a out b bout initial pending query
 obtain ⟨finished,run,len,contents,canonical⟩ := NBB_Finish.source bout out.weights.deref raw weights
 refine ⟨{out with weights:=⟨finished.val,finished.property⟩},?_,contents,len,rfl,rfl,next,terms,
   canonical,good.2,good.1.power⟩
 simp only [source,query,finishResult,bind_tc_ok,run]
#print axioms association
#print axioms accepted
end NBO_Composite
end
