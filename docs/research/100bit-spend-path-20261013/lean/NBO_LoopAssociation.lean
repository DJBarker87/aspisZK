import NBO_QueryAssociation
import NBO_ProducerDomains
set_option autoImplicit false
noncomputable section
namespace NBO_LoopAssociation
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2 Port3_NativeQueryBody
abbrev sourceOps (ops : Ops) := NBO_QueryAssociation.sourceOps ops
def referenceCall (ops : Ops) : QueryCall :=
 AspisR1Stage2.verifier.candidate.queryWithOps (NBO_AccumulateAssociation.reference ops)
   (NBO_QueryAssociation.reference ops)
/-- Reuse the SAME chronological source history. Each local Result transfers
by the proved query_values association; its next caller domain is derived. -/
theorem transport (ops : Ops) (lower : NBO_QueryDomains.Lower ops)
 (bindings : NBO_FieldSemantics.NBC_Bindings ops) (proof : Slice U8)
 (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (state : NBB_QueryTrace.State) (out : Result NBB_QueryTrace.State)
 (history : NBB_QueryTrace.Trace (fun a b=>verifier.candidate.query_values
   (sourceOps ops) proof p a g none geometry b) 10 state out) :
 NBO_QueryRhs.StateGood state →
 NBB_QueryTrace.Trace (fun a b=>referenceCall ops proof p a g none geometry b) 10 state out := by
 have fields:=NBO_FieldSemantics.fields ops bindings
 have order : ∀ a : verifier.Accumulator, geometry.start.val≤a.next.val := by
   intro a;rw [domain.start];change 0≤a.next.val;omega
 induction history with
 | error e => intro good;exact .error e
 | stop a b done => intro good;exact .stop a b done
 | @step a b reply out active head tail ih =>
   intro good
   have same:=NBO_QueryAssociation.source ops proof p a g none geometry b
     good.1.weights good.1.phase.2.1 active good.1.sync (order a)
   refine .step active (same.symm.trans head) (ih ?_)
   cases reply with
   | Err error => trivial
   | Ok pair =>
     rcases pair with ⟨a1,b1⟩
     exact ⟨NBF_QueryInvariant.step ops fields.power proof p g geometry prepared.rho
       a a1 b b1 good.1 active head,
       (NBO_AcceptedTail.canonical ops lower fields proof p prepared a a1 g geometry
         domain b b1 active good.1 good.2 head).1⟩
 | @fail a b active error head =>
   intro good
   have same:=NBO_QueryAssociation.source ops proof p a g none geometry b
     good.1.weights good.1.phase.2.1 active good.1.sync (order a)
   exact .fail active error (same.symm.trans head)
 | @div a b active head =>
   intro good
   have same:=NBO_QueryAssociation.source ops proof p a g none geometry b
     good.1.weights good.1.phase.2.1 active good.1.sync (order a)
   exact .div active (same.symm.trans head)
/-- Complete loop Result association, without a loop-success premise.
Constructors supply all initial row/phase/power/rhs domains; each subsequent
caller is established above rather than postulated globally. -/
theorem from_constructors (base : VTop_Stages.Ops) (reserved : Bool) (ops : Ops)
 (lower : NBO_QueryDomains.Lower ops) (bindings : NBO_FieldSemantics.NBC_Bindings ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b)) :
 verifier.candidate.query_loop (sourceOps ops) proof p a g none geometry b 10#usize =
 AspisR1Stage2.verifier.candidate.query_loop (referenceCall ops)
   proof p a g none geometry b 10#usize := by
 obtain ⟨result,history,same⟩ := NBB_QueryWitness.direct (sourceOps ops)
   proof p g none geometry 10#usize a b
 obtain ⟨_,good⟩:=NBF_QueryInitial.good base reserved a b initial pending
 have converted:=transport ops lower bindings proof p prepared g geometry domain (.Ok (a,b)) result
   (by simpa only [show (10#usize).val=10 from rfl] using history)
   ⟨good,NBO_TailDomain.initial base reserved a initial⟩
 have referenceResult:=NBB_QueryTrace.native_result (referenceCall ops) proof p g none geometry
   10#usize (.Ok (a,b)) result converted
 exact same.trans referenceResult.symm
#print axioms transport
#print axioms from_constructors
end NBO_LoopAssociation
end
