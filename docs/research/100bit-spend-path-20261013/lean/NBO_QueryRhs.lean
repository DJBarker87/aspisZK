import NBO_AcceptedTail
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBO_QueryRhs
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open NBO_TailDomain (WideCanonical)
def Good (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop :=
 NBF_QueryInvariant.Good a b ∧ WideCanonical a.rhs
def StateGood (s : NBB_QueryTrace.State) : Prop :=
 match s with | .Err _=>True | .Ok (a,b)=>Good a b
def ResultGood (s : Result NBB_QueryTrace.State) : Prop :=
 match s with | .fail _=>True | .div=>True | .ok s=>StateGood s
/-- Chronological induction now carries the rhs multiplication domain as
well as the inherited power/row domain, including error/failure/divergence. -/
theorem trace (ops : Ops) (lower : NBO_QueryDomains.Lower ops)
 (fields : NBO_TailDomain.NBC_Fields ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (state : NBB_QueryTrace.State) (out : Result NBB_QueryTrace.State)
 (history : NBB_QueryTrace.Trace (fun a b=>verifier.candidate.query_values
   (NBF_Accumulate.install ops) proof p a g none geometry b) 10 state out) :
 StateGood state → ResultGood out := by
 induction history with
 | error => intro good;trivial
 | stop => intro good;exact good
 | @step a b reply out active head tail ih =>
   intro good
   apply ih
   cases reply with
   | Err e=>trivial
   | Ok pair=>
     rcases pair with ⟨a1,b1⟩
     exact ⟨NBF_QueryInvariant.step ops fields.power proof p g geometry prepared.rho
       a a1 b b1 good.1 active head,
       (NBO_AcceptedTail.canonical ops lower fields proof p prepared a a1 g geometry
         domain b b1 active good.1 good.2 head).1⟩
 | fail => intro good;trivial
 | div => intro good;trivial
/-- SAME constructors and SAME accepted loop; no initial canonicality,
row phase, selected prefix output or final rhs property is a premise. -/
theorem from_constructors (base : VTop_Stages.Ops) (reserved : Bool)
 (ops : Ops) (lower : NBO_QueryDomains.Lower ops) (fields : NBO_TailDomain.NBC_Fields ops)
 (proof : Slice U8) (p : verifier.Prepared) (prepared : NBO_AcceptedTail.PreparedDomain p)
 (g : Array Stage2E 29#usize) (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry)
 (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (initial : (Port3_Initial.install base reserved).op12 .S2=ok (.Ok a))
 (pending : Port3_NativePendingInstall.source reserved a.weights.deref=ok (.Ok b))
 (run : verifier.candidate.query_loop (NBF_Accumulate.install ops)
   proof p a g none geometry b 10#usize=ok (.Ok (out,bout))) : Good out bout := by
 obtain ⟨_,good⟩ := NBF_QueryInitial.good base reserved a b initial pending
 obtain ⟨result,history,same⟩ := NBB_QueryWitness.direct (NBF_Accumulate.install ops)
   proof p g none geometry 10#usize a b
 have eq : result=ok (.Ok (out,bout)) := same.symm.trans run
 rw [eq] at history
 exact trace ops lower fields proof p prepared g geometry domain (.Ok (a,b))
   (ok (.Ok (out,bout)))
   (by simpa only [show (10#usize).val=10 from rfl] using history)
   ⟨good,NBO_TailDomain.initial base reserved a initial⟩
#print axioms trace
#print axioms from_constructors
end NBO_QueryRhs
