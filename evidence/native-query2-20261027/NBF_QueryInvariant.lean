import NBF_PowerStep
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_QueryInvariant
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
structure Good (a : verifier.Accumulator) (b : verifier.BatchedWeights) : Prop where
 weights : a.weights.val.length=64
 sync : b.terms=a.next
 phase : S7JoinRowsTrace.Progress a.next.val 0 (Port3_RowsInstall.toBW b)
 power : NBF_PowerStep.Canonical a.power

theorem step (ops : Ops) (field : NBF_PowerStep.NBC_Qm31Canonical ops)
 (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (rho : NBF_PowerStep.Canonical p.rho)
 (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (good : Good a b) (active : a.next.val<10)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) : Good out bout := by
 have phase : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b) := by
   rw [good.sync];exact good.phase
 obtain ⟨weights,next,sync,phaseOut⟩ := NBF_QueryStep.phase ops proof p a out g geometry b bout
   good.weights active good.sync phase good.power run
 exact ⟨by rw [weights];exact good.weights,sync,phaseOut,
   NBF_PowerStep.query ops field proof p a out g geometry b bout good.weights phase good.power rho run⟩

def StateGood (s : NBB_QueryTrace.State) : Prop :=
 match s with | .Err _=>True | .Ok (a,b)=>Good a b

def ResultGood (s : Result NBB_QueryTrace.State) : Prop :=
 match s with | .fail _=>True | .div=>True | .ok s=>StateGood s

/-- The inherited chronological query trace propagates the exact phase and
canonical-power domain, including rejection/failure/divergence without suffix. -/
theorem trace (ops : Ops) (field : NBF_PowerStep.NBC_Qm31Canonical ops)
 (proof : Slice U8) (p : verifier.Prepared) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (rho : NBF_PowerStep.Canonical p.rho)
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
     exact step ops field proof p g geometry rho a a1 b b1 good active head
 | fail => intro good;trivial
 | div => intro good;trivial
#print axioms step
#print axioms trace
end NBF_QueryInvariant
