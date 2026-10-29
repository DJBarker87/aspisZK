import R1Z.PV_RunJoin_ActualProvenance60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CaptureFactorRelation60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes] [ExternalFuns]

def resume {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (beforeResult : Result (core.result.Result (Phase × prover.MaskedFixtureAudit) verifier.Error × T)) :
    Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T) := do
  let (status,store) ← beforeResult
  match status with
  | .Err e => ok (.Err e,store)
  | .Ok (p,audit) => do
    let result ← f p
    match result with
    | .Err e => ok (.Err e,store)
    | .Ok a => ok (.Ok (a,audit),store)

def Rel {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (left : Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T))
    (right : Result (core.result.Result (Phase × prover.MaskedFixtureAudit) verifier.Error × T)) : Prop :=
  left=resume f right

theorem same_bind {A B T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (m : Result B)
    (left : B → Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T))
    (right : B → Result (core.result.Result (Phase × prover.MaskedFixtureAudit) verifier.Error × T))
    (step : ∀ b, Rel f (left b) (right b)) : Rel f (m >>= left) (m >>= right) := by
  cases m with
  | ok b => exact step b
  | fail e => rfl
  | div => rfl

theorem error {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (e : verifier.Error) (store : T) : Rel f (ok (.Err e,store)) (ok (.Err e,store)) := rfl

theorem tail {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (p : Phase) (audit : prover.MaskedFixtureAudit) (store : T) :
    Rel f
      (do let r ← f p
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue value => ok (.Ok (value,{audit with h1_total_balanced:=true}),store)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (A × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) residual
            ok (r1,store))
      (do let r ← capture p
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue value => ok (.Ok (value,{audit with h1_total_balanced:=true}),store)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (Phase × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) residual
            ok (r1,store)) := by
  cases hf : f p with
  | fail e => simp only [Rel,resume,capture,bind_tc_ok,hf];rfl
  | div => simp only [Rel,resume,capture,bind_tc_ok,hf];rfl
  | ok result => cases result <;> simp only [Rel,resume,capture,bind_tc_ok,hf] <;> rfl

#print axioms same_bind
#print axioms error
#print axioms tail
end R1Z.PV_RunJoin_CaptureFactorRelation60
