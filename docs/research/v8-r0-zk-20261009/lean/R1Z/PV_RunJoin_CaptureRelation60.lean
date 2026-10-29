import R1Z.PV_RunJoin_ActualProvenance60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CaptureRelation60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualProvenance60 (capture)
variable [ExternalTypes] [ExternalFuns]

/-- A successful callback output exposes the phase actually reached by the
same prefix, with exactly the same returned audit and nonce-store state. -/
def Rel {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (left : Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T))
    (right : Result (core.result.Result (Phase × prover.MaskedFixtureAudit) verifier.Error × T)) : Prop :=
  ∀ a audit next, left=ok (.Ok (a,audit),next) →
    ∃ p, right=ok (.Ok (p,audit),next) ∧ f p=ok (.Ok a)

theorem same_bind {A B T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (m : Result B)
    (left : B → Result (core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T))
    (right : B → Result (core.result.Result (Phase × prover.MaskedFixtureAudit) verifier.Error × T))
    (step : ∀ b, Rel f (left b) (right b)) : Rel f (m >>= left) (m >>= right) := by
  cases m with
  | ok b => exact step b
  | fail e => intro a audit next h; cases h
  | div => intro a audit next h; cases h

theorem error {A T : Type} (f : Phase → Result (core.result.Result A verifier.Error))
    (e : verifier.Error) (store : T) : Rel f (ok (.Err e,store)) (ok (.Err e,store)) := by
  intro a audit next h
  cases h

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
  intro a resultAudit next success
  cases hf : f p with
  | fail e => simp only [hf,bind_tc_fail] at success; cases success
  | div => simp only [hf,bind_tc_div] at success; cases success
  | ok r =>
    cases r with
    | Err e =>
      simp only [hf,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame,bind_tc_ok] at success
      cases success
    | Ok value =>
      simp only [hf,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch] at success
      cases success
      exact ⟨p,rfl,hf⟩

#print axioms same_bind
#print axioms error
#print axioms tail
end R1Z.PV_RunJoin_CaptureRelation60
