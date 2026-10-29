import R1Z.PV_RunJoin_NativeControl55
import R1Z.PV_RunJoin_ResultRelation55
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NativeResult55
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultRelation55

def Output {A B T : Type} (R : A → B → Prop)
    (a : core.result.Result (A × prover.MaskedFixtureAudit) verifier.Error × T)
    (b : core.result.Result (B × prover.MaskedFixtureAudit) verifier.Error × T) : Prop :=
  CoreRel (fun x y => R x.1 y.1 ∧ x.2=y.2) a.1 b.1 ∧ a.2=b.2

theorem tail {A B T : Type} (R : A → B → Prop)
    (a : Result (core.result.Result A verifier.Error))
    (b : Result (core.result.Result B verifier.Error))
    (audit : prover.MaskedFixtureAudit) (store : T)
    (h : Rel (CoreRel R) a b) :
    Rel (Output R)
      (do let r ← a
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue value => ok (.Ok (value,{audit with h1_total_balanced:=true}),store)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (A × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) residual
            ok (r1,store))
      (do let r ← b
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue value => ok (.Ok (value,{audit with h1_total_balanced:=true}),store)
          | core.ops.control_flow.ControlFlow.Break residual => do
            let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (B × prover.MaskedFixtureAudit) (core.convert.FromSame verifier.Error) residual
            ok (r1,store)) := by
  cases h with
  | fail e => exact .fail e
  | div => exact .div
  | ok hr =>
    cases hr with
    | ok hv => exact .ok ⟨.ok ⟨hv,rfl⟩,rfl⟩
    | err e => exact .ok ⟨.err e,rfl⟩

theorem error {A B T : Type} (R : A → B → Prop) (e : verifier.Error) (store : T) :
    Rel (Output R) (ok (.Err e,store)) (ok (.Err e,store)) := .ok ⟨.err e,rfl⟩
#print axioms Output
#print axioms tail
#print axioms error
end R1Z.PV_RunJoin_NativeResult55
