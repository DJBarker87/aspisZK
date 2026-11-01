import R1Z.PV_RunJoin_ResultPost41
import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PrepareFrame66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem source (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn) :
    Post (fun status => match status with | .Err _ => True | .Ok p => p.backend=backend)
      (prover.prepare_opening variant hash backend sem) := by
  unfold prover.prepare_opening
  apply PV_RunJoin_ResultPost41.bind
  intro different
  cases different with
  | true => trivial
  | false =>
    simp only [Bool.false_eq_true,if_false]
    apply PV_RunJoin_ResultPost41.bind
    intro coefficients
    apply PV_RunJoin_ResultPost41.bind
    intro scp
    apply PV_RunJoin_ResultPost41.bind
    intro we
    apply PV_RunJoin_ResultPost41.bind
    intro we1
    apply PV_RunJoin_ResultPost41.bind
    intro y1
    apply PV_RunJoin_ResultPost41.bind
    intro state
    apply PV_RunJoin_ResultPost41.bind
    intro transcript
    apply PV_RunJoin_ResultPost41.bind
    rintro ⟨gamma,transcript1⟩
    simp only [Aeneas.Std.uncurry]
    apply PV_RunJoin_ResultPost41.bind
    intro q
    apply PV_RunJoin_ResultPost41.bind
    intro status
    cases status with
    | Err e => trivial
    | Ok weights =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro inactive
      apply PV_RunJoin_ResultPost41.bind
      intro encoded
      simp only [lift,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      rintro ⟨kappa,transcript2⟩
      simp only [Aeneas.Std.uncurry]
      apply PV_RunJoin_ResultPost41.bind
      intro material
      cases material with
      | Err e => trivial
      | Ok w =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro c0
        simp only [lift,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro c0bytes
        apply PV_RunJoin_ResultPost41.bind
        rintro ⟨alpha0,transcript3⟩
        simp only [Aeneas.Std.uncurry]
        apply PV_RunJoin_ResultPost41.bind
        intro q1
        apply PV_RunJoin_ResultPost41.bind
        intro w1
        apply PV_RunJoin_ResultPost41.bind
        intro domain
        apply PV_RunJoin_ResultPost41.bind
        intro mapped
        cases mapped with
        | Err e => trivial
        | Ok folded => rfl

theorem complete (variant : transport.Variant) (hash : aspis_core.digest.LegacyHashFn)
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (p : prover.PreparedOpening) (success : prover.prepare_opening variant hash backend sem=ok (.Ok p)) :
    p.backend=backend :=
  PV_RunJoin_ResultPost41.success _ _ (.Ok p) (source variant hash backend sem) success

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_PrepareFrame66
