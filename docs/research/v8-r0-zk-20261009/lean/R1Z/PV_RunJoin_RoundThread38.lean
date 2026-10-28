import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundThread38
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31
abbrev Point := Array Q 10#usize
abbrev Output (H : Type) :=
  (core.result.Result (Point × Q) r1_wire.Error) × host_wire.SemanticTranscript H × alloc.vec.Vec U8

def finish {H F : Type} (OracleInst : host_sumcheck.Oracle F)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Point) (running : Q) (oracle : F) : Result (Output H) := do
  let r ← OracleInst.evaluate oracle point
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let b ←
      core.cmp.PartialEq.ne.trait_default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 val running
    if b
    then
      ok (core.result.Result.Err r1_wire.Error.Terminal, transcript, output)
    else ok (core.result.Result.Ok (point, running), transcript, output)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
        (core.convert.FromSame r1_wire.Error) residual
    ok (r1, transcript, output)

/-- Finite ordered source-round fold; the terminal oracle is still the actual
supplied OracleInst. No semantic-terminal law is assumed or credited. -/
def phase {H F : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
    (OracleInst : host_sumcheck.Oracle F) : Nat → host_wire.SemanticTranscript H →
    alloc.vec.Vec U8 → Point → Q → Usize → F → Result (Output H)
  | 0, transcript, output, point, running, _, oracle =>
      finish OracleInst transcript output point running oracle
  | n+1, transcript, output, point, running, round, oracle => do
    let (r, transcript1, output1) ←
      host_sumcheck.prove_sumcheck_round aspis_coredigestDigest32Inst
        OracleInst transcript output point running round oracle
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (point1, running1) := val
      let i ← Aeneas.Std.lift (Std.Usize.wrapping_add round 1#usize)
      phase aspis_coredigestDigest32Inst
        OracleInst n transcript1 output1 point1 running1 i oracle
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array aspis_core.field.QM31 10#usize) × aspis_core.field.QM31)
          (core.convert.FromSame r1_wire.Error) residual
      ok (r1, transcript1, output1)

/-- The whole actual round owner equals a finite fold on the remaining count.
Every source fail/divergence and inner error keeps its original branch; every
successful step passes its returned transcript/output to the next step. -/
theorem thread {H F : Type} (digest : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle F) (oracle : F) (n : Nat)
    (round : Usize) (bound : round.val+n=10)
    (transcript : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Point) (running : Q) :
    host_sumcheck.prove_sumcheck_rounds digest oi transcript output point running round oracle =
      phase digest oi n transcript output point running round oracle := by
  induction n generalizing round transcript output point running with
  | zero =>
    have hz : round=10#usize := by scalar_tac
    subst round
    rw [host_sumcheck.prove_sumcheck_rounds]
    simp only [↓reduceIte,phase,finish]
    rfl
  | succ n ih =>
    have hn : round≠10#usize := by scalar_tac
    have inc := PV_RunJoin_MergeLoop35.increment round (by omega)
    rw [host_sumcheck.prove_sumcheck_rounds]
    simp only [hn,↓reduceIte,phase]
    apply congrArg (Aeneas.Std.bind
      (host_sumcheck.prove_sumcheck_round digest oi transcript output point running round oracle))
    funext triple
    rcases triple with ⟨r,t,o⟩
    dsimp only [Aeneas.Std.uncurry]
    apply congrArg (Aeneas.Std.bind (core.result.Result.Insts.CoreOpsTry.branch r))
    funext cf
    cases cf with
    | Break residual => rfl
    | Continue val =>
      rcases val with ⟨p,q⟩
      simp only [lift,bind_tc_ok]
      exact ih (Usize.wrapping_add round 1#usize) (by rw [inc];omega) t o p q

#print axioms thread
end R1Z.PV_RunJoin_RoundThread38
