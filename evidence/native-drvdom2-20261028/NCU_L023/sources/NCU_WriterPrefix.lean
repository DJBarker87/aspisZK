import NCU_PrefixTail
import NBA_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCU_WriterPrefix
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The emitted release driver up to its writer invocation. No writer success
is required. `factor` below checks this factor against the original body for
ALL outer/inner outcomes, not just accepted runs. -/
def beforeWriter (ops : Ops)
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
  (public_bytes : Slice Std.U8) (proof : Slice Std.U8) (k : Std.Usize)
  (hash : H)  :
  Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
  := do
  if k != compact.SPLIT
  then ok (core.result.Result.Err verifier.Error.Parse)
  else
    let r ← ops.op3 proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← ops.op4 proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        verifier.mark none verifier.Phase.Parsed
        let we ← (aspis_core.field.wide_exact.WideExact.ZERO ops)
        let g := Array.repeat 29#usize we
        let (r2, g1) ←
          (verifier.candidate.prepare ops) aspis_coredigestDigest32Inst public1 proof
            hash none g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          NCU_PrefixTail.tail ops aspis_coredigestDigest32Inst public_bytes proof k hash val g1
        | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame
                      verifier.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame
                    verifier.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (verifier.Prepared × verifier.Accumulator) (core.convert.FromSame verifier.Error) residual

attribute [local irreducible] verifier.candidate.prepare Tx1Reachability.afterPrepare

theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H) :
    verifier.candidate.tx1 ops D semantic pub proof split hash none =
      NCU_PrefixTail.finish ops D pub proof hash
        (beforeWriter ops D semantic pub proof split hash) := by
  unfold verifier.candidate.tx1 beforeWriter NCU_PrefixTail.finish
  split
  · simp only [bind_tc_ok]
  · simp only [bind_assoc_eq]
    apply NBA_QueryJoin.bind_same
    intro parsed
    cases parsed with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
    | Ok variant =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
      apply NBA_QueryJoin.bind_same
      intro scan
      cases scan with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
      | Ok u =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark,bind_assoc_eq]
        apply NBA_QueryJoin.bind_same
        intro zero
        apply NBA_QueryJoin.bind_same
        rintro ⟨r,g⟩
        cases r with
        | Err e =>
          change ok (.Err e) = NCU_PrefixTail.finish ops D pub proof hash (ok (.Err e))
          simp only [NCU_PrefixTail.finish,bind_tc_ok]
        | Ok p =>
          change Tx1Reachability.afterPrepare ops D pub proof split hash none p g =
            NCU_PrefixTail.finish ops D pub proof hash
              (NCU_PrefixTail.tail ops D pub proof split hash p g)
          exact NCU_PrefixTail.factor ops D pub proof split hash p g

/-- All reached calls, including an outer failure/divergence in the writer. -/
def Reached (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator) : Prop :=
  beforeWriter ops D semantic pub proof split hash = ok (.Ok (p,a))

theorem resume (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : Reached ops D semantic pub proof split hash p a) :
    verifier.candidate.tx1 ops D semantic pub proof split hash none =
      (do let bytes ← ops.op16 D p a proof pub hash
          ok (core.result.Result.Ok (E := verifier.Error) bytes)) := by
  rw [factor]
  unfold Reached at reached
  rw [reached]
  simp only [NCU_PrefixTail.finish,bind_tc_ok]

/-- No protocol rejection is possible after the writer is reached in release
mode. The writer can still fail/diverge in the outer Aeneas Result. -/
theorem no_later_reject (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : Reached ops D semantic pub proof split hash p a) (e : verifier.Error) :
    verifier.candidate.tx1 ops D semantic pub proof split hash none ≠ ok (.Err e) := by
  rw [resume ops D semantic pub proof split hash p a reached]
  cases ops.op16 D p a proof pub hash <;> simp only [bind_tc_ok,bind_tc_fail,bind_tc_div] <;> intro h <;> cases h

#print axioms factor
#print axioms resume
#print axioms no_later_reject
end AspisR1.NCU_WriterPrefix
end
