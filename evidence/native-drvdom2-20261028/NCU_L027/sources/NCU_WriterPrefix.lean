import NCU_PrefixTail
import NBA_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCU_WriterPrefix
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The emitted release driver up to its writer invocation. No writer success
is required. `factor` below checks this factor against the original body for
ALL outer/inner outcomes, not just accepted runs. -/
@[irreducible] def beforeWriter (ops : Ops) {H : Type}
    (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  if split != compact.SPLIT then ok (.Err .Parse) else
    let parsed ← ops.op3 proof
    match parsed with
    | .Err e => ok (.Err e)
    | .Ok _ =>
      let scan ← ops.op4 proof
      match scan with
      | .Err e => ok (.Err e)
      | .Ok _ =>
        let zero ← aspis_core.field.wide_exact.WideExact.ZERO ops
        let (r,g) ← verifier.candidate.prepare ops D semantic proof hash none (Array.repeat 29#usize zero)
        match r with
        | .Err e => ok (.Err e)
        | .Ok p => NCU_PrefixTail.tail ops D pub proof split hash p g

attribute [local irreducible] verifier.candidate.prepare Tx1Reachability.afterPrepare

set_option pp.all true in
theorem factor (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H) :
    verifier.candidate.tx1 ops D semantic pub proof split hash none =
      NCU_PrefixTail.finish ops D pub proof hash
        (beforeWriter ops D semantic pub proof split hash) := by
  unfold verifier.candidate.tx1 beforeWriter NCU_PrefixTail.finish
  split
  · simp (config := { zeta := true }) only [bind_tc_ok]
  · simp (config := { zeta := true }) only [bind_assoc_eq]
    apply NBA_QueryJoin.bind_same
    intro parsed
    cases parsed with
    | Err e =>
      simp (config := { zeta := true }) only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from]
    | Ok variant =>
      simp (config := { zeta := true }) only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,bind_assoc_eq]
      apply NBA_QueryJoin.bind_same
      intro scan
      cases scan with
      | Err e =>
        simp (config := { zeta := true }) only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from]
      | Ok u =>
        simp (config := { zeta := true }) only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark,bind_assoc_eq]
        apply NBA_QueryJoin.bind_same
        intro zero
        apply NBA_QueryJoin.bind_same
        rintro ⟨r,g⟩
        cases r with
        | Err e =>
          simp (config := { zeta := true }) only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from]
        | Ok p =>
          have h := NCU_PrefixTail.factor ops D pub proof split hash p g
          unfold Tx1Reachability.afterPrepare NCU_PrefixTail.finish at h
          simpa only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,verifier.mark] using h

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
  simp (config := { zeta := true }) only [NCU_PrefixTail.finish,bind_tc_ok]

/-- No protocol rejection is possible after the writer is reached in release
mode. The writer can still fail/diverge in the outer Aeneas Result. -/
theorem no_later_reject (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : Reached ops D semantic pub proof split hash p a) (e : verifier.Error) :
    verifier.candidate.tx1 ops D semantic pub proof split hash none ≠ ok (.Err e) := by
  rw [resume ops D semantic pub proof split hash p a reached]
  cases ops.op16 D p a proof pub hash <;> simp (config := { zeta := true }) only [bind_tc_ok,bind_tc_fail,bind_tc_div] <;> intro h <;> cases h

#print axioms factor
#print axioms resume
#print axioms no_later_reject
end AspisR1.NCU_WriterPrefix
end
