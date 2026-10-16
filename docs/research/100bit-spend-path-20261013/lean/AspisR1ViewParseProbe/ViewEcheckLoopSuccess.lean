import AspisR1ViewParseProbe.CleanParameterizedParse
import AspisR1ViewParseProbe.ViewEcheckParserAgreement

set_option autoImplicit false

namespace AspisR1ViewParseProbe.ViewEcheckLoopSuccess
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1ViewParseProbe.ViewEcheckParserAgreement

abbrev Iter := core.slice.iter.ChunksExact U8

def Parses (chunk : Slice U8) : Prop :=
  ∃ w, AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes chunk =
    ok (some w)

theorem loop_unroll (iter : Iter) (k : Bool) :
    AspisR1ViewParseProbe.verifier.echeck_loop iter k = (do
      let (o, iter1) ← core.slice.iter.IteratorChunksExact.next iter
      match o with
      | none => ok (core.result.Result.Ok ())
      | some c => do
        let o1 ← AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes c
        let r ← AspisR1ViewParseProbe.core.option.Option.ok_or o1
          AspisR1ViewParseProbe.verifier.Error.Parse
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          if k then do
            let q ← AspisR1ViewParseProbe.field.wide_exact.WideExact.impl.c1 val
            let b ← core.cmp.PartialEq.ne.trait_default
              AspisR1ViewParseProbe.field.QM31.Insts.CoreCmpPartialEqQM31 q
              AspisR1ViewParseProbe.field.QM31.ZERO
            if b then ok (core.result.Result.Err AspisR1ViewParseProbe.verifier.Error.Parse)
            else AspisR1ViewParseProbe.verifier.echeck_loop iter1 true
          else AspisR1ViewParseProbe.verifier.echeck_loop iter1 false
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame AspisR1ViewParseProbe.verifier.Error) residual) := by
  rw [AspisR1ViewParseProbe.verifier.echeck_loop.eq_def]
  rfl

theorem loop_success (iter : Iter)
    (h : AspisR1ViewParseProbe.verifier.echeck_loop iter false =
      ok (core.result.Result.Ok ())) :
    ∀ chunk ∈ iter.chunks, Parses chunk := by
  rw [loop_unroll] at h
  cases hc : iter.chunks with
  | nil => simp
  | cons chunk chunks =>
    simp only [core.slice.iter.IteratorChunksExact.next, hc, bind_tc_ok,
      ↓reduceIte] at h
    let next : Iter := { chunks := chunks, remainder := iter.remainder }
    change (do
      let o1 ← AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes chunk
      let r ← AspisR1ViewParseProbe.core.option.Option.ok_or o1
        AspisR1ViewParseProbe.verifier.Error.Parse
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        AspisR1ViewParseProbe.verifier.echeck_loop next false
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame AspisR1ViewParseProbe.verifier.Error) residual) =
        ok (core.result.Result.Ok ()) at h
    cases hp : AspisR1ViewParseProbe.field.wide_exact.WideExact.from_le_bytes chunk with
    | fail e =>
      have hf : False := by simp [hp, bind_tc_fail] at h
      exact hf.elim
    | div =>
      have hf : False := by simp [hp, bind_tc_div] at h
      exact hf.elim
    | ok decoded =>
      cases decoded with
      | none =>
        have hf : False := by
          simp [hp, AspisR1ViewParseProbe.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        exact hf.elim
      | some w =>
        simp only [hp, bind_tc_ok,
          AspisR1ViewParseProbe.core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch] at h
        change AspisR1ViewParseProbe.verifier.echeck_loop next false =
          ok (core.result.Result.Ok ()) at h
        have ih := loop_success next h
        intro candidate hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact ⟨w, hp⟩
        · exact ih candidate hmem
termination_by iter.chunks.length
decreasing_by simp only [hc, List.length_cons]; omega

theorem loop_success_echeckcut (iter : Iter)
    (h : AspisR1ViewParseProbe.verifier.echeck_loop iter false =
      ok (core.result.Result.Ok ())) :
    ∀ chunk ∈ iter.chunks,
      ∃ w : EWide,
        AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes chunk =
          ok (some w) := by
  intro chunk hmem
  obtain ⟨w, hw⟩ := loop_success iter h chunk hmem
  exact ⟨wideToEcheck w, parsed_wide_transfers chunk w hw⟩

#print axioms loop_success
#print axioms loop_success_echeckcut

end AspisR1ViewParseProbe.ViewEcheckLoopSuccess
