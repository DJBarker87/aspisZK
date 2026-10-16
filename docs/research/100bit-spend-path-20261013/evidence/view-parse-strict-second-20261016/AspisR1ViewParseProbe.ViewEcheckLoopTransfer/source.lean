import AspisR1ViewParseProbe.ViewEcheckLoopSuccess
import CanonicalLiteralEcheckLoopSuccess

set_option autoImplicit false

namespace AspisR1ViewParseProbe.ViewEcheckLoopTransfer
open Aeneas Aeneas.Std Result
open AspisR1ViewParseProbe.ViewEcheckLoopSuccess
open AspisR1ViewParseProbe.ViewEcheckParserAgreement

abbrev Iter := core.slice.iter.ChunksExact U8

theorem echeckcut_loop_success_from_parses (iter : Iter)
    (hall : ∀ chunk ∈ iter.chunks,
      ∃ w : EWide,
        AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes chunk =
          ok (some w)) :
    AspisR1EcheckCut.verifier.echeck_loop iter false =
      ok (core.result.Result.Ok ()) := by
  rw [AspisR1.CanonicalLiteralEcheckLoopSuccess.loop_unroll]
  cases hc : iter.chunks with
  | nil => simp [core.slice.iter.IteratorChunksExact.next, hc]
  | cons chunk chunks =>
    let next : Iter := { chunks := chunks, remainder := iter.remainder }
    have hmem : chunk ∈ iter.chunks := by simp [hc]
    obtain ⟨w, hw⟩ := hall chunk hmem
    have htail : ∀ c ∈ next.chunks,
        ∃ w : EWide,
          AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes c = ok (some w) := by
      intro c hc'
      have hcChunks : c ∈ chunks := by simpa [next] using hc'
      have hcin : c ∈ chunk :: chunks := List.mem_cons_of_mem chunk hcChunks
      exact hall c (by simpa [hc] using hcin)
    have ih := echeckcut_loop_success_from_parses next htail
    simp only [core.slice.iter.IteratorChunksExact.next, hc, bind_tc_ok]
    change (do
      let o1 ← AspisR1EcheckCut.field.wide_exact.WideExact.from_le_bytes chunk
      let r ← AspisR1PrefixAggregateParser.core.option.Option.ok_or o1
        AspisR1EcheckCut.verifier.Error.Parse
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        if false then do
          let q ← AspisR1EcheckCut.field.wide_exact.WideExact.impl.c1 val
          let b ← core.cmp.PartialEq.ne.trait_default
            AspisR1EcheckCut.field.QM31.Insts.CoreCmpPartialEqQM31 q
            AspisR1EcheckCut.field.QM31.ZERO
          if b then ok (core.result.Result.Err AspisR1EcheckCut.verifier.Error.Parse)
          else AspisR1EcheckCut.verifier.echeck_loop next true
        else AspisR1EcheckCut.verifier.echeck_loop next false
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame AspisR1EcheckCut.verifier.Error) residual) =
      ok (core.result.Result.Ok ())
    simp only [hw, bind_tc_ok,
      AspisR1PrefixAggregateParser.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, ↓reduceIte]
    exact ih
termination_by iter.chunks.length
decreasing_by simp only [hc, List.length_cons]; omega

#print axioms echeckcut_loop_success_from_parses

end AspisR1ViewParseProbe.ViewEcheckLoopTransfer
