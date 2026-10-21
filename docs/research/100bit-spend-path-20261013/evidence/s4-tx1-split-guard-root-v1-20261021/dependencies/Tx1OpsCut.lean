import AspisR1CurrentCaller.Types
import Aeneas
set_option autoImplicit false
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CallerV4Tx1OpsCut
open AspisR1CurrentCaller

structure Ops (H : Type) where
  split : Std.Usize
  offFoldedRoot : Result Std.Usize
  offRound1 : Result Std.Usize
  zero : Result aspis_core.field.wide_exact.WideExact
  mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit
  parseShape : Slice Std.U8 → Result (core.result.Result transport.Variant verifier.Error)
  canonicalScan : Slice Std.U8 → Result (core.result.Result Unit verifier.Error)
  prepare : aspis_core.digest.Digest32 H → aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Slice Std.U8 → H → Option (verifier.Phase → Result Unit) → Array aspis_core.field.wide_exact.WideExact 29#usize → Result ((core.result.Result verifier.Prepared verifier.Error) × Array aspis_core.field.wide_exact.WideExact 29#usize)
  accumulatorNew : transport.Variant → Result (core.result.Result verifier.Accumulator verifier.Error)
  batchMerkle : aspis_core.digest.Digest32 H → (Slice Std.U8) → verifier.Prepared → Array Std.U8 32#usize → Std.Usize → H → Result (core.result.Result Unit verifier.Error)
  makeGeometry : Array Std.U32 22#usize → Std.Usize → Std.Usize → Result (core.result.Result verifier.QueryGeometry verifier.Error)
  weightsNew : Slice aspis_core.field.QM31 → Result (core.result.Result verifier.BatchedWeights verifier.Error)
  queryLoop : Slice Std.U8 → verifier.Prepared → verifier.Accumulator → Array aspis_core.field.wide_exact.WideExact 29#usize → Option (verifier.Phase → Result Unit) → verifier.QueryGeometry → verifier.BatchedWeights → Std.Usize → Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
  weightsFinish : verifier.BatchedWeights → Slice aspis_core.field.QM31 → Result (Slice aspis_core.field.QM31)
  checkpoint : aspis_core.digest.Digest32 H → verifier.Prepared → verifier.Accumulator → Slice Std.U8 → Slice Std.U8 → H → Result (alloc.vec.Vec Std.U8)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem tryContinueOk {α ε β : Type}
    (r : core.result.Result α ε)
    (k : α → Result (core.result.Result β ε)) (b : β)
    (h : (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue a => k a
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          β (core.convert.FromSame ε) residual) = .ok (.Ok b)) :
    ∃ a, r = .Ok a ∧ k a = .ok (.Ok b) := by
  cases r with
  | Ok a =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    exact ⟨a, rfl, h⟩
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h

/-- Exact source suffix after successful `prepare`; factored only so its
    Result continuation can be inverted without reopening Array.repeat's bound. -/
def afterPrepared {H : Type} (ops : Ops H) (inst : aspis_core.digest.Digest32 H)
    (prepared : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (proof public_bytes : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  let r3 ← ops.accumulatorNew transport.Variant.S2
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val1 =>
    ops.mark obs verifier.Phase.Prepare
    let i ← ops.offFoldedRoot
    let i1 ← ops.offRound1
    let s ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
      { start := i, «end» := i1 }
    let r4 ← core.array.TryFromArrayCopySlice.try_from 32#usize
      core.marker.CopyU8 s
    let folded_root ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r4
    let r5 ← ops.batchMerkle inst proof prepared folded_root 0#usize hash
    let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
    match cf4 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      ops.mark obs (verifier.Phase.Merkle 0#usize)
      let r6 ← ops.makeGeometry prepared.queries 0#usize k
      let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
      match cf5 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let s1 := alloc.vec.Vec.deref val1.weights
        let r7 ← ops.weightsNew s1
        let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
        match cf6 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r8 ← ops.queryLoop proof prepared val1 scratch obs val2 val3 k
          let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
          match cf7 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (a, pending) := val4
            let (s2, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut a.weights)
            let s3 ← ops.weightsFinish pending s2
            let v := deref_mut_back s3
            let bytes ← ops.checkpoint inst prepared { a with weights := v } proof public_bytes hash
            ops.mark obs verifier.Phase.CheckpointWrite
            ok (.Ok bytes)
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

def tx1 {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    Result (core.result.Result (alloc.vec.Vec Std.U8) verifier.Error) := do
  if k != ops.split then ok (.Err verifier.Error.Parse)
  else
    let r ← ops.parseShape proof
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let r1 ← ops.canonicalScan proof
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        ops.mark obs verifier.Phase.Parsed
        let we ← ops.zero
        let g := Array.repeat 29#usize we
        let (r2, g1) ← ops.prepare inst public1 proof hash obs g
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val =>
          afterPrepared ops inst val g1 proof public_bytes k hash obs
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual

end AspisR1CallerV4Tx1OpsCut

namespace AspisR1CallerV4Tx1OpsCut
open AspisR1CurrentCaller

theorem tx1_success_prepare_same_suffix {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec Std.U8)
    (h : tx1 ops inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    ∃ parsed zero prepared scratch,
      ops.parseShape proof = .ok (.Ok parsed) ∧
      ops.canonicalScan proof = .ok (.Ok ()) ∧
      ops.zero = .ok zero ∧
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) =
        .ok (.Ok prepared, scratch) ∧
      afterPrepared ops inst prepared scratch proof public_bytes k hash obs =
        .ok (.Ok bytes) := by
  unfold tx1 at h
  by_cases hk : k != ops.split
  · simp [hk] at h
  · simp only [if_neg hk] at h
    obtain ⟨r, hr, hrest⟩ := bind_ok_inv h
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hrest
    | Ok parsed =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrest
      obtain ⟨r1, hr1, hrest⟩ := bind_ok_inv hrest
      cases r1 with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hrest
      | Ok _ =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrest
        obtain ⟨_, hmarkParsed, hrest⟩ := bind_ok_inv hrest
        obtain ⟨zero, hzero, hrest⟩ := bind_ok_inv hrest
        obtain ⟨prepPair, hprep, hrest⟩ := bind_ok_inv hrest
        rcases prepPair with ⟨r2, scratch⟩
        change (do
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf with
          | core.ops.control_flow.ControlFlow.Continue a =>
              afterPrepared ops inst a scratch proof public_bytes k hash obs
          | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame verifier.Error) residual) =
            .ok (.Ok bytes) at hrest
        cases r2 with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hrest
        | Ok prepared =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at hrest
          exact ⟨parsed, zero, prepared, scratch, hr, hr1, hzero, hprep, hrest⟩

end AspisR1CallerV4Tx1OpsCut

#print axioms AspisR1CallerV4Tx1OpsCut.tx1

namespace AspisR1CallerV4Tx1OpsCut
open AspisR1CurrentCaller

theorem afterPrepared_success_query_loop {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H)
    (prepared : verifier.Prepared)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (proof public_bytes : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (bytes : alloc.vec.Vec Std.U8)
    (h : afterPrepared ops inst prepared scratch proof public_bytes k hash obs = .ok (.Ok bytes)) :
    ∃ initialAcc geom pending outputAcc outputPending,
      ops.queryLoop proof prepared initialAcc scratch obs geom pending k =
        .ok (.Ok (outputAcc, outputPending)) := by
  unfold afterPrepared at h
  obtain ⟨r3, hr3, h⟩ := bind_ok_inv h
  cases r3 with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | Ok val1 =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
    obtain ⟨_, hmark, h⟩ := bind_ok_inv h
    obtain ⟨i, hi, h⟩ := bind_ok_inv h
    obtain ⟨i1, hi1, h⟩ := bind_ok_inv h
    obtain ⟨s, hs, h⟩ := bind_ok_inv h
    obtain ⟨r4, hr4, h⟩ := bind_ok_inv h
    obtain ⟨foldedRoot, hfolded, h⟩ := bind_ok_inv h
    obtain ⟨r5, hr5, h⟩ := bind_ok_inv h
    cases r5 with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok _ =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨_, hmark2, h⟩ := bind_ok_inv h
      obtain ⟨r6, hr6, h⟩ := bind_ok_inv h
      cases r6 with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
      | Ok geom =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
        obtain ⟨r7, hr7, h⟩ := bind_ok_inv h
        cases r7 with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | Ok pending =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          obtain ⟨r8, hr8, h⟩ := bind_ok_inv h
          cases r8 with
          | Err e =>
            simp [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
          | Ok pair =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
            rcases pair with ⟨acc, pending'⟩
            exact ⟨val1, geom, pending, acc, pending', hr8⟩

end AspisR1CallerV4Tx1OpsCut

namespace AspisR1CallerV4Tx1OpsCut
open AspisR1CurrentCaller

theorem tx1_success_same_prepare_and_query {H : Type} (ops : Ops H)
    (inst : aspis_core.digest.Digest32 H)
    (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice Std.U8) (k : Std.Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec Std.U8)
    (h : tx1 ops inst public1 public_bytes proof k hash obs = .ok (.Ok bytes)) :
    ∃ parsed zero prepared scratch initialAcc geom pending outputAcc outputPending,
      ops.parseShape proof = .ok (.Ok parsed) ∧
      ops.canonicalScan proof = .ok (.Ok ()) ∧
      ops.zero = .ok zero ∧
      ops.prepare inst public1 proof hash obs (Array.repeat 29#usize zero) =
        .ok (.Ok prepared, scratch) ∧
      ops.queryLoop proof prepared initialAcc scratch obs geom pending k =
        .ok (.Ok (outputAcc, outputPending)) := by
  obtain ⟨parsed, zero, prepared, scratch, hparse, hscan, hzero, hprep, hafter⟩ :=
    tx1_success_prepare_same_suffix ops inst public1 public_bytes proof k hash obs bytes h
  obtain ⟨initialAcc, geom, pending, outputAcc, outputPending, hquery⟩ :=
    afterPrepared_success_query_loop ops inst prepared scratch proof public_bytes k hash obs bytes hafter
  exact ⟨parsed, zero, prepared, scratch, initialAcc, geom, pending, outputAcc, outputPending,
    hparse, hscan, hzero, hprep, hquery⟩

#print axioms tx1_success_same_prepare_and_query
end AspisR1CallerV4Tx1OpsCut
