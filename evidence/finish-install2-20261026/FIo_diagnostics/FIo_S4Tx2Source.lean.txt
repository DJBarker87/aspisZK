import S4Tx2FullOperationCutV7

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1Stage2
open AspisR1S4Tx2FullOperationCutV7
open AspisR1FastDotsTx2PowersQuerySourceCutV1
open AspisR1S4P6PowersQueryJoinV1 (sourceP6WeightsPowers)

abbrev Prepared := AspisR1Stage2.verifier.Prepared
abbrev Accumulator := AspisR1Stage2.verifier.Accumulator
abbrev Pending := AspisR1Stage2.verifier.BatchedWeights
abbrev Error := AspisR1Stage2.verifier.Error
abbrev Wide := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev QueryCall := AspisR1FastDotsTx2PowersQuerySourceCutV1.QueryCall

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- Operation cut obtained by copying the complete emitted `tx2_common` body.
Only the listed named callees and compact constants are redirected into typed
slots. Result binds, `Try::branch`, both-match arms, every residual propagation,
and the complete post-query suffix stay in the copied body. The trailing
checker token-compares this body with the pinned generated source after the
explicit substitutions. -/
structure Ops (H : Type) where
  resumeOps : AspisR1Stage2.ResumeOps
  weightsPowers : Std.Usize → Wide → Result (Array Wide 29#usize)
  mark : Option (AspisR1Stage2.verifier.Phase → Result Unit) →
    AspisR1Stage2.verifier.Phase → Result Unit
  split : Std.Usize
  optionOkOr : {T E : Type} → Option T → E → Result (core.result.Result T E)
  offInactive : Result Std.Usize
  offRound0 : Result Std.Usize
  offFoldedRoot : Result Std.Usize
  offRound1 : Result Std.Usize
  offFinal : Result Std.Usize
  offOpenings : Result Std.Usize
  wideFromLeBytes : Slice Std.U8 → Result (Option Wide)
  batchMerkle : AspisR1Stage2.aspis_core.digest.Digest32 H → Slice Std.U8 →
    Prepared → Array Std.U8 32#usize → Std.Usize → H →
    Result (core.result.Result Unit Error)
  forRange : Array Std.U32 22#usize → Std.Usize → Std.Usize →
    Result (core.result.Result AspisR1Stage2.verifier.QueryGeometry Error)
  newPending : Slice AspisR1Stage2.aspis_core.field.QM31 →
    Result (core.result.Result Pending Error)
  finishPending : Pending → Slice AspisR1Stage2.aspis_core.field.QM31 →
    Result (Slice AspisR1Stage2.aspis_core.field.QM31)
  finishRelation : AspisR1Stage2.verifier.View → Prepared → Accumulator →
    Option (AspisR1Stage2.verifier.Phase → Result Unit) →
    Result (core.result.Result Unit Error)

/-- Complete emitted body with only the named substitutions documented above. -/
def tx2CommonFullSourceCut {H : Type}
    (ops : Ops H) (call : QueryCall)
    (aspis_coredigestDigest32Inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes : Slice Std.U8) (proof : Slice Std.U8)
    (checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit)) :
    Result (core.result.Result Unit Error) := do
  let r ←
    verifier.resumeWithOps ops.resumeOps aspis_coredigestDigest32Inst checkpoint proof public_bytes
      transport.Variant.S2 hash
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (p, a) := val
    if a.next != ops.split
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let g ← ops.weightsPowers 29#usize p.gamma
      ops.mark obs verifier.Phase.CheckpointRead
      let i ← ops.offInactive
      let i1 ← ops.offRound0
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
          { start := i, «end» := i1 }
      let o ← ops.wideFromLeBytes s
      let r1 ← ops.optionOkOr o verifier.Error.Parse
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let i2 ← ops.offFoldedRoot
        let i3 ← ops.offRound1
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
            { start := i2, «end» := i3 }
        let r2 ←
          core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
            s1
        let folded_root ←
          core.result.Result.unwrap core.fmt.DebugTryFromSliceError r2
        let r3 ←
          ops.batchMerkle aspis_coredigestDigest32Inst proof p
            folded_root 1#usize hash
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ops.mark obs (verifier.Phase.Merkle ops.split)
          let r4 ← ops.forRange p.queries a.next 22#usize
          let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val2 =>
            let s2 := alloc.vec.Vec.deref a.weights
            let r5 ← ops.newPending s2
            let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val3 =>
              let r6 ←
                verifier.candidate.query_loop call proof p a g obs val2 val3
                  22#usize
              let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue val4 =>
                let (a1, pending) := val4
                let (s3, deref_mut_back) ←
                  lift (alloc.vec.Vec.deref_mut a1.weights)
                let s4 ← ops.finishPending pending s3
                let weights := deref_mut_back s4
                let s5 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s6 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                let s7 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i1, «end» := i2 }
                let i4 ← ops.offFinal
                let s8 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i3, «end» := i4 }
                let i5 ← ops.offOpenings
                let s9 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) proof
                    { start := i4, «end» := i5 }
                let s10 ← lift (Array.to_slice (Std.Array.empty Std.U8))
                ops.finishRelation
                  {
                    variant := transport.Variant.S2,
                    semantic := s5,
                    y1 := s6,
                    inactive := val1,
                    round0 := s7,
                    folded_root := none,
                    round1 := s8,
                    final_message := s9,
                    query_bytes := s10
                  } p { a1 with weights } obs
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame verifier.Error) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame verifier.Error) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame verifier.Error) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame verifier.Error) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame verifier.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame verifier.Error) residual


private theorem branch_continue_inv {A E : Type}
    (r : core.result.Result A E) (x : A)
    (h : core.result.Result.Insts.CoreOpsTry.branch r =
      .ok (core.ops.control_flow.ControlFlow.Continue x)) :
    r = .Ok x := by
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
  | Ok value =>
    cases h
    rfl

theorem tx2CommonFullSourceCut_success_reaches_query_loop {H : Type}
    (ops : Ops H) (call : QueryCall)
    (inst : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice Std.U8) (hash : H)
    (obs : Option (AspisR1Stage2.verifier.Phase → Result Unit))
    (h : tx2CommonFullSourceCut ops call inst public_bytes proof checkpoint hash obs =
      .ok (.Ok ())) :
    ∃ (p : Prepared) (a : Accumulator) (g : Array Wide 29#usize)
      (geometry : AspisR1Stage2.verifier.QueryGeometry) (pending : Pending)
      (a1 : Accumulator) (pending1 : Pending),
      AspisR1Stage2.verifier.resumeWithOps ops.resumeOps inst checkpoint proof
        public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) ∧
      a.next = ops.split ∧
      ops.weightsPowers 29#usize p.gamma = .ok g ∧
      ops.forRange p.queries a.next 22#usize = .ok (.Ok geometry) ∧
      ops.newPending (alloc.vec.Vec.deref a.weights) = .ok (.Ok pending) ∧
      AspisR1Stage2.verifier.candidate.query_loop call proof p a g obs geometry
        pending 22#usize = .ok (.Ok (a1,pending1)) := by
  unfold tx2CommonFullSourceCut at h
  obtain ⟨resumed, hresumeBind, h⟩ := bind_ok_inv h
  obtain ⟨cf, hcfBind, h⟩ := bind_ok_inv h
  cases cf with
  | Break residual =>
    cases residual with
    | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok impossible => cases impossible
  | Continue val =>
    rcases val with ⟨p,a⟩
    dsimp only [] at h
    change (if (a.next != ops.split) = true then
      ok (core.result.Result.Err AspisR1Stage2.verifier.Error.Checkpoint) else _) =
      ok (core.result.Result.Ok ()) at h
    have hresume : AspisR1Stage2.verifier.resumeWithOps ops.resumeOps inst
        checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) := by
      rw [hresumeBind]
      exact congrArg (fun x => ok x)
        (branch_continue_inv resumed (p,a) hcfBind)
    by_cases hguard : (a.next != ops.split) = true
    · simp only [if_pos hguard] at h
      cases h
    · simp only [if_neg hguard] at h
      have hsplit : a.next = ops.split := by
        by_contra hn
        apply hguard
        simp [hn]
      obtain ⟨g,hg,h⟩ := bind_ok_inv h
      obtain ⟨_,_,h⟩ := bind_ok_inv h
      obtain ⟨_,_,h⟩ := bind_ok_inv h
      obtain ⟨_,_,h⟩ := bind_ok_inv h
      obtain ⟨_,_,h⟩ := bind_ok_inv h
      obtain ⟨_,_,h⟩ := bind_ok_inv h
      obtain ⟨r1,hr1,h⟩ := bind_ok_inv h
      obtain ⟨cf1,hcf1,h⟩ := bind_ok_inv h
      cases cf1 with
      | Break residual =>
        cases residual with
        | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        | Ok impossible => cases impossible
      | Continue _ =>
        obtain ⟨_,_,h⟩ := bind_ok_inv h
        obtain ⟨_,_,h⟩ := bind_ok_inv h
        obtain ⟨s1,hs1,h⟩ := bind_ok_inv h
        obtain ⟨r2,hr2,h⟩ := bind_ok_inv h
        obtain ⟨_,_,h⟩ := bind_ok_inv h
        obtain ⟨r3,hr3,h⟩ := bind_ok_inv h
        obtain ⟨cf2,hcf2,h⟩ := bind_ok_inv h
        cases cf2 with
        | Break residual =>
          cases residual with
          | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
          | Ok impossible => cases impossible
        | Continue _ =>
          obtain ⟨_,_,h⟩ := bind_ok_inv h
          obtain ⟨r4,hr4,h⟩ := bind_ok_inv h
          obtain ⟨cf3,hcf3,h⟩ := bind_ok_inv h
          cases cf3 with
          | Break residual =>
            cases residual with
            | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
            | Ok impossible => cases impossible
          | Continue geometry =>
            have hgeometry : ops.forRange p.queries a.next 22#usize =
                .ok (.Ok geometry) := by
              rw [hr4]
              exact congrArg (fun x => ok x)
                (branch_continue_inv r4 geometry hcf3)
            obtain ⟨r5,hr5,h⟩ := bind_ok_inv h
            obtain ⟨cf4,hcf4,h⟩ := bind_ok_inv h
            cases cf4 with
            | Break residual =>
              cases residual with
              | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
              | Ok impossible => cases impossible
            | Continue pending =>
              have hpending : ops.newPending (alloc.vec.Vec.deref a.weights) =
                  .ok (.Ok pending) := by
                rw [hr5]
                exact congrArg (fun x => ok x)
                  (branch_continue_inv r5 pending hcf4)
              obtain ⟨r6,hr6,h⟩ := bind_ok_inv h
              obtain ⟨cf5,hcf5,h⟩ := bind_ok_inv h
              cases cf5 with
              | Break residual =>
                cases residual with
                | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
                | Ok impossible => cases impossible
              | Continue pairOut =>
                rcases pairOut with ⟨a1,pending1⟩
                have hquery : AspisR1Stage2.verifier.candidate.query_loop call proof p a g obs geometry pending 22#usize =
                    .ok (.Ok (a1,pending1)) := by
                  rw [hr6]
                  exact congrArg (fun x => ok x)
                    (branch_continue_inv r6 (a1,pending1) hcf5)
                exact ⟨p,a,g,geometry,pending,a1,pending1,
                  hresume,hsplit,hg,hgeometry,hpending,hquery⟩

#print axioms tx2CommonFullSourceCut
#print axioms tx2CommonFullSourceCut_success_reaches_query_loop
#print axioms tx2CommonFullSourceCut_success_reaches_query_loop
end AspisR1S4Tx2FullSourceOwnedCutV1
