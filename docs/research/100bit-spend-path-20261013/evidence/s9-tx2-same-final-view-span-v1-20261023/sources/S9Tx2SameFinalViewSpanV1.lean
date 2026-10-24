import S4Tx2FullSourceOwnedCutV1
import S9FinalSpanSourceBoundsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9Tx2SameFinalViewSpanV1
open AspisR1Stage2
open AspisR1S4Tx2FullSourceOwnedCutV1
open AspisR1S9FinalSpanSourceBoundsV1

def withSourceFinalConstants {H : Type} (ops : Ops H) : Ops H :=
  {ops with offFinal:=compact.OFF_FINAL,offOpenings:=compact.OFF_OPENINGS}

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

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

/-- SAME complete emitted tx2_common-body cut constructs the actual final
View internally from its successful fixed proof range. No arbitrary-View
provenance, quotient-to-exact-length or independent finish success premise. -/
theorem source_tx2_success_same_final_view {H : Type}
    (ops : Ops H) (call : AspisR1S4Tx2FullSourceOwnedCutV1.QueryCall)
    (inst : aspis_core.digest.Digest32 H)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : tx2CommonFullSourceCut (withSourceFinalConstants ops) call inst
      public_bytes proof checkpoint hash obs=.ok (.Ok ())) :
    ∃ (v : verifier.View) (p : Prepared) (resumeAcc a : Accumulator) (final openings : Usize),
      verifier.resumeWithOps ops.resumeOps inst checkpoint proof public_bytes
        transport.Variant.S2 hash = .ok (.Ok (p,resumeAcc)) ∧
      ops.finishRelation v p a obs=.ok (.Ok ()) ∧
      compact.OFF_FINAL=.ok final ∧ compact.OFF_OPENINGS=.ok openings ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=final,«end»:=openings}=.ok v.final_message ∧
      v.final_message.val.length=2048 ∧ Slice.len v.final_message=2048#usize := by
  let srcOps := withSourceFinalConstants ops
  change tx2CommonFullSourceCut srcOps call inst public_bytes proof checkpoint hash obs=.ok (.Ok ()) at h
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
    change (if (a.next != srcOps.split) = true then
      ok (core.result.Result.Err AspisR1Stage2.verifier.Error.Checkpoint) else _) =
      ok (core.result.Result.Ok ()) at h
    have hresume : AspisR1Stage2.verifier.resumeWithOps srcOps.resumeOps inst
        checkpoint proof public_bytes transport.Variant.S2 hash = .ok (.Ok (p,a)) := by
      rw [hresumeBind]
      exact congrArg (fun x => ok x)
        (branch_continue_inv resumed (p,a) hcfBind)
    by_cases hguard : (a.next != srcOps.split) = true
    · simp only [if_pos hguard] at h
      cases h
    · simp only [if_neg hguard] at h
      have hsplit : a.next = srcOps.split := by
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
            have hgeometry : srcOps.forRange p.queries a.next 22#usize =
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
              have hpending : srcOps.newPending (alloc.vec.Vec.deref a.weights) =
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
                dsimp only [] at h
                obtain ⟨borrowed,hborrowed,h⟩ := bind_ok_inv h
                rcases borrowed with ⟨oldWeights,weightsBack⟩
                obtain ⟨newWeights,hweights,h⟩ := bind_ok_inv h
                obtain ⟨emptySemantic,hemptySemantic,h⟩ := bind_ok_inv h
                obtain ⟨emptyY1,hemptyY1,h⟩ := bind_ok_inv h
                obtain ⟨round0,hround0,h⟩ := bind_ok_inv h
                obtain ⟨final,hfinal,h⟩ := bind_ok_inv h
                obtain ⟨round1,hround1,h⟩ := bind_ok_inv h
                obtain ⟨openings,hopenings,h⟩ := bind_ok_inv h
                obtain ⟨finalMessage,hfinalMessage,h⟩ := bind_ok_inv h
                obtain ⟨emptyQueries,hemptyQueries,h⟩ := bind_ok_inv h
                have hf : compact.OFF_FINAL=.ok final := hfinal
                have ho : compact.OFF_OPENINGS=.ok openings := hopenings
                have hspan := source_final_range_length proof finalMessage final openings hf ho hfinalMessage
                exact ⟨_,p,a,_,final,openings,hresume,h,hf,ho,hfinalMessage,hspan.1,hspan.2⟩

#print axioms source_tx2_success_same_final_view
end AspisR1S9Tx2SameFinalViewSpanV1
