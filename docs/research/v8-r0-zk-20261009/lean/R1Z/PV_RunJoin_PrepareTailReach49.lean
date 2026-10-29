import R1Z.PV_RunJoin_PrepareMaterialContext49
import R1Z.PV_RunJoin_ResultPost
import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PrepareTailReach49
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
abbrev W := aspis_core.field.wide_exact.WideExact
set_option allowUnsafeReducibility true in
attribute [local irreducible] ProverRwP6BoundaryInstall.selected
attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (variant : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (backend : prover.Backend) (sem : host_semantic.BuiltSemantics aspis_core.digest.LegacyHashFn)
    (out : prover.PreparedOpening)
    (h : @prover.prepare_opening (types base) (selected base heap box ops) variant hash backend sem=ok (.Ok out)) :
    ∃ (tr0 tr1 tr2 : host_transcript.Transcript aspis_core.digest.LegacyHashFn)
      (claim : alloc.vec.Vec U8) (g inactive k : W) (ib : Array U8 32#usize) (q w : alloc.vec.Vec W),
      @host_transcript.Transcript.scalar (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        tr0 27#u8 (alloc.vec.Vec.deref claim) true=ok (g,tr1) ∧
      @host_transcript.Transcript.scalar (types base) (selected base heap box ops) _
        (@aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 (types base) (selected base heap box ops))
        tr1 28#u8 (Array.to_slice ib) false=ok (k,tr2) ∧
      @PV_RunJoin_PrepareTail48.run (types base) (selected base heap box ops) variant hash backend sem
        tr2 claim g inactive k (alloc.vec.Vec.deref q) (alloc.vec.Vec.deref w)=ok (.Ok out) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  rw [PV_RunJoin_PrepareOperations47.source,PV_RunJoin_PrepareClaimContext48.source,
    PV_RunJoin_PrepareMaterialContext49.source] at h
  unfold PV_RunJoin_PrepareMaterialContext49.run at h
  obtain ⟨b,hb,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
  cases b with
  | true => cases h
  | false =>
    simp only [Bool.false_eq_true,if_false] at h
    obtain ⟨coeff,hcoeff,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨point,hpoint,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨x,hx,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨y,hy,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨claim,hclaim,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨state,hstate,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨tr0,htr0,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨⟨g,tr1⟩,hg,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    dsimp only [Aeneas.Std.uncurry] at h
    obtain ⟨q,hq,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    obtain ⟨r,hr,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    cases r with
    | Err e =>
      change (ok (core.result.Result.Err e) : Result (core.result.Result prover.PreparedOpening verifier.Error))=ok (.Ok out) at h
      cases h
    | Ok weight =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
      obtain ⟨inactive,hi,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      obtain ⟨ib,hib,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      simp only [lift,bind_tc_ok] at h
      obtain ⟨⟨k,tr2⟩,hk,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      dsimp only [Aeneas.Std.uncurry] at h
      obtain ⟨rmat,hrmat,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      cases rmat with
      | Err e =>
        change (ok (core.result.Result.Err e) : Result (core.result.Result prover.PreparedOpening verifier.Error))=ok (.Ok out) at h
        cases h
      | Ok w =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at h
        exact ⟨tr0,tr1,tr2,claim,g,inactive,k,ib,q,w,hg,hk,h⟩
#print axioms complete
end R1Z.PV_RunJoin_PrepareTailReach49
