import R1Z.PV_RunJoin_ActualRunSources59
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ActualAlpha1Trace60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

theorem source (phase : Phase) (w : aspis_core.field.wide_exact.WideExact)
    (success : PV_RunJoin_ActualRunSources59.alpha1 phase=ok (some w)) :
    ∃ (tr next : host_transcript.Transcript aspis_core.digest.LegacyHashFn) (payload : Slice U8),
      host_transcript.Transcript.scalar aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        tr 30#u8 payload false=ok (w,next) := by
  unfold PV_RunJoin_ActualRunSources59.alpha1 at success
  obtain ⟨preparedStatus,_,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  cases preparedStatus with
  | Err e => cases h
  | Ok prepared =>
    obtain ⟨publicationStatus,_,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
    cases publicationStatus with
    | Err e => cases h
    | Ok publication =>
      simp only [lift,bind_tc_ok] at h
      obtain ⟨first,_,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      obtain ⟨payload,_,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      obtain ⟨pair,hs,h⟩ := PV_RunJoin_ResultPost.bind_eq_ok h
      rcases pair with ⟨a,next⟩
      dsimp only [Aeneas.Std.uncurry] at h
      cases h
      exact ⟨prepared.transcript,next,alloc.vec.Vec.deref payload,hs⟩

#print axioms source
end R1Z.PV_RunJoin_ActualAlpha1Trace60
