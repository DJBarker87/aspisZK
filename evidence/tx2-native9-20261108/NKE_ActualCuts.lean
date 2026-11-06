import NKE_CommonDomain
import NKE_CommonNative
import NKE_GeometryCuts
set_option autoImplicit false
noncomputable section
namespace NKE_ActualCuts
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- M03's SAME-weight row cuts at the actual C06 occurrence. Allocation failure
is retained and no native output vector or successful allocation is assumed. -/
theorem pending (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (weights : Slice aspis_core.field.QM31) (reply : R verifier.BatchedWeights)
 (entered : Event.pending weights reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 ∃ states : Nat → alloc.vec.Vec Port3_NativePendingBody.Row,
 reply=(match rr with
 | .Ok () => ok (.Ok (⟨states 64,0#usize⟩ : verifier.BatchedWeights))
 | .Err _ => ok (.Err .Allocation)) ∧
 ∀ i,i<64 → NJR_Cuts.pending weights (states i) (states (i+1)) i (i+1) := by
 obtain ⟨width,source⟩ := NKE_CommonDomain.source wr rr merkle finish d pub proof ck hash
  (.pending weights reply) entered
 let before := NKE_CommonNative.zeros weights
 have rawWidth : before.val.length=64 := by
  simpa only [before,NKE_CommonNative.zeros,List.length_replicate] using width
 refine ⟨NKE_PendingNative.states weights before,?_,?_⟩
 · rw [source]
   exact NKE_PendingNative.source rr weights before width rawWidth
 · intro i hi
   exact NKE_PendingNative.cut weights before width rawWidth i hi

/-- C05's fixed12-cell domain is discharged on the SAME returned geometry. -/
theorem geometry (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (queries : Array U32 22#usize) (next : Usize) (out : verifier.QueryGeometry)
 (entered : Event.geometry queries next (ok (.Ok out))∈
  (run wr rr merkle finish d pub proof ck hash none).events) :
 next=10#usize ∧ out.start=10#usize ∧ out.inverses.val.length=12 ∧ out.line_z.val.length=12 := by
 obtain ⟨start,source⟩ := NKE_CommonDomain.source wr rr merkle finish d pub proof ck hash
  (.geometry queries next (ok (.Ok out))) entered
 refine ⟨start,?_⟩
 subst next
 exact NKE_GeometryDomain.returned queries out source.symm

/-- Apply all THREE native geometry windows to this SAME occurrence, including
full vectors and their frames. A successful child is an internal branch only. -/
theorem geometry_post (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (queries : Array U32 22#usize) (next : Usize) (out native : verifier.QueryGeometry)
 (entered : Event.geometry queries next (ok (.Ok out))∈
  (run wr rr merkle finish d pub proof ck hash none).events)
 (cut : NKE_GeometryCuts.Cut out native) : native=out := by
 obtain ⟨_,_,inverseSize,lineSize⟩ := geometry wr rr merkle finish d pub proof ck hash queries next out entered
 exact NKE_GeometryCuts.same out native inverseSize lineSize cut
#print axioms pending
#print axioms geometry
#print axioms geometry_post
end NKE_ActualCuts
