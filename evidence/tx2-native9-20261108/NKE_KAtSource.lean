import NKE_ResumeClauses6
import NJJ_ResumeDomains
set_option autoImplicit false
noncomputable section
namespace NKE_KAtSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved NIL_Carriers
theorem total (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H)
 (r : verifier.Reader) (reply : Result (core.result.Result K verifier.Error × verifier.Reader))
 (entered : Event.k r reply∈(run reservation d ck proof pub v hash).events) :
 reply=outer (fun x=>(unInner unK x.1,unReader x.2))
  (do let (b,out) ← CheckpointBytes3Reader.raw 16#usize (reader r)
      ok (NJC_ReaderResults.naturalK b,out)) := by
 have clause := NKE_ResumeClauses.run reservation d ck proof pub v hash (.k r reply) entered
 change reply=NIL_FreshOps.readK r at clause
 rw [clause,NIL_FreshOps.readK,NJC_ReaderResults.k]

/-- SAME occurrence, full canonical rejection plus reader frame. The literal
site domain still requires installation across the caller prefix; this local
law is not a new positive-root premise or a completed parent. -/
theorem bounded (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H)
 (site : NJJ_ResumeDomains.KSite) (r : verifier.Reader)
 (reply : Result (core.result.Result K verifier.Error × verifier.Reader))
 (entered : Event.k r reply∈(run reservation d ck proof pub v hash).events)
 (length : r.bytes.val.length=1768) (cursor : r.at.val=NJJ_ResumeDomains.kOffset site) :
 ∃ b : Array U8 16#usize, ∃ out : AspisR1Stage2.verifier.Reader,
 b.val=(r.bytes.val.drop r.at.val).take 16 ∧ out.at.val=r.at.val+16 ∧
 out.bytes=r.bytes ∧ reply=ok (unInner unK (NJC_ReaderResults.naturalK b),unReader out) := by
 have clause := NKE_ResumeClauses.run reservation d ck proof pub v hash (.k r reply) entered
 change reply=NIL_FreshOps.readK r at clause
 obtain ⟨b,out,bytes,advance,frame,result⟩ := NJJ_ResumeDomains.k site (reader r) length cursor
 refine ⟨b,out,bytes,advance,frame,?_⟩
 rw [clause,NIL_FreshOps.readK,result]
 rfl
#print axioms total
#print axioms bounded
end NKE_KAtSource
