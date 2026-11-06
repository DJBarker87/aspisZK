import NKE_ResumeClauses6
import NJJ_ResumeDomains
set_option autoImplicit false
noncomputable section
namespace NKE_RawAtSource
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved NIL_Carriers
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (ck proof pub : Slice U8)
 (v : transport.Variant) (hash : H)
 (n : Usize) (r : verifier.Reader) (reply : Result (Array U8 n × verifier.Reader))
 (entered : Event.raw n r reply∈(run reservation d ck proof pub v hash).events)
 (bound : r.at.val+n.val≤r.bytes.val.length) :
 ∃ b : Array U8 n, ∃ out : verifier.Reader,
 reply=ok (b,out) ∧ b.val=(r.bytes.val.drop r.at.val).take n.val ∧
 out.at.val=r.at.val+n.val ∧ out.bytes=r.bytes := by
 have clause := NKE_ResumeClauses.run reservation d ck proof pub v hash (.raw n r reply) entered
 change reply=NJC_ConcreteUnwrap.raw n r at clause
 obtain ⟨b,out,result,bytes,cursor,frame⟩ := NJC_ConcreteUnwrap.bounded n r bound
 exact ⟨b,out,clause.trans result,bytes,cursor,frame⟩
#print axioms source
end NKE_RawAtSource
