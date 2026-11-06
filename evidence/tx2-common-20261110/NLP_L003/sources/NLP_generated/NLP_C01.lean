import NLP_ResumeInstall
import NLB_C01
import NLB_C01Domain
set_option autoImplicit false
noncomputable section
namespace NLP_C01
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- At C01, the two incoming extents are transported by literal SAME inputs. -/
theorem native_scope (wr rr : NP6_StdModel.Reservation) (merkle : Merkle) (finish : Finish)
 {H : Type} (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (proofLength : proof.val.length=57607) (publicLength : pub.val.length≤1880)
 (c pr pu : Slice U8) (reply : R (verifier.Prepared × verifier.Accumulator))
 (entered : Event.resume c pr pu reply∈(run wr rr merkle finish d pub proof ck hash none).events) :
 NKU_CallerScope.Inputs (NKU.initial ⟨c,pr,pu,wr⟩).frame := by
 obtain ⟨hc,hpr,hpu⟩:=NLB_C01Domain.source wr rr merkle finish d pub proof ck hash _ entered
 subst c; subst pr; subst pu
 exact NLP_ResumeInstall.scope wr ck proof pub proofLength publicLength
/-- C01 step consumes the actual NKU root, without a packet hypothesis. -/
theorem step (wr rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (nativeMerkle modelMerkle : Merkle) {H : Type}
 (d : aspis_core.digest.Digest32 H) (pub proof ck : Slice U8) (hash : H)
 (c pr pu : Slice U8) (reply : R (verifier.Prepared × verifier.Accumulator))
 (entered : Event.resume c pr pu reply∈(run wr rr modelMerkle (NLB_Parent.finish fr) d pub proof ck hash none).events) :
 NLB_Parent.window rr fr loc (NLB_ResumePacket.action NLP_ResumeInstall.native wr) nativeMerkle d hash
  (.resume c pr pu reply)=.resume c pr pu reply :=
 NLB_Parent.C01_step wr rr fr loc (NLB_ResumePacket.action NLP_ResumeInstall.native wr) nativeMerkle modelMerkle
 d pub proof ck hash c pr pu reply entered (NLP_ResumeInstall.action wr d c pr pu hash)
#print native_scope
#print step
#print axioms native_scope
#print axioms step
end NLP_C01
