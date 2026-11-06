import NJU_WeakFinishPairCertificate
import NIW_AlignFinishPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakFinishPort
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed
open NIW_AlignFinishPort
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NJU_FinishInput.Holds proof v p a) (log : PairPort) (afterOwner : Nat)
 (cut : Cut p log afterOwner (run r loc v p a).2.2) : Bound r log (run r loc v p a).2.2 := by
 have linked := NJU_WeakFinishPairCertificate.source r loc proof v p a domain
 cases observed : (run r loc v p a).2.2 with
 | none => trivial
 | some info =>
  simp only [observed,NJU_WeakFinishPairCertificate.Bound] at linked
  rcases linked with ⟨provenance,caller,certificate,native,canonical⟩
  cases result : info.native.1 with
  | fail err => simpa only [Bound,observed,result,NIT_ErrorTransport.full] using native
  | div => simpa only [Bound,observed,result,NIT_ErrorTransport.full] using native
  | ok reply =>
   simp only [Cut,observed,result] at cut
   have same := (NIT_FinishComposition.pair_port info.owner.address info.alpha.address info.message.address
    p log _ afterOwner cut).symm
   have canon : replyCanonical (NIT_ErrorTransport.reply reply) := by
    apply NIT_PortInstantiation.canonical_reply
    simpa only [result] using canonical
   simp only [Bound,observed,result]
   refine ⟨same,?_,same.symm ▸ canon⟩
   simpa only [result,NIT_ErrorTransport.full,←same] using native

#print source
#print axioms source
end AspisR1.NJU_WeakFinishPort
