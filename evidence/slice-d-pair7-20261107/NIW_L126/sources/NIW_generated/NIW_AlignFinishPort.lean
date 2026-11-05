import NIW_AlignFinishPairCertificate
import NIT_FinishComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishPort
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

def Cut (p : verifier.Prepared) (log : PairPort) (afterOwner : Nat) : Option PairInfo → Prop
 | none => True
 | some info => match info.native.1 with
   | fail _ => True
   | div => True
   | ok reply => cutPairPort info.owner.address info.alpha.address info.message.address p log
     (NIT_ErrorTransport.reply reply) afterOwner

def Bound (r : NP6_StdModel.Reservation) (log : PairPort) : Option PairInfo → Prop
 | none => True
 | some info =>
   let call := FIo_Install.pair r info.owner.value info.alpha.value.to_slice info.message.value info.kappa
   match info.native.1 with
   | fail err => call=fail err
   | div => call=div
   | ok reply => log.reply=NIT_ErrorTransport.reply reply ∧ call=ok log.reply ∧ replyCanonical log.reply

/-- Only the parent's reviewed return cut is supplied. The actual nested pair
certificate and its domain are produced inside the root, for every arm of the
SAME source invocation. Unentered/aborting pair calls need no returning record. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (log : PairPort) (afterOwner : Nat)
 (cut : Cut p log afterOwner (run r loc v p a).2.2) : Bound r log (run r loc v p a).2.2 := by
 have linked := NIW_AlignFinishPairCertificate.source r loc proof v p a domain
 cases observed : (run r loc v p a).2.2 with
 | none => trivial
 | some info =>
  simp only [observed,NIW_AlignFinishPairCertificate.Bound] at linked
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
end AspisR1.NIW_AlignFinishPort
