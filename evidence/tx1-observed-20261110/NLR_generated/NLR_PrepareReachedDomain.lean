import NLR_PrepareSemantic137
import NHL_PrepareDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareReachedDomain
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The existing CLOSED buffer-prefix model supplies137's OWN extent clause
at SAME view. Native admission of this reached prefix is still087's duty. -/
theorem semantic_extent (base : Ops) (reserved : Bool)
 (i : NLJ_Prepare.Input Unit) (v : verifier.View)
 (proofSize : i.proof.val.length=57607)
 (reached : NHL_PrepareModel.Reaches base reserved i.digest i.proof v) :
 v.semantic.val.length=13831 :=
 (NHL_PrepareDomain.reached base reserved i.digest i.proof v proofSize reached).2.1
/-- Full137 packet consumed on SAME digest/public/hash/produced semantic,
with the extent clause discharged from the SAME reached prefix. This is an
intermediate(bd) theorem: child137 and native087 prefix are not installed. -/
theorem semantic_packet (native : NLR_Interface.Native137)
 (child137 : NLR_Interface.RowSpec_137 native) (base : Ops) (reserved : Bool)
 (reservation : NP6_StdModel.Reservation) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (before : NLR_Interface.ExternalFrame)
 (proofSize : i.proof.val.length=57607)
 (reached : NHL_PrepareModel.Reaches base reserved i.digest i.proof v) :
 AspisR1PublicPreparation.PreparedHashCode.run
  (S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
   (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) (IDa_Deployed.boundaries reservation))
   i.digest i.publicValue v.semantic i.hash) =
 ((native (NLR_PrepareSemantic137.observedInput reservation i v) before).log,
  NLR_PrepareSemantic137.reply (native (NLR_PrepareSemantic137.observedInput reservation i v) before).reply) :=
 NLR_PrepareSemantic137.packet native child137 reservation i v before
  (semantic_extent base reserved i v proofSize reached)
#print axioms semantic_extent
#print axioms semantic_packet
set_option pp.proofs false
#print semantic_packet
end AspisR1.NLR_PrepareReachedDomain
end
