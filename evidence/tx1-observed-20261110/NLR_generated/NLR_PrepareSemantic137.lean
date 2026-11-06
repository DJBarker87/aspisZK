import NLR_RowSpec137
import NLJ_PrepareStep
import NLJ_RoundPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareSemantic137
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (Code run)
def configuration (base : Ops) (reservation : NP6_StdModel.Reservation) : NLJ_Prepare.Configuration :=
 ⟨base,IDa_Deployed.boundaries reservation,NP6_StdModel.calls reservation⟩
/-- SAME source digest/public through the existing canonical carrier maps. -/
def observedInput (reservation : NP6_StdModel.Reservation) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) : NLJ_Observed.Input Unit :=
 ⟨reservation,InstalledPreparation.retainedDigest i.digest,
  FirstComposition.toRetainedPublic i.publicValue,v.semantic,i.hash⟩
def convert : NLJ_Observed.Out Unit → core.result.Result (r1_semantic.Verified Unit) r1_wire.Error
 | .Ok sem => .Ok (S1SemanticCarrier.currentSem sem)
 | .Err e => .Err (S1SemanticCarrier.currentWireError e)
def reply : Result (NLJ_Observed.Out Unit) → Result (core.result.Result (r1_semantic.Verified Unit) r1_wire.Error)
 | .ok r => .ok (convert r) | .fail e => .fail e | .div => .div
/-- Exact installed137 source call AND its canonical carrier conversion.
No equality between incompatible current and retained carriers is assumed. -/
theorem installed (reservation : NP6_StdModel.Reservation) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) :
 S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
  (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) (IDa_Deployed.boundaries reservation))
  i.digest i.publicValue v.semantic i.hash =
 AspisR1PublicPreparation.PreparedHashCode.bind
  (S1SemanticCode.verify (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries reservation))
   (observedInput reservation i v).digest (observedInput reservation i v).publicValue
   v.semantic i.hash none) (fun r => pure (convert r)) := by
 rfl
/-- Exact child packet at the produced view;13831 is a verbatim(bf) caller
clause. It is not silently supplied, and no physical087 root is emitted. -/
theorem packet (native : NLR_Interface.Native137) (child137 : NLR_Interface.RowSpec_137 native)
 (reservation : NP6_StdModel.Reservation) (i : NLJ_Prepare.Input Unit)
 (v : verifier.View) (before : NLR_Interface.ExternalFrame)
 (domain : v.semantic.val.length=13831) :
 run (S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
  (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) (IDa_Deployed.boundaries reservation))
  i.digest i.publicValue v.semantic i.hash) =
 ((native (observedInput reservation i v) before).log,
  reply (native (observedInput reservation i v) before).reply) := by
 rw [installed,AuS1_Trace.run_bind]
 rw [(child137 (observedInput reservation i v) before domain).2.2.2]
 cases h : (native (observedInput reservation i v) before).reply <;>
  simp only [AuS1_Trace.continueRun,reply,AspisR1PublicPreparation.PreparedHashCode.run,List.append_nil]
 all_goals rfl
#print axioms installed
#print axioms packet
set_option pp.proofs false
#print packet
end AspisR1.NLR_PrepareSemantic137
end
