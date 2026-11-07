import NLR_PrepareSemantic137
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLR_PrepareStep137
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode (run)
def post (i : NLJ_Prepare.Input Unit) (logical : alloc.vec.Vec U8) (v : verifier.View) :
 Result (NLJ_Observed.Out Unit) → Result (NLJ_Prepare.Post Unit)
 | .ok r => .ok (.inr ⟨i,.mapSemantic logical v (NLR_PrepareSemantic137.convert r)⟩)
 | .fail e => .fail e
 | .div => .div
/-- Exact087 semantic occurrence with its137 packet at SAME physical source
arguments. Conditional(bd) intermediate; no root or native cut is inferred. -/
theorem semantic_step (native : NLR_Interface.Native137)
 (child137 : NLR_Interface.RowSpec_137 native) (base : Ops)
 (reservation : NP6_StdModel.Reservation) (i : NLJ_Prepare.Input Unit)
 (logical : alloc.vec.Vec U8) (v : verifier.View)
 (before : NLR_Interface.ExternalFrame) (domain : v.semantic.val.length=13831) :
 let call := NLR_PrepareSemantic137.observedInput reservation i v
 (native call before).afterInput=call ∧ (native call before).afterFrame=before ∧
 run (NLJ_Prepare.step (NLR_PrepareSemantic137.configuration base reservation)
  ⟨i,.semantic logical v⟩) =
 ((native call before).log,post i logical v (native call before).reply) := by
 let call := NLR_PrepareSemantic137.observedInput reservation i v
 have full := child137 call before domain
 refine ⟨full.1,full.2.1,?_⟩
 change run (AspisR1PublicPreparation.PreparedHashCode.bind
  (S1SemanticCodeInstallation.code AspisS1ExtractedRoundChildren.children
   (ClaimsUnrolledFinish.install (NP6_StdModel.calls reservation) (IDa_Deployed.boundaries reservation))
   i.digest i.publicValue v.semantic i.hash) _) = _
 rw [AuS1_Trace.run_bind,NLR_PrepareSemantic137.packet native child137 reservation i v before domain]
 cases h : (native call before).reply <;>
  simp only [AuS1_Trace.continueRun,NLR_PrepareSemantic137.reply,post,Pure.pure,NLJ_Prepare.advance,
   AspisR1PublicPreparation.PreparedHashCode.run,List.append_nil]
 all_goals rfl
#print axioms semantic_step
set_option pp.proofs false
#print semantic_step
end AspisR1.NLR_PrepareStep137
end
