import NJC_QueryOccurrence
import NIG_FinishInput
set_option autoImplicit false
noncomputable section
namespace NJR_FinishPrepared
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Precisely the Prepared-only portion of the finish domain. All fields come
from the SAME successful resume; success is an internal reached branch and is
not an additional positive-root input. No finish or child success is assumed. -/
theorem returned (r : Bool) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (freshP : NIL_StatePort.F.P) (freshA : NIL_StatePort.F.A)
 (run : NIL_FreshOps.resume r d ck proof pub .S2 hash=ok (.Ok (freshP,freshA))) :
 let p:=NIL_StatePort.prepared freshP
 p.variant=.S2 ∧ NBO_TailDomain.WideCanonical p.claim ∧
 (∀ i, i<2 → ∀ x,p.alpha.val[i]?=some x → NBO_TailDomain.WideCanonical x) ∧
 NBO_TailDomain.WideCanonical p.kappa ∧
 (∀ q∈p.semantic_alpha.val,NGW_NewInterface.CanonK q) ∧
 (∀ point∈p.z.val,NGW_NewInterface.CanonK point.x ∧ NGW_NewInterface.CanonK point.y) := by
 let p:=NIL_StatePort.prepared freshP
 let a:=NIL_StatePort.accumulator freshA
 have same : verifier.resumeWithOps (CheckpointBytes4Ops.ops r) d ck proof pub .S2 hash=
   ok (.Ok (p,a)) := by
  rw [←NIY_ResumePort.source,run]
  rfl
 have size:=NJC_QueryOccurrence.checkpoint_size r d ck proof pub hash freshP freshA run
 have dom:=NID_ResumeFields.returned r d ck proof pub hash p a size same
 refine ⟨dom.variant,NID_ResumeCallerDomain.wide p.claim dom.claim,?_,
  NID_ResumeCallerDomain.wide p.kappa dom.kappa,?_,?_⟩
 · intro i _ x hx
   exact NID_ResumeCallerDomain.wide x (dom.alpha x (List.mem_of_getElem? hx))
 · intro q hq
   have h:=dom.semantic q hq
   exact ⟨⟨h.1,h.2.1⟩,h.2.2⟩
 · intro point hp
   have h:=dom.coordinates point hp
   exact ⟨⟨⟨h.1.1,h.1.2.1⟩,h.1.2.2⟩,⟨⟨h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

#print axioms returned
end NJR_FinishPrepared
