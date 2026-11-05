import NIW_AlignFinishComposedLog
import NIW_AlignFinishDomains
import NIW_AlignFinishPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinishMatched
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

theorem events (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 (run r loc v p a).2.1=(NIW_AlignFinishExecution.run r v p a).2 :=
 congrArg Prod.snd (NIW_AlignFinishComposedLog.source r loc proof v p a domain)

theorem clauses (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 ∀ event∈(run r loc v p a).2.1,NIW_AlignFinishInvocation.Clause r event := by
 rw [events r loc proof v p a domain]
 exact NIW_AlignFinishInvocation.clauses r proof v p a domain

theorem domains (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) :
 ∀ event∈(run r loc v p a).2.1,NIW_AlignFinishDomains.Inputs p v a event := by
 rw [events r loc proof v p a domain]
 exact NIW_AlignFinishDomains.all r proof v p a domain

theorem no_suffix (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a)
 (before : List Event) (event : Event) (after : List Event)
 (atEvent : (run r loc v p a).2.1=before++event::after)
 (aborted : ¬NIW_AlignFinishPrefix.Continues event) : after=[] := by
 have history := NIW_AlignFinishPrefix.source r v p a
 rw [←events r loc proof v p a domain] at history
 exact NIW_AlignFinishPrefix.no_suffix _ history before event after atEvent aborted

#print axioms events
#print axioms clauses
#print axioms domains
#print axioms no_suffix
end AspisR1.NIW_AlignFinishMatched
