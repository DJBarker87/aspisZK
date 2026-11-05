import NIW_AlignFinishComposedSource
import NIW_AlignFinishMatched
import NIW_AlignFinishPairCertificate
import NIW_AlignFinishInfoNew
import NIW_AlignFinishPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignComposedRoot
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

/-- SOURCE invocation capsule, not a whole-native row promotion. It has no
child-clause or endpoint-equality hypotheses. The remaining native projection
obligation is kept explicit in NIW_OPEN_EDGE.md, rather than inserted here. -/
theorem source (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (port : PairPort) (afterOwner : Nat)
 (cut : NIW_AlignFinishPort.Cut p port afterOwner (run r loc v p a).2.2) :
 let execution:=run r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 (∀ event∈execution.2.1,NIW_AlignFinishInvocation.Clause r event) ∧
 (∀ event∈execution.2.1,NIW_AlignFinishDomains.Inputs p v a event) ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NIW_AlignFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishInfoEvent.HasPair execution ∧ NIW_AlignFinishInfoNew.HasNew p execution ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 have history := NIW_AlignFinishPrefix.source r v p a
 rw [←NIW_AlignFinishMatched.events r loc proof v p a domain] at history
 exact ⟨NIW_AlignFinishComposedSource.source r loc proof v p a domain,
  NIW_AlignFinishMatched.clauses r loc proof v p a domain,
  NIW_AlignFinishMatched.domains r loc proof v p a domain,history,
  NIW_AlignFinishPairCertificate.source r loc proof v p a domain,
  NIW_AlignFinishInfoEvent.source r loc v p a,NIW_AlignFinishInfoNew.source r loc v p a,
  NIW_AlignFinishPort.source r loc proof v p a domain port afterOwner cut⟩

#print source
#print axioms source
end AspisR1.NIW_AlignComposedRoot
