import NJF_FinishObserved
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJF_Root
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2 NIW_AlignFinishComposed

/-- Complete forward-instantiated pair/finish source capsule. Native credit is
conditional on the reviewed cut table and combined gate; it is never inferred
from compilation alone. All entered child clauses are discharged internally. -/
theorem finish (r : NP6_StdModel.Reservation) (loc : Locations) (proof : Slice U8)
 (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : NIG_FinishInput.Domain proof v p a) (port : PairPort) (afterOwner : Nat)
 (cut : NIW_AlignFinishPort.Cut p port afterOwner (NJF_FinishObserved.G r loc v p a).2.2) :
 let execution:=NJF_FinishObserved.G r loc v p a
 Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none=execution.1 ∧
 (∀ event∈execution.2.1,NIW_AlignFinishInvocation.Clause r event) ∧
 (∀ event∈execution.2.1,NIW_AlignFinishDomains.Inputs p v a event) ∧
 NIW_AlignFinishPrefix.Prefix execution.2.1 ∧
 NIW_AlignFinishPairCertificate.Bound r execution.2.2 ∧
 NIW_AlignFinishInfoEvent.HasPair execution ∧ NIW_AlignFinishInfoNew.HasNew p execution ∧
 NIW_AlignFinishPort.Bound r port execution.2.2 := by
 rw [NJF_FinishObserved.source r loc proof v p a domain] at cut ⊢
 exact NIW_AlignComposedRoot.source r loc proof v p a domain port afterOwner cut

#print finish
#print axioms finish
end AspisR1.NJF_Root
