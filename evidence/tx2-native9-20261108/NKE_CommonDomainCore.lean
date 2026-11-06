import NKE_ResumeWidth
import NKE_Entered
set_option autoImplicit false
noncomputable section
namespace NKE_CommonDomainCore
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- Domains of the native geometry/pending call-entry windows. -/
def Holds (rr : NP6_StdModel.Reservation) : Event → Prop
 | .geometry queries next reply => next=10#usize ∧ reply=NJC_ClosedCalls.geometry queries next 22#usize
 | .pending weights reply => weights.val.length=64 ∧ reply=NJJ_Common.pending rr weights
 | _ => True
end NKE_CommonDomainCore
