import NFI_SingleTrace
import NFF_LoggedDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_SingleDomains
open Aeneas Aeneas.Std Result NEV_DotCarrier

/-- All native arithmetic domains are derived from the SAME traced slot
computation and its root g predicate. This supplies no physical-state witness. -/
theorem reached (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (tailOracle : NFF_ProductCall.Oracle) (tailLaw : NFF_ProductCall.Law tailOracle)
    (input : NFI_InnerCut.Input) (out : NE)
    (canonical : NEV_DotInputs.Canonical input.g)
    (run : (NFI_SingleTrace.run oracle tailOracle input).result=ok out) :
    ∃ p : NFE_NFC_MainPacket.Packet input.q input.g input.slot out,
      NFE_WrapperBridge.NativeDomains p := by
  exact NFF_LoggedDomains.one oracle law tailOracle tailLaw input.q input.g input.slot out canonical
    ((NFI_SingleTrace.erased oracle tailOracle input).symm.trans run)

#print axioms reached
end AspisR1.NFI_SingleDomains
end
