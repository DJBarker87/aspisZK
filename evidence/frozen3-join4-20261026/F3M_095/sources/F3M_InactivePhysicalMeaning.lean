import F3M_InactiveReader
import F3K_InactivePhysical
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_InactivePhysicalMeaning
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open MultiproofConeCanonical OraclePortCompactDraft

theorem source (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view)) :
    FoldedLeafCodec.decodeWide (slice (bytesOf proof.val) 7495 32)=
      some (decode (toClaimE (retainedView view).inactive)) := by
  obtain ⟨selected,call,same⟩ := PAln_ViewCuts.current proof semantic y1 view accepted
  obtain ⟨input,value,physical,parsed,carrier,len⟩ := PAln_InactiveDecode.physical
    proof semantic y1 selected call
  have prep : (retainedView view).inactive=F3K_WideEncoding.prepFromParsed value := by
    rw [← same]
    change AspisR1SelectedWideViewV1.prepCarrier selected.inactive=_
    rw [← carrier]
    rfl
  rw [prep,← physical]
  exact F3M_InactiveReader.parsed input value parsed

#print axioms source
end AspisR1.F3M_InactivePhysicalMeaning
end
