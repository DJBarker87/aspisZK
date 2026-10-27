import F3M_InactivePhysicalMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_InactiveRow28
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open MultiproofConeCanonical OraclePortCompactDraft

theorem decoded (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view))
    (p : Parsed) (wire : p.wire=bytesOf proof.val) :
    OpeningRecordCodec.decode .kappa (rowBytes p 28)=
      some (decode (toClaimE (retainedView view).inactive)) := by
  have raw := F3M_InactivePhysicalMeaning.source proof semantic y1 view accepted
  have encoded := FoldedLeafCodec.encodeWide_of_decode _ _ raw
  change OpeningRecordCodec.decode .kappa (framed (slice p.wire 7495 32))=_
  rw [wire,← encoded]
  exact OpeningRecordCodec.decode_encode (row:=.kappa) _

#print axioms decoded
end AspisR1.F3M_InactiveRow28
end
