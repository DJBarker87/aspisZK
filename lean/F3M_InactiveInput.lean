import F3M_InactiveRow28
import F3M_MatchingInactive
import PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_InactiveInput
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open MultiproofConeCanonical OraclePortCompactDraft

theorem c0 (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1=ok (.Ok view))
    (p : Parsed) (wire : p.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (tr : RawCutTranscriptRun.ErasedPrefix)
    (aligned : Aligned p tr) (i : RecordedBinaryExperimentBin.SourceInputs)
    (found : OraclePortStoredDecisionDraftC4.input p q tr=some i) :
    i.data.c0=decode (toClaimE (retainedView view).inactive) := by
  have numeric := F3M_InactiveRow28.decoded proof semantic y1 view accepted p wire
  have source := PAln_AlignedRead.readAt p q tr aligned 28 (by decide) (by decide)
    (OpeningRecordCodec.decode .kappa) _ numeric
  have target := F3M_MatchingInactive.read _ i.data
    (OraclePortStoredDecisionDraftC4.input_fields p q tr i found).2
  exact Option.some.inj (target.symm.trans source)

#print axioms c0
end AspisR1.F3M_InactiveInput
end
