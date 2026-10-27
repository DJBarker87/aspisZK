import F3L_SamplerMessages
import F3L_EraseIndex
import PAln_AlignedRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_AlignedMessages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
/-- Alignment of the actual completed sampler fixes every physical proof
message through row32, including the identical source-root bytes. -/
theorem value (H : Bytes → State) (pf : RawCutProverCompiler.Proof)
    (pub : LiteralTranscript.Public) (p : Parsed) (root : State)
    (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (rootBytes : bytes root=root0 p)
    (aligned : Aligned p (LiteralTranscript.erasePrefix
      (eval H (F3J_SamplerRun.program pf 0 33 (FS.emptyPrefix pub))).2)) :
    ∀ row,row<33 → LiteralTranscript.erase (pf row)=
      LiteralTranscript.erase (F3J_InputRows.proof p root w bound row) := by
  intro row below
  obtain ⟨challenge,called⟩:=F3L_SamplerMessages.entry H pf pub 33 row below
  have erased:=F3L_EraseIndex.entry _ row (pf row) challenge called
  rw [F3J_InputRows.erased]
  by_cases zero : row=0
  · subst row
    obtain ⟨r,c,initial,bytesEq⟩:=aligned.2.2.2.1
    have same:=(Prod.mk.inj (Option.some.inj (erased.symm.trans initial))).1
    have rootSame : r=root := AspisV8R19.UniformStateFirstHit.bytes_injective (bytesEq.trans rootBytes.symm)
    rw [if_pos rfl]
    simpa only [rootSame] using same
  · obtain ⟨b,c,slot,bytesEq⟩:=aligned.2.2.2.2 row (by omega) below
    have same:=(Prod.mk.inj (Option.some.inj (erased.symm.trans slot))).1
    rw [if_neg zero]
    exact same.trans (congrArg TranscriptView.Message.payload (Subtype.ext bytesEq))
#print axioms value
end AspisR1.FJq_AlignedMessages
end
