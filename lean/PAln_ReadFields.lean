import PAln_Carrier
import PAln_MatchingFacts
import PAln_Accepted
import PAln_Bootstrap
import PAln_InactiveDecode
import PAln_OutputFields
import PAln_Log
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_ReadFields
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames RawCutTranscriptRun

theorem alpha1 (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (data : MatchingSupport.Data OraclePortCheckpointAbiC5.E)
    (value : LiteralTranscript.E)
    (read : LiteralMatchingData.read (typedRows p q tr)=some data)
    (challenge : LiteralChallengeRead.ordinaryAt (typedRows p q tr) 30=some value) :
    data.alpha1=value := by
  obtain ⟨common,staged,row31,word,gamma,kappa,a0,a1,view,stages,last,v,g,k,a,b,same⟩ :=
    PAln_MatchingFacts.read_success_components _ data read
  have eq : a1=value := Option.some.inj (b.symm.trans challenge)
  rw [same]
  exact eq

#print axioms alpha1
end AspisR1.PAln_ReadFields
end

#print axioms AspisR1.PSem_Accepted.accepted_pair_claims_semantic_rows
#print axioms AspisR1.PAln_Accepted.accepted_pair_selected_physical_rows
#print axioms AspisR1.PAln_Bootstrap.on_run
#print axioms AspisR1.PAln_JoinedFacts.on_run
#print axioms AspisR1.PAln_CurrentPhysical.second
#print axioms AspisR1.PAln_InactiveDecode.physical
#print axioms AspisR1.PAln_OutputFields.from_double
#print axioms AspisR1.PAln_Log.source_replay
#print AspisR1.Tx1Q_Endpoint.WhenBound
#print AspisR1.PAln_JoinedFacts.Facts
#print AspisR1.PSem_Accepted.accepted_pair_claims_semantic_rows
#print AspisR1.PAln_Accepted.accepted_pair_selected_physical_rows
