import Port5Q1_Parsed
import R1LiteralMatchingFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_WordRead
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisV8R19.DuplexFrames
/-- The literal W reader, retaining the exact restored C1/C2 maps. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (data : MatchingSupport.Data AspisWideTower.WideExact)
    (read : LiteralMatchingData.read (typedRows parsed q tr)=some data) :
    ∃ common : LiteralOpeningView.View,
      LiteralOpeningView.read (typedRows parsed q tr)=some common ∧
      data.W=common.word := by
  obtain ⟨common,staged,row31,word,gamma,kappa,alpha0,alpha1,hc,hs,hr,hw,hg,hk,ha0,ha1,eq⟩ :=
    LiteralMatchingFacts.read_success_components _ data read
  exact ⟨common,hc,by rw [eq];rfl⟩
#print axioms value
end AspisR1.FJl_WordRead
end
