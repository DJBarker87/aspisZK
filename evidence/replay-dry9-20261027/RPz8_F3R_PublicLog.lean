import RPz7_F3J_InitialLog
import RPz7_F3K_CodeStep
import RPz7_S1SemanticCodePublicTranscriptExactV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3R_PublicLog
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode SourceGlobalOracleInitial
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem log {Hash : Type} {D : aspis_core.Digest32 Hash}
    {pub : pool_v1.pair_forest_semantic_terminal.r0.Public}
    {root : Array U8 32#usize} {before : r1_wire.SemanticTranscript Hash}
    (init : PublicInitCall D pub root before) :
    observe (run (S1SemanticCode.publicTranscript D pub before.hash root)).1=[initPair init] := by
  unfold S1SemanticCode.publicTranscript
  rw [init.serialized]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  unfold S1SemanticCode.newTranscript
  try simp only
  rw [init.converted]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  try simp only
  simp only [lift]
  erw [F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,F3K_CodeStep.pure_step,
    F3K_CodeStep.pure_step,F3K_CodeStep.pure_step]
  erw [F3K_CodeStep.digest_success _ _ _ _ init.digest]
  rfl

#print axioms log
end AspisR1.F3R_PublicLog
end
