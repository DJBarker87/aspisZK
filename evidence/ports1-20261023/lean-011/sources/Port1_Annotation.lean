import Port1_Driver
import VTop_Annotation

/-! The source backward-acceptance premise, now for a named constructed
source driver. No raw source/frozen2 join is assumed or asserted here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port1_Annotation
open Aeneas Aeneas.Std VTop_Stages VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4

theorem source_enrich (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (words : CanonicalCutEnrichedTranscript.Words) (i : Input) :
    Port1_Driver.rust adapter impl D hash (enrich words i) =
      Port1_Driver.rust adapter impl D hash i := rfl

/-- Exactly the backward law consumed by VTop_Annotation.two_pass. It holds
for every body/decoder dictionary, oracle, and annotation word collection. -/
theorem backward (adapter : AdapterRw.Ops) (impl : Implementation) {Hash : Type}
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) :
    ∀ words i H, (eval H (Port1_Driver.rust adapter impl D hash (enrich words i))).2 = true →
      (eval H (Port1_Driver.rust adapter impl D hash i)).2 = true := by
  intro words i H accepted
  rw [source_enrich] at accepted
  exact accepted

#print axioms source_enrich
#print axioms backward
end AspisR1.Port1_Annotation
end
