import ARP_Interface
import Hiq_ByteSelection
import OraclePortCheckpointPreparedC5
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARQ_Observer
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment GExq_AccountExperiment MultiproofConeCanonical

/-- Total projection from the actual first-wrapper response. Missing or
malformed checkpoint fields have a total fallback, including on rejection.
No oracle, external successful execution or fresh query occurs here. -/
def project {A : Type} (out : Outcome A) :
    OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144) :=
  ((OraclePortCompactDraft.parse (submitted out.1).stored).getD ⟨(submitted out.1).stored,[]⟩,
    match out.2.1 with
    | .ok (.Ok (saved,_,_)) =>
      (OraclePortCheckpointPreparedC5.decodeQueries
        (OraclePortCompactDraft.slice (bytesOf saved.val) 320 88)).getD (fun _ => 0)
    | _ => fun _ => 0)

/-- Physical audit selector from the actual account outcome, fixed before H. -/
def select {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (id : S2W_ExtractionBoundary.Program) : Outcome A →
    R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  Hiq_ByteSelection.select (DrvC_Installation.sdk c) id

#print project
#print select
end AspisR1.ARQ_Observer
end
