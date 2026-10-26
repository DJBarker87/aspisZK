import SCJ_OrderedTransport
import SCF_Charge
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_AccountProjection
open FS FS2.Duplex
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment
/-- The requested implication on the TWO ACTUAL recorder carriers, consuming
SCF's original FULL-log charge with no extra loss. Only inclusion and causal
first-occurrence preservation remain inputs. Neither is silently inferred
from a shared oracle or independently selected physical audit bytes. -/
theorem event_implies {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (sourceSelect : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (H : Bytes → State) :
    let small := eval H (Hiq_RecordedJoint.program
      (F3X_Account.program c hashv (submission a)) F3X_Projection.project sourceSelect)
    let full := eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a) project select)
    (∀ addr, Read small.1 addr → Read full.1 addr) →
    (∀ b addr, Read small.1 addr → Before small.1 b addr → Before full.1 b addr) →
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) small →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) full := by
  dsimp only
  intro reads order
  apply SCJ_Projection.event_implies SelectedTranscriptParams.params.iv (Q0+Q1+2965) H
  · exact FS.eval_consistent H _
  · exact FS.eval_consistent H _
  · exact reads
  · exact order
  · exact (SCF_Charge.charged c hashv copy allocator id a Q0 Q1 prefixBound choiceBound project select).2.1 H

#print axioms event_implies
end AspisR1.SCJ_AccountProjection
end
