import DrvC_Implementation
import Hiq_AccountLoss
import Hiq_StoredTransport
import Hiq_ExactMargin
import Hiq_BindingFailure
import Hiq_AccountEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_AccountTransport
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))

/-- Exact remaining L159 interface. The complete accepted-run equality outside
the one charged event remains an explicit, UNINSTANTIATED source obligation. -/
attribute [local irreducible] DrvC_Implementation.driver Hiq_DrvRecorded.program

theorem with_runtime_join (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (runtime : OraclePortRuntimeBindingC7.Runtime)
    (binding : ∀ H run, (eval H runtime).2 = some run → run.2.2 = true →
      run = eval H (OraclePortRuntimeBindingC7.annotatedWith D (DrvC_Implementation.driver c)
        (OraclePortStoredAdmissionC4.canon P)) ∨
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
        (eval H (Hiq_DrvRecorded.program c hashv copy allocator id adversary chooseSecond project))) :
    OraclePortRuntimeBindingC7.deployedFailure runtime ≤
      lazyMean (OraclePortRuntimeBindingC7.annotatedWith D (DrvC_Implementation.driver c)
        (OraclePortStoredAdmissionC4.canon P)) emptyTable
        (fun v => RawRecordedOracleExtractionMassBin.failureMass (OraclePortStoredExperimentC4.view v)) +
      Hiq_Numeric.accountLoss (Q0+Q1) := by
  have transport := Hiq_StoredTransport.transport (A := View Bytes State (GExq_AccountExperiment.Outcome A)) D (DrvC_Implementation.driver c) P runtime
    (Hiq_DrvRecorded.program c hashv copy allocator id adversary chooseSecond project)
    (fun v => BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) v) binding
  exact transport.trans (add_le_add_left
    (Hiq_AccountLoss.one_loss c hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound project) _)

#print axioms with_runtime_join
set_option pp.proofs false in
#print with_runtime_join
end AspisR1.Hiq_AccountTransport
end
