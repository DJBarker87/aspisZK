import OraclePortConsumer
import OraclePortSelectedConsumerC6

/-! The exact recorded-log clean-model consumer with selected observation
checks. The extractor and its full recovered words are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCleanObservationsC6
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortExperiment OraclePortConsumer
open RawCutProverCompiler (Prover)
open RawRecordedOracleExtractionMassBin

def CheckedObservations (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat) : Type :=
  ∀ H : Bytes → State, ¬ collision Q (eval H (recorded D d P)) →
    FS2.accepts (eval H (original D d P)) →
    OraclePortSelectedConsumerC6.Checks (eval H (recorded D d P)).2.1.1
      (compiledRows D d P H)

def literal_acceptance (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (Q : Nat) (checks : CheckedObservations D d P Q) : CheckedAcceptance D d P Q :=
  fun H clean accepted => OraclePortSelectedConsumerC6.toLiteral (checks H clean accepted)

/-- Selected-observation replacement for OraclePortConsumer.clean_of_checks.
No equality of the candidate's full word annotations is required. -/
theorem clean_of_observations (D : LiteralByteProtocol.Decoder) (d : Decision)
    (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q) (hbudget : Budget d)
    (hcompletion : Completion D d P (Q+1161))
    (hchecks : CheckedObservations D d P (Q+1161)) :
    CleanAcceptedModel D (recorded D d P) (fun run => collision (Q+1161) run ∨
      hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1) :=
  OraclePortConsumer.clean_of_checks D d P Q hqueries hbudget hcompletion
    (literal_acceptance D d P (Q+1161) hchecks)

#print axioms literal_acceptance
#print axioms clean_of_observations
end AspisR1.OraclePortCleanObservationsC6
end
