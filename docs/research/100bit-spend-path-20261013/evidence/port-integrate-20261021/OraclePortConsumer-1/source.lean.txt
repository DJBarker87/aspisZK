import OraclePortCleanModel

/-! Generalized binary consumer. The remaining decoder-completion and
collision-conditioned checked-acceptance premises are displayed separately. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortConsumer
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortExperiment
open RawCutProverCompiler (Prover RunView)
open RawRecordedOracleExtractionMassBin
abbrev dec := RecordedBinaryExperimentBin.dec
abbrev collision := RecordedBinaryExperimentBin.binaryCollision

abbrev compiledRows (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (H : Bytes → State) :=
  ((LiteralByteProtocol.protocol D).transcript H
    (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 33).rounds

/-- The exact LazyInj.decodes statement at the new program; no terminal
Merkle query is asserted to belong to the legacy address language. -/
def Completion (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ collision Q (eval H (recorded D dO P)) →
    FS2.accepts (eval H (recorded D dO P)) →
    ∀ n a, n < (LiteralByteProtocol.protocol D).r →
      firstCell ((LiteralByteProtocol.protocol D).chain H
        (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable (eval H (recorded D dO P)).1 a) =
        some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (recorded D dO P)).1 a) own pend
          (tableBefore emptyTable (eval H (recorded D dO P)).1 a) =
        some ((LiteralByteProtocol.protocol D).transcript H
            (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n,
          (LiteralByteProtocol.protocol D).msg (eval H (recorded D dO P)).2.1.2 n,
          (LiteralByteProtocol.protocol D).chal H
            (eval H (recorded D dO P)).2.1.1 (eval H (recorded D dO P)).2.1.2 n)

/-- Data-producing checks, guarded by the same binary collision event. -/
def CheckedAcceptance (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (Q : Nat) : Type :=
  ∀ H : Bytes → State, ¬ collision Q (eval H (recorded D dO P)) →
    FS2.accepts (eval H (original D dO P)) →
    LiteralAcceptanceTerminal.Checks (eval H (recorded D dO P)).2.1.1
      (compiledRows D dO P H)

def injection (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover)
    (Q : Nat) (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO) (hcompletion : Completion D dO P (Q + 1161)) :
    AcceptedAdaptiveFiatShamir.LazyInj (LiteralByteProtocol.protocol D) dec
      (compiled D dO P) (verifier D dO) BinCombinedMerkleCollision.kappa (Q + 1161) :=
  { Coll := collision (Q + 1161)
    mass := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
      (Q + 1161) (recorded D dO P) (first_reads D dO hbudget P Q hqueries)
    decodes := hcompletion }

theorem clean_of_checks
    (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) (Q : Nat)
    (hqueries : DecoderQueryAccounting.AdversaryQueries P Q)
    (hbudget : Budget dO) (hcompletion : Completion D dO P (Q + 1161))
    (hchecks : CheckedAcceptance D dO P (Q + 1161)) :
    CleanAcceptedModel D (recorded D dO P) (fun run => collision (Q + 1161) run ∨
      hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1) := by
  exact OraclePortCleanModel.clean_model_of_checked_acceptance_no_hit
    D dO P BinCombinedMerkleCollision.kappa (Q + 1161)
    (injection D dO P Q hqueries hbudget hcompletion) hchecks
    (recorded D dO P) rfl _ (fun _ => Iff.rfl)

#print axioms injection
#print axioms clean_of_checks
end AspisR1.OraclePortConsumer
end
