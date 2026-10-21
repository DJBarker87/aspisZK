import OraclePortFrozenOrderCanonicalChecks
import OraclePortCompletionDraft

/-! Close the stored-carrier CheckedAcceptance interface with the original
collision event and exact annotation compiler. No ReaderBinding, source-data,
matching, writer, semantic or backend model hypothesis remains. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortFrozenOrderC6
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.AdaptiveFirstReadLaw
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortFrozenOrderReached

theorem original_clean (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State)
    (Q : Nat) (clean : ¬ RecordedBinaryExperimentBin.binaryCollision Q
      (view (eval H (annotated D decision P)))) :
    ¬ hitsBad (AllAddressCollision.bad SelectedTranscriptParams.params.iv
      BinRawByteCollisionTargets.pred Q) emptyTable (run D P H).1 := by
  intro bad
  apply clean
  change hitsBad _ emptyTable (eval H (recorded D decision (build D) P)).1
  rw [recorded_eval]
  exact TraceAppend.hitsBad_of_prefix _ _ _ _ bad

/-- The complete stored model acceptance premise is now a theorem, on the
canonical prover with unchanged bytes and oracle calls. It is not the old
pair-carrier clean-model/probability theorem. -/
def checked_acceptance (D : LiteralByteProtocol.Decoder) (P : Prover) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q) :
    OraclePortStoredChecksC4.CheckedAcceptance D decision (canon P) (Q+1161) := by
  intro H clean accepted
  exact Classical.choice (OraclePortFrozenOrderCanonicalChecks.accepted_checks D P H Q hq accepted
    (original_clean D (canon P) H (Q+1161) clean))

#print axioms original_clean
#print axioms checked_acceptance
end AspisR1.OraclePortFrozenOrderC6
end
