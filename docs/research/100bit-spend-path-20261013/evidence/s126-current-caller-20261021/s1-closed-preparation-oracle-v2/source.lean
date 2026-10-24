import S1PreparedP3CompleteValidV1
import S1ClosedPreparationHashCodeV1
import S1ReusedSolanaDigestWrapperP3V1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentCaller
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation.PreparedHashCode
open S4SolanaDigestWrapperP3BindingV1

/-- The actual extracted wrapper's P3 dictionary, transported through the
existing fieldwise carrier adapter. No new source/backend association field. -/
def p3CallerDigest (sha : Bytes → Array U8 32#usize) :
    aspis_core.digest.Digest32 SolanaDigest := publicToCurrent (p3PublicDigest32 sha)

theorem closedPreparation_p3_valid (sha : Bytes → Array U8 32#usize)
    (sem : r1_semantic.Verified SolanaDigest) (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    OracleValid sha (closedPreparationCode (p3CallerDigest sha) sem view hash scratch) := by
  unfold closedPreparationCode
  apply valid_bind
  · change OracleValid sha (AspisR1PublicPreparation.PreparedSourceEffects.prepare
      (preparationEffects closedHashBoundaries closedHashQueries)
      (p3PublicDigest32 sha) (InstalledPreparation.retainedSem sem)
      (InstalledPreparation.retainedView view) hash (mapArray InstalledPreparation.retainedE scratch))
    rw [p3_public_record_eq_model]
    exact preparation_p3_valid _ _ _ _ _ _ _ _
  · intro value
    exact valid_pure sha _

/-- SAME complete ordered byte-oracle reads and Result as the source-shaped
execution, including duplicates and failure prefixes. Validity is discharged
for the concrete P3 wrapper; it is not a theorem premise. -/
theorem closedPreparation_oracle_exact (sha : Bytes → Array U8 32#usize)
    (sem : r1_semantic.Verified SolanaDigest) (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    eval (fun bytes => decodeState (sha bytes))
      (oracleProgram (closedPreparationCode (p3CallerDigest sha) sem view hash scratch))=
    (observe (run (closedPreparationCode (p3CallerDigest sha) sem view hash scratch)).1,
      (run (closedPreparationCode (p3CallerDigest sha) sem view hash scratch)).2) :=
  oracleProgram_exact sha _ (closedPreparation_p3_valid sha sem view hash scratch)

/-- Value transport reaches precisely the existing installed caller operation.
P3 is the existing hashv interpretation, not a proof of the Solana runtime. -/
theorem closedPreparation_oracle_installed (ops : Ops) (sha : Bytes → Array U8 32#usize)
    (sem : r1_semantic.Verified SolanaDigest) (view : verifier.View) (hash : SolanaDigest)
    (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (eval (fun bytes => decodeState (sha bytes))
      (oracleProgram (closedPreparationCode (p3CallerDigest sha) sem view hash scratch))).2=
      (closedInstall ops).op8 (p3CallerDigest sha) sem view hash scratch := by
  rw [oracleProgram_value sha _ (closedPreparation_p3_valid sha sem view hash scratch)]
  exact closedPreparationCode_installed ops _ _ _ _ _

#print axioms closedPreparation_p3_valid
#print axioms closedPreparation_oracle_exact
#print axioms closedPreparation_oracle_installed
end AspisR1CurrentCaller.BorrowedClaimPrepared
