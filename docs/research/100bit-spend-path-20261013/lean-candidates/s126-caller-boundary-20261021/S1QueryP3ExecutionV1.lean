import S1QueryClosedRelationV1
import S1ClosedPreparationOracleV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.BorrowedClaimPrepared
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedQueryMaterialize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

theorem closed_query_p3_valid (sha : Bytes → Array U8 32#usize)
    (self : AspisR1PublicPreparation.transcript.Transcript SolanaDigest) (row : U8) (payload : Slice U8) :
    OracleValid sha (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
      (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self row payload) := by
  have roundtrip (d : AspisR1PublicPreparation.aspis_core.Digest32 SolanaDigest) :
      InstalledPreparation.retainedDigest (publicToCurrent d)=d := by cases d; rfl
  unfold p3CallerDigest
  rw [roundtrip,p3_public_record_eq_model]
  exact queries_p3_valid _ _ _ _ _ _

/-- Actual retained query procedure under the extracted P3 wrapper, all
outcomes and ordered reads. No per-call DigestAt or caller association premise. -/
theorem closed_query_p3_execution (sha : Bytes → Array U8 32#usize)
    (self : AspisR1PublicPreparation.transcript.Transcript SolanaDigest) (row : U8) (payload : Slice U8) :
    eval (fun bytes => decodeState (sha bytes))
      (oracleProgram (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
        (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self row payload))=
      (observe (run (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
        (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self row payload)).1,
        AspisR1PublicPreparation.QueriesModel.queries closedHashQueries
          (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self row payload) := by
  rw [oracleProgram_exact sha _ (closed_query_p3_valid sha self row payload),queries_run_value]

/-- SAME actual P3 query success supplies the fixed program's result and
COMPLETE actual hash trace. The existing P3 runtime assumption is retained;
this does not assert native SDK/hashv/syscall implementation correspondence. -/
theorem closed_query31_p3_fixed_accepted {M Cv : Type} {L : Nat} (p : FS2.Duplex.Params M Cv L)
    (sha : Bytes → Array U8 32#usize)
    (self after : AspisR1PublicPreparation.transcript.Transcript SolanaDigest) (payload : Slice U8)
    (queries : Array U32 22#usize)
    (success : AspisR1PublicPreparation.QueriesModel.queries closedHashQueries
      (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self 31#u8 payload=ok (.Ok queries,after)) :
    eval (fun bytes => decodeState (sha bytes)) (fixedQuery31 self.state payload)=
      (observe (run (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
        (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self 31#u8 payload)).1,
        (.ok (queries.val.map (fun w => w.val)),decodeState after.state)) ∧ after.hash=self.hash := by
  have execution := closed_query_p3_execution sha self 31#u8 payload
  have transport := closed_query31_fixed_program p
    (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self payload (fun bytes => decodeState (sha bytes))
  have accepted : (eval (fun bytes => decodeState (sha bytes))
      (oracleProgram (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
        (InstalledPreparation.retainedDigest (p3CallerDigest sha)) self 31#u8 payload))).2=ok (.Ok queries,after) := by
    rw [execution,success]
  obtain ⟨value,hash⟩ := transport.2 queries after accepted
  have log := transport.1
  rw [execution] at log
  exact ⟨Prod.ext log.symm value,hash⟩

#print axioms closed_query_p3_valid
#print axioms closed_query_p3_execution
#print axioms closed_query31_p3_fixed_accepted
end AspisR1CurrentCaller.BorrowedClaimPrepared
