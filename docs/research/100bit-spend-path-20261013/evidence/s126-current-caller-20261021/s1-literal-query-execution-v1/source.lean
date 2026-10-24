import S1LiteralQueryProgramV1
import S1SelectedQueryExecutionV1
set_option autoImplicit false
noncomputable section
namespace AspisS1SelectedQueryPayload
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedQueryMaterialize
open S4SolanaDigestWrapperP3BindingV1

/-- Actual source query to the selected literal row31, including COMPLETE
ordered log and actual literal challenge constructor. The exact remaining
input relation is EXPLICIT: the given Prefix's prior state equals the source
before-state. This theorem neither assumes a per-call hash/frame law nor
constructs a substitute Prefix to make that state relation hold. -/
theorem literal_query_p3_accepted (sha : Bytes → Array U8 32#usize)
    (P : AspisR1.LiteralTranscript.Prefix)
    (self after : AspisR1PublicPreparation.transcript.Transcript SolanaDigest)
    (payload : Slice U8) (length : payload.length=2048) (queries : Array U32 22#usize)
    (success : AspisR1PublicPreparation.QueriesModel.queries closedHashQueries
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (p3CallerDigest sha))
      self 31#u8 payload=ok (.Ok queries,after))
    (stateEq : AspisR1.UnifiedSampler.stateOf AspisR1.SelectedTranscriptParams.params
      (AspisR1.LiteralTranscript.erasePrefix P)=decodeState self.state) :
    eval (fun bytes => decodeState (sha bytes))
      (AspisR1.LiteralByteSampler.samp 31 P (.payload (selectedMessage payload length))).toProgram=
      (observe (run (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
        (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (p3CallerDigest sha)) self 31#u8 payload)).1,
        (.queries (.ok (queries.val.map (fun w => w.val))),decodeState after.state)) := by
  have beforeBytes : encodeState (AspisR1.UnifiedSampler.stateOf AspisR1.SelectedTranscriptParams.params
      (AspisR1.LiteralTranscript.erasePrefix P))=self.state := by
    rw [stateEq,array_roundtrip]
  have execution := closed_query31_p3_fixed_accepted AspisR1.SelectedTranscriptParams.params
    sha self after payload queries success
  rw [←literal_query_program P payload length,beforeBytes,eval_bind,execution.1]
  simp only [eval,List.append_nil]
  rfl

#print axioms literal_query_p3_accepted
end AspisS1SelectedQueryPayload
