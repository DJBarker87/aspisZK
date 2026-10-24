import S1SelectedQueryPayloadV1
import S1QueryP3ExecutionV1
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

def selectedQueryProgram (state : Array U8 32#usize) (payload : Slice U8) (length : payload.length=2048) :
    Program Bytes State (Except Nat (List Nat) × State) :=
  rename Addr.toBytes (AspisR1.QuerySamplerBridge.sampler AspisR1.SelectedTranscriptParams.params
    (queryAbsorb state payload length) id).toProgram

/-- SAME actual source query success supplies the selected fixed-parameter
query constructor's entire log, ordered result, state and full source hash.
Payload, frame, label and cast correspondence are concrete derived laws. -/
theorem selected_query_p3_accepted (sha : Bytes → Array U8 32#usize)
    (self after : AspisR1PublicPreparation.transcript.Transcript SolanaDigest)
    (payload : Slice U8) (length : payload.length=2048) (queries : Array U32 22#usize)
    (success : AspisR1PublicPreparation.QueriesModel.queries closedHashQueries
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (p3CallerDigest sha))
      self 31#u8 payload=ok (.Ok queries,after)) :
    eval (fun bytes => decodeState (sha bytes)) (selectedQueryProgram self.state payload length)=
      (observe (run (AspisR1PublicPreparation.PreparedQueryEffects.queries effects closedHashQueries
        (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (p3CallerDigest sha)) self 31#u8 payload)).1,
        (.ok (queries.val.map (fun w => w.val)),decodeState after.state)) ∧ after.hash=self.hash := by
  unfold selectedQueryProgram
  rw [←fixedQuery31_selected self.state payload length]
  exact closed_query31_p3_fixed_accepted AspisR1.SelectedTranscriptParams.params sha self after payload queries success

#print axioms selected_query_p3_accepted
end AspisS1SelectedQueryPayload
