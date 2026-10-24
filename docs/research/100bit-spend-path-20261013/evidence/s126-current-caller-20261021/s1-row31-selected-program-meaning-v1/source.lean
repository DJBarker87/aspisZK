import S1SelectedQueryExecutionV1
import S1Row31P3ProgramMeaningV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.OriginalSerializerInstallation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedQueryMaterialize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1 AspisS1SelectedQueryPayload

def Row31SelectedProgramMeaning (sha : Bytes → Array U8 32#usize)
    (v : AspisR1PublicPreparation.verifier.View) (out : AspisR1PublicPreparation.verifier.Prepared) : Prop :=
  ∃ (before after last : transcript.Transcript SolanaDigest) (rhoBlock : Array U8 32#usize),
    ∃ length : v.final_message.length=2048,
    QueriesModel.queries closedHashQueries (InstalledPreparation.retainedDigest (p3CallerDigest sha))
      before 31#u8 v.final_message=ok (.Ok out.queries,after) ∧
    (selectedMessage v.final_message length).val.length=2052 ∧
    eval (fun bytes => decodeState (sha bytes)) (selectedQueryProgram before.state v.final_message length)=
      (observe (run (PreparedQueryEffects.queries effects closedHashQueries
        (InstalledPreparation.retainedDigest (p3CallerDigest sha)) before 31#u8 v.final_message)).1,
        (.ok (out.queries.val.map (fun w => w.val)),decodeState after.state)) ∧
    after.hash=before.hash ∧
    transcript.Transcript.block (InstalledPreparation.retainedDigest (p3CallerDigest sha)) after 32#u8
      PreparedScratchReachability.emptyPayload=ok (rhoBlock,last) ∧
    sampler.qm31_sample rhoBlock=ok out.rho ∧ out.state=last.state

/-- Generic helper's sole frame hypothesis is discharged from the actual
accepted View in the enclosing owned-stage1 consumer. -/
theorem row31_selected_from_p3 (sha : Bytes → Array U8 32#usize)
    (v : AspisR1PublicPreparation.verifier.View) (out : AspisR1PublicPreparation.verifier.Prepared)
    (length : v.final_message.length=2048) (meaning : Row31P3ProgramMeaning sha v out) :
    Row31SelectedProgramMeaning sha v out := by
  obtain ⟨before,after,last,rhoBlock,hquery,execution,hash,hrho,hsample,hstate⟩ := meaning
  have model := selected_query_p3_accepted sha before after v.final_message length out.queries hquery
  have messageLength : (selectedMessage v.final_message length).val.length=2052 := by
    change (framedPayload v.final_message).length=2052
    rw [framedPayload_length,length]
  exact ⟨before,after,last,rhoBlock,length,hquery,messageLength,model.1,model.2,hrho,hsample,hstate⟩

#print axioms row31_selected_from_p3
end AspisR1CurrentCaller.OriginalSerializerInstallation
