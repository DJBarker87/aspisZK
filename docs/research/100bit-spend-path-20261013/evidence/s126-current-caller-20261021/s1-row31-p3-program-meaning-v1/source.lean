import S1QueryP3ExecutionV1
import S1RankTraceQueryProgramV1
set_option autoImplicit false
noncomputable section
namespace AspisR1CurrentCaller.OriginalSerializerInstallation
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1PublicPreparation.PreparedHashCode AspisR1PublicPreparation.PreparedQueryMaterialize
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1

def Row31P3ProgramMeaning (sha : Bytes → Array U8 32#usize)
    (v : AspisR1PublicPreparation.verifier.View) (out : AspisR1PublicPreparation.verifier.Prepared) : Prop :=
  ∃ (before after last : transcript.Transcript SolanaDigest) (rhoBlock : Array U8 32#usize),
    QueriesModel.queries closedHashQueries (InstalledPreparation.retainedDigest (p3CallerDigest sha))
      before 31#u8 v.final_message=ok (.Ok out.queries,after) ∧
    eval (fun bytes => decodeState (sha bytes)) (fixedQuery31 before.state v.final_message)=
      (observe (run (PreparedQueryEffects.queries effects closedHashQueries
        (InstalledPreparation.retainedDigest (p3CallerDigest sha)) before 31#u8 v.final_message)).1,
        (.ok (out.queries.val.map (fun w => w.val)),decodeState after.state)) ∧
    after.hash=before.hash ∧
    transcript.Transcript.block (InstalledPreparation.retainedDigest (p3CallerDigest sha)) after 32#u8
      PreparedScratchReachability.emptyPayload=ok (rhoBlock,last) ∧
    sampler.qm31_sample rhoBlock=ok out.rho ∧ out.state=last.state

/-- No independent query success or hash association: consume the query and
rho calls already derived from the SAME enclosing preparation trace. -/
theorem row31P3_from_program_meaning {M Cv : Type} {L : Nat} (p : FS2.Duplex.Params M Cv L)
    (sha : Bytes → Array U8 32#usize) (v : AspisR1PublicPreparation.verifier.View)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (meaning : Row31QueryProgramMeaning (InstalledPreparation.retainedDigest (p3CallerDigest sha)) v out) :
    Row31P3ProgramMeaning sha v out := by
  obtain ⟨before,after,last,rhoBlock,hquery,hprogram,hrho,hsample,hstate⟩ := meaning
  obtain ⟨execution,hash⟩ := closed_query31_p3_fixed_accepted p sha before after v.final_message out.queries hquery
  exact ⟨before,after,last,rhoBlock,hquery,execution,hash,hrho,hsample,hstate⟩

#print axioms row31P3_from_program_meaning
end AspisR1CurrentCaller.OriginalSerializerInstallation
