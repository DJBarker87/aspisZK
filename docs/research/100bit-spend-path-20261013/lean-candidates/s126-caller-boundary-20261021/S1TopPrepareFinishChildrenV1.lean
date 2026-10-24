import S1ExtractedRoundChildrenV1
import S1FinishChildrenV1
import S1TopPrepareExtractedChildrenV1
import S1TopPrepareY1ProvenanceV1
import S1TopPrepareCallbackProgramV1
set_option autoImplicit false
noncomputable section
namespace AspisS1TopPrepareCode
open Aeneas Aeneas.Std Result
open AspisS1TopPrepareCarrier AspisR1ClaimPreparedBridge
open AspisR1PublicPreparation.PreparedHashCode
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisS1ValuesOwnedInstallation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisV8R19.MemoizedProgramLaw
open S4SolanaDigestWrapperP3BindingV1
open AspisS1PreparedPowersCallbacks AspisS1PowersCallbackChain
open AspisR1PowersConcreteMul AspisR1PowersExactProduct


/-- Same accepted release op7 with concrete round children and six fixed finish
source operations. Only claims/terminal remain explicit finish parameters.
Native SDK/Std/abort and S9 raw-circle source gates remain separate. -/
theorem installed_finish_children_y1 (base : AspisR1CurrentCaller.Ops)
    (claims : AspisS1FinishChildren.Claims) (terminal : AspisS1FinishChildren.Terminal)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : (eval H (body base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).2=
        ok (.Ok prepared,scratch)) :
    (eval H (body base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 ∧
    Y1Provenance base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) (digest (fun bytes => encodeState (H bytes))) pub proof hash input scratch prepared := by
  exact installed_extracted_children_y1 base (AspisS1FinishChildren.install claims terminal) other H pub proof hash input scratch prepared accepted

#print axioms installed_finish_children_y1

/-- Same accepted release op7 with concrete round children and six fixed finish
source operations. Only claims/terminal remain explicit finish parameters.
Native SDK/Std/abort and S9 raw-circle source gates remain separate. -/
theorem accepted_finish_children_scratch (base : AspisR1CurrentCaller.Ops)
    (claims : AspisS1FinishChildren.Claims) (terminal : AspisS1FinishChildren.Terminal)
    (other : AspisR1.VTop_OracleCode.Implementation) (H : Bytes → State)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : SolanaDigest) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (accepted : (eval H (body base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).2=
        ok (.Ok prepared,scratch)) :
    eval H (body base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))=
      (observe (run (code base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) (digest (fun bytes => encodeState (H bytes))) pub proof hash input)).1,
        AspisS1TopPrepareSource.prepare (sourceOps base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal)) (digest (fun bytes => encodeState (H bytes)))
          pub proof hash none input) ∧
    (eval H (body base AspisS1ExtractedRoundChildren.children (AspisS1FinishChildren.install claims terminal) other
      (.op7 (digest (fun bytes => encodeState (H bytes))) pub proof hash none input))).1.length ≤ 115 ∧
    ∃ last,
      execute 29#usize (one,callbackE prepared.gamma) (slots 29#usize)=
        ok (scratch.val.map callbackE,(last,callbackE prepared.gamma)) ∧
      Canonical last ∧ decode last=decode (callbackE prepared.gamma)^29 ∧
      Complete 7#usize (callbackE prepared.kappa) := by
  exact accepted_extracted_children_scratch base (AspisS1FinishChildren.install claims terminal) other H pub proof hash input scratch prepared accepted

#print axioms accepted_finish_children_scratch
end AspisS1TopPrepareCode
