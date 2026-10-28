import NDO_JGg_PreparationOpening
import NDO_JGg_ViewOpening
import NDO_JGe_SemanticSame
set_option autoImplicit false
namespace AspisR1.JGg_OpeningFixture
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge
open AspisR1CurrentCaller.InstalledPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1ClaimPreparedBridge

def Calls {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) : Prop :=
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (gamma kappa alpha0 alpha1 : aspis_core.field.WideExact) (rho : aspis_core.field.QM31)
      (q : Array U32 22#usize) (powers : Array aspis_core.field.WideExact 29#usize),
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening27.before,hash⟩ : transcript.Transcript Hash) 27#u8 JGg_Opening27.payload true=
        ok (gamma,(⟨encodeState JGg_Opening27.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening28.before,hash⟩ : transcript.Transcript Hash) 28#u8 JGg_Opening28.payload false=
        ok (kappa,(⟨encodeState JGg_Opening28.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening29.before,hash⟩ : transcript.Transcript Hash) 29#u8 JGg_Opening29.payload false=
        ok (alpha0,(⟨encodeState JGg_Opening29.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening30.before,hash⟩ : transcript.Transcript Hash) 30#u8 JGg_Opening30.payload false=
        ok (alpha1,(⟨encodeState JGg_Opening30.next0,hash⟩ : transcript.Transcript Hash)) ∧
      PreparedModel.scalar_k closedHashBoundaries.sampling D0
        (⟨encodeState JGg_Opening32.before,hash⟩ : transcript.Transcript Hash) 32#u8 JGg_Opening32.payload=
        ok (rho,(⟨encodeState JGg_Opening32.next0,hash⟩ : transcript.Transcript Hash)) ∧
      QueriesModel.queries closedHashQueries D0
        (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript Hash) 31#u8 JGg_Opening31.payload=
        ok (.Ok q,(⟨encodeState JGg_Opening31.next2,hash⟩ : transcript.Transcript Hash)) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE gamma) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE kappa) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE alpha0) ∧
      AspisR1CurrentPreparedClaim.Concrete.Canonical (toClaimE alpha1) ∧
      powersPublic 29#usize gamma=ok powers

/-- Partial real-byte source non-vacuity. Full preparation/accepted1, checkpoint
identity, accepted2 and the deployed fixture are not asserted by this theorem. -/
theorem inhabited {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (expanded : Slice U8) (pre : r1_wire.Prefix) (view : AspisR1CurrentCaller.verifier.View),
      compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),JGe_Payload27.value) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      view.variant=.S2 ∧ view.y1=JGg_Opening27.payload ∧ view.round0=JGg_Opening29.payload ∧
      view.folded_root=some JGe_View.folded ∧
      JGe_View.folded.val ++ view.round1.val=JGg_Opening30.payload.val ∧
      view.final_message=JGg_Opening31.payload ∧
      AspisR1CurrentCaller.OriginalSerializerInstallation.sourceBytes (retainedView view).inactive=
        ok (Array.repeat 32#usize 0#u8) ∧
      Calls D hash ∧
      (JGe_TerminalCondition.Identified → ∃ sem : r1_semantic.Verified Hash,
        FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value D0
          JFs_PublicSerialization.value pre
          (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
          JFm_Begin.challenges none=ok (.Ok sem) ∧
        sem.roots=Array.make 2#usize [JFp_InitBytes.root,JFq_Root1.value] ∧
        sem.transcript.state=encodeState JFu_Q26Source.ratchet) := by
  dsimp only
  obtain ⟨expanded,y1,pre,oldView,claims,cs,mask,old,rest⟩ := JFu_FinishInputs.inhabited D JGe_Boundaries.value hash
  have expand := old.1
  have parse := old.2.1
  obtain ⟨view,wide,variant,y1eq,round0,root,round1,finalMessage,inactive⟩ := JGg_ViewOpening.source expanded
  refine ⟨expanded,pre,view,expand,parse,JGe_Payload27.source,wide,variant,y1eq,round0,root,round1,
    finalMessage,inactive,JGg_PreparationOpening.source D hash,?_⟩
  intro identified
  exact JGe_SemanticSame.source D hash expanded pre expand parse identified
#print axioms inhabited
end AspisR1.JGg_OpeningFixture
