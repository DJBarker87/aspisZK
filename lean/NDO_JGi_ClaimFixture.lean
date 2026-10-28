import NDO_JGi_PreparedClaim
import NDO_JGg_OpeningFixture
set_option autoImplicit false
namespace AspisR1.JGi_ClaimFixture
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1ClaimPreparedBridge
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.SqueezeOracleBridge

theorem inhabited {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H) :
    let D0 := retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (expanded : Slice U8) (pre : r1_wire.Prefix) (view : AspisR1CurrentCaller.verifier.View)
      (gamma kappa : aspis_core.field.WideExact) (powers : Array aspis_core.field.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      AspisS1ValuesOwnedInstallation.expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),JGe_Payload27.value) ∧
      AspisR1CurrentCaller.InstalledPreparation.sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      powersPublic 29#usize gamma=ok powers ∧
      (JGe_TerminalCondition.Identified → ∃ (sem : r1_semantic.Verified H) (claim : aspis_core.field.WideExact),
        FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value D0
          JFs_PublicSerialization.value pre
          (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript H)
          JFm_Begin.challenges none=ok (.Ok sem) ∧
        closedHashBoundaries.claim D0 sem (retainedView view).y1 (retainedView view).inactive powers kappa=ok (.Ok claim)) := by
  dsimp only
  obtain ⟨expanded,pre,view,expand,parse,yexpand,wide,variant,y1eq,round0,root,round1,finalMessage,inactive,calls,finish⟩ :=
    JGg_OpeningFixture.inhabited D hash
  obtain ⟨gamma,kappa,a0,a1,rho,q,powers,gc,kc,a0c,a1c,rc,qc,gcanon,kcanon,a0canon,a1canon,powersCall⟩ := calls
  refine ⟨expanded,pre,view,gamma,kappa,powers,expand,parse,yexpand,wide,powersCall,?_⟩
  intro identified
  obtain ⟨sem,finished,roots,state⟩ := finish identified
  obtain ⟨claim,claimed⟩ := JGi_PreparedClaim.source _ hash expanded pre sem view gamma kappa powers
    expand parse finished wide y1eq gcanon kcanon powersCall
  exact ⟨sem,claim,finished,claimed⟩
#print axioms inhabited
end AspisR1.JGi_ClaimFixture
