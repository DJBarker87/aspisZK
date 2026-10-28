import NDO_JGi_ClosedQueries
import NDO_JGi_ClaimFixture
import NDO_JGi_PrepareForward
import NDO_JGi_FoldBuffers
import NDO_JGg_OpeningSeed
set_option autoImplicit false
namespace AspisR1.JGi_PreparationFixture
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1ClaimPreparedBridge
open AspisR1CurrentCaller.InstalledPreparation
open AspisV8R19.SqueezeOracleBridge

theorem inhabited {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (input : Array aspis_core.field.WideExact 29#usize) (identified : JGe_TerminalCondition.Identified) :
    let D0 := retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (expanded : Slice U8) (pre : r1_wire.Prefix) (view : AspisR1CurrentCaller.verifier.View)
      (sem : r1_semantic.Verified H) (out : verifier.Prepared) (scratch : Array aspis_core.field.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      AspisS1ValuesOwnedInstallation.expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),JGe_Payload27.value) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value D0 JFs_PublicSerialization.value pre
        (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript H)
        JFm_Begin.challenges none=ok (.Ok sem) ∧
      PreparedScratchModel.prepare closedHashBoundaries D0 sem (retainedView view) hash input=ok (.Ok out,scratch) := by
  dsimp only
  obtain ⟨expanded,pre,view,expand,parse,yexpand,wide,variant,y1eq,round0,root,round1,finalMessage,inactive,calls,finish⟩ :=
    JGg_OpeningFixture.inhabited D hash
  obtain ⟨gamma,kappa,a0,a1,rho,q,powers,gc,kc,a0c,a1c,rc,qc,gcanon,kcanon,a0canon,a1canon,powersCall⟩ := calls
  obtain ⟨sem,finished,roots,state⟩ := finish identified
  obtain ⟨claim,claimed⟩ := JGi_PreparedClaim.source _ hash expanded pre sem view gamma kappa powers
    expand parse finished wide y1eq gcanon kcanon powersCall
  have variant' : (retainedView view).variant=.S2 := by
    change retainedVariant view.variant=_
    rw [variant]
    rfl
  have seed := JGg_OpeningSeed.source D hash sem (retainedView view) state variant'
  have len1 : view.round1.length=224 := by
    have h := congrArg List.length round1
    have hl := JGg_Opening30.length
    change JGg_Opening30.payload.val.length=256 at hl
    have hr : JGe_View.folded.val.length=32 := JGe_View.folded.property
    simp only [List.length_append] at h
    change view.round1.val.length=224
    omega
  obtain ⟨bytes1,bytes2,first,second,contents⟩ := JGi_FoldBuffers.source JGe_View.folded view.round1 len1
  have buffer : alloc.vec.Vec.deref bytes2=JGg_Opening30.payload := Subtype.ext (contents.trans round1)
  have rootCall : core.option.Option.unwrap (retainedView view).folded_root=ok JGe_View.folded := by
    change core.option.Option.unwrap view.folded_root=_
    rw [root]
    rfl
  let out := PreparedScratchReachability.output sem (retainedView view) gamma kappa
    (Array.make 2#usize [a0,a1]) rho q claim
    (⟨encodeState JGg_Opening32.next0,hash⟩ : transcript.Transcript H)
  have double : PAln_OpeningStages.Double closedHashBoundaries
      (retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)) sem (retainedView view) hash out powers := by
    refine ⟨⟨encodeState JGg_Opening27.before,hash⟩,
      ⟨encodeState JGg_Opening27.next0,hash⟩,
      ⟨encodeState JGg_Opening28.next0,hash⟩,
      ⟨encodeState JGg_Opening29.next0,hash⟩,
      ⟨encodeState JGg_Opening30.next0,hash⟩,
      ⟨encodeState JGg_Opening31.next2,hash⟩,
      ⟨encodeState JGg_Opening32.next0,hash⟩,
      Array.repeat 32#usize 0#u8,JGe_View.folded,bytes1,bytes2,
      gamma,kappa,a0,a1,rho,q,claim,seed,?_,inactive,?_,?_,rootCall,first,second,?_,?_,rc,powersCall,claimed,rfl⟩
    · change PreparedModel.scalar _ _ _ _ view.y1 _=_
      rw [y1eq]
      exact gc
    · exact kc
    · change PreparedModel.scalar _ _ _ _ view.round0 _=_
      rw [round0]
      exact a0c
    · rw [buffer]
      exact a1c
    · rw [JGi_ClosedQueries.source]
      change QueriesModel.queries closedHashQueries _ _ _ view.final_message=_
      rw [finalMessage]
      exact qc
  exact ⟨expanded,pre,view,sem,out,powers,expand,parse,yexpand,wide,finished,
    JGi_PrepareForward.source _ _ _ _ _ out powers input variant' double⟩
#print axioms inhabited
end AspisR1.JGi_PreparationFixture
