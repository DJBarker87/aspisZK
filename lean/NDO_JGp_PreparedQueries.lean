import NDO_JGp_QueryCalls
import NDO_JGi_PreparationFixture
set_option autoImplicit false
namespace AspisR1.JGp_PreparedQueries
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
open AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1ClaimPreparedBridge
open AspisR1CurrentCaller.InstalledPreparation

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (sem : r1_semantic.Verified H) (view : verifier.View) (out : verifier.Prepared)
    (input scratch : Array aspis_core.field.WideExact 29#usize)
    (state : sem.transcript.state=encodeState JFu_Q26Source.ratchet)
    (variant : view.variant=.S2) (y1 : view.y1=JGg_Opening27.payload)
    (inactiveInput : AspisR1CurrentCaller.OriginalSerializerInstallation.sourceBytes view.inactive=ok (Array.repeat 32#usize 0#u8))
    (round0 : view.round0=JGg_Opening29.payload) (folded : view.folded_root=some JGe_View.folded)
    (round1 : JGe_View.folded.val++view.round1.val=JGg_Opening30.payload.val)
    (finalMessage : view.final_message=JGg_Opening31.payload)
    (run : PreparedScratchModel.prepare closedHashBoundaries
      (retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)) sem view hash input=ok (.Ok out,scratch)) :
    out.queries=JFq_Queries.value := by
  let D0 := retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
  have reached := PreparedScratchReachability.prepare_success closedHashBoundaries D0 sem view hash out scratch input run
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,gammaCall,serialized,kappaCall,a0Call,rootCall,first,second,a1Call,query,rhoCall,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached closedHashBoundaries D0 sem view hash out scratch variant reached
  obtain ⟨g,k,b0,b1,r,gc,kc,b0c,b1c,rc⟩ := JGg_Scalars.source D hash
  have seedCall := JGg_OpeningSeed.source D hash sem view state variant
  have et0 : t0=(⟨encodeState JGe_OpeningInit.state,hash⟩ : transcript.Transcript H) := Result.ok.inj (seed.symm.trans seedCall)
  subst t0
  rw [y1] at gammaCall
  have et1 : t1=(⟨encodeState JGg_Opening27.next0,hash⟩ : transcript.Transcript H) := congrArg Prod.snd (Result.ok.inj (gammaCall.symm.trans gc))
  rw [et1] at kappaCall
  have ei : inactive=Array.repeat 32#usize 0#u8 := Result.ok.inj (serialized.symm.trans inactiveInput)
  subst inactive
  have et2 : t2=(⟨encodeState JGg_Opening28.next0,hash⟩ : transcript.Transcript H) := congrArg Prod.snd (Result.ok.inj (kappaCall.symm.trans kc))
  rw [et2,round0] at a0Call
  have et3 : t3=(⟨encodeState JGg_Opening29.next0,hash⟩ : transcript.Transcript H) := congrArg Prod.snd (Result.ok.inj (a0Call.symm.trans b0c))
  rw [et3] at a1Call
  rw [folded] at rootCall
  have eroot : JGe_View.folded=root := Result.ok.inj rootCall
  subst root
  have len1 : view.round1.length=224 := by
    have h := congrArg List.length round1
    have hl := JGg_Opening30.length
    change JGg_Opening30.payload.val.length=256 at hl
    have hr : JGe_View.folded.val.length=32 := JGe_View.folded.property
    simp only [List.length_append] at h
    change view.round1.val.length=224
    omega
  obtain ⟨buf1,buf2,hfirst,hsecond,contents⟩ := JGi_FoldBuffers.source JGe_View.folded view.round1 len1
  have eb1 : bytes1=buf1 := Result.ok.inj (first.symm.trans hfirst)
  subst bytes1
  have eb2 : bytes2=buf2 := Result.ok.inj (second.symm.trans hsecond)
  subst bytes2
  have buffer : alloc.vec.Vec.deref buf2=JGg_Opening30.payload := Subtype.ext (contents.trans round1)
  rw [buffer] at a1Call
  have et4 : t4=(⟨encodeState JGg_Opening30.next0,hash⟩ : transcript.Transcript H) := congrArg Prod.snd (Result.ok.inj (a1Call.symm.trans b1c))
  rw [JGi_ClosedQueries.source,et4,finalMessage] at query
  have qe : queries=JFq_Queries.value := core.result.Result.Ok.inj
    (congrArg Prod.fst (Result.ok.inj (query.symm.trans (JGp_QueryCalls.source D hash))))
  rw [output]
  exact qe
#print axioms source
end AspisR1.JGp_PreparedQueries
