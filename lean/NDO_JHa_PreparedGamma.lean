import NDO_JGp_CurrentQueries
import NDO_JHa_GammaSample
import RPt_JFo_Prepared
set_option autoImplicit false
namespace AspisR1.JHa_PreparedGamma
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition

theorem source {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (JGp_PrepareLayout.installed base query geo)
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof hash none input=ok (.Ok p,scratch)) :
    p.gamma=currentE JHa_GammaSample.value ∧
      ∃ rs : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize,
        powersPublic 29#usize JHa_GammaSample.value=ok rs ∧ mapArray currentE rs=scratch := by
  obtain ⟨initial,expanded,view,sem,expand,wide,viewsem,verify,newCall⟩ :=
    JGp_PrepareCuts.source base query geo _ hash _ p input scratch success
  have semantic := JGp_SemanticIdentity.source D hash initial expanded sem expand verify
  obtain ⟨out,rs,reached,outEq,scratchEq⟩ := PAln_Borrowed.original_reached
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed _ sem view hash input scratch p newCall
  obtain ⟨other,call,variant,y1,round0,folded,round1,finalMessage,inactive⟩ := JGg_ViewOpening.source expanded
  have same : other=view := core.result.Result.Ok.inj (Result.ok.inj (call.symm.trans wide))
  subst other
  have oldVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [variant]
    rfl
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,gammaCall,serialized,kappaCall,a0Call,rootCall,first,second,a1Call,queryCall,rhoCall,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached _ _ (retainedSem sem) (retainedView view) hash out rs oldVariant reached
  have seedCall := JGg_OpeningSeed.source D hash (retainedSem sem) (retainedView view) semantic.2 oldVariant
  have et0 : t0=(⟨AspisV8R19.SqueezeOracleBridge.encodeState JGe_OpeningInit.state,hash⟩ :
      AspisR1PublicPreparation.transcript.Transcript H) := Result.ok.inj (seed.symm.trans seedCall)
  subst t0
  change AspisR1PublicPreparation.PreparedModel.scalar closedHashBoundaries.sampling
    (retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
    _ 27#u8 view.y1 true=ok (gamma,t1) at gammaCall
  rw [y1] at gammaCall
  have gc := JGg_ScalarForward.scalar closedHashBoundaries.sampling _ _ _ _ _ _
    JHa_GammaSample.value true (JGg_Opening27.source D hash) JHa_GammaSample.sample
  have eg : gamma=JHa_GammaSample.value := congrArg Prod.fst (Result.ok.inj (gammaCall.symm.trans gc))
  subst gamma
  constructor
  · rw [←outEq,output]
    rfl
  · exact ⟨rs,powers,scratchEq⟩
#print axioms source
end AspisR1.JHa_PreparedGamma
