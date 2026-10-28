import NDO_JGp_CurrentQueries
import RPt_JFo_Prepared
set_option autoImplicit false
namespace AspisR1.JGp_CurrentRoots
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition

theorem source {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (JGp_PrepareLayout.installed base query geo)
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof hash none input=ok (.Ok p,scratch)) :
    p.roots=JFo_Prepared.value.roots := by
  obtain ⟨initial,expanded,view,sem,expand,wide,viewsem,verify,newCall⟩ :=
    JGp_PrepareCuts.source base query geo _ hash _ p input scratch success
  have semantic := JGp_SemanticIdentity.source D hash initial expanded sem expand verify
  obtain ⟨out,rs,reached,outEq,scratchEq⟩ := PAln_Borrowed.original_reached
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed _ sem view hash input scratch p newCall
  have variant := sourceView_variant _ _ _ _ wide
  have oldVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [variant]
    rfl
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,inactive,root,bytes1,bytes2,gamma,kappa,a0,a1,rho,queries,claim,
    seed,gammaCall,serialized,kappaCall,a0Call,rootCall,first,second,a1Call,queryCall,rhoCall,powers,claimed,output⟩ :=
    PAln_OpeningStages.double_of_reached _ _ (retainedSem sem) (retainedView view) hash out rs oldVariant reached
  have roots : out.roots=sem.roots := by rw [output];rfl
  rw [←outEq]
  change out.roots=JFo_Prepared.value.roots
  rw [roots,semantic.1,JGe_Roots.first_root_checkpoint]
  rfl
#print axioms source
end AspisR1.JGp_CurrentRoots
