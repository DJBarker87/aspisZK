import FJq_ExtraCanonical
import ClaimsUnrolledVerify
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_AcceptedExtra
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller InstalledPreparation
/-- ONE complete semantic success supplies its actual extra decoder and
canonical array, retaining the SAME parsed prefix and row25 getter. -/
theorem value (std : ClaimsUnrolledFinish.StdCalls) (ops : Ops) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (accepted : (AspisS1NativeBufferClaimTrace.semanticBase ops
      (ClaimsUnrolledFinish.install std B)).op9 D pub bytes hash none=ok (.Ok sem)) :
    ∃ (pre : r1_wire.Prefix) (record : r1_wire.ValidatedRecord),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      r1_wire.Prefix.validated_record pre 25#u8=ok (.Ok record) ∧
      AspisS1ExtractedRoundChildren.decodeMain 29#usize record 87#usize=ok (.Ok (retainedSem sem).extra) ∧
      (∀ x∈(retainedSem sem).extra.val,FIp_SemanticValues.Canon x) := by
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begun,finished,claims⟩:=
    ClaimsUnrolledSdk.semantic_claims std ops B D pub bytes hash sem accepted
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,rounds,ch,state,transcript,claimCall,read25,extra,rest⟩:=
    S1SemanticFinishBounds.finish_success AspisS1ExtractedRoundChildren.children
      (S1SemanticRootCopy.install (ClaimsUnrolledFinish.install std B))
      (retainedDigest D) (FirstComposition.toRetainedPublic pub) pre after challenges none (retainedSem sem) finished
  exact ⟨pre,r25,parsed,read25,extra,FJq_ExtraCanonical.value r25 (retainedSem sem).extra extra⟩
#print axioms value
end AspisR1.FJq_AcceptedExtra
end
