import NDO_JGi_FinishFields
import NDO_JGi_DotOps
import NDO_JGe_SemanticSame
import NDO_JFv_DecodeCanonical
set_option autoImplicit false
namespace AspisR1.JGi_ClaimArrays
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1ClaimPreparedBridge

def RowCanonical (a : Array aspis_core.field.QM31 29#usize) : Prop :=
  ∀ j : Fin 29,JGi_DotOps.CanonQ (toClaimQ (a.val[j.val]'(by have h:=a.property;change a.val.length=29 at h;omega)))

theorem decoded (r : r1_wire.ValidatedRecord) (off : Usize) (a : Array aspis_core.field.QM31 29#usize)
    (call : AspisS1ExtractedRoundChildren.decodeMain 29#usize r off=ok (.Ok a)) : RowCanonical a := by
  have canonical := JFv_DecodeCanonical.source r off a call
  intro j
  exact canonical j
#print axioms decoded

theorem claims : ∀ p : Fin 3,RowCanonical
    (JFu_ClaimsData.claims.val[p.val]'(by have h:=JFu_ClaimsData.claims.property;change JFu_ClaimsData.claims.val.length=3 at h;omega)) := by
  intro p
  fin_cases p
  · exact decoded _ _ _ JFu_ClaimsData.decode0
  · exact decoded _ _ _ JFu_ClaimsData.decode1
  · exact decoded _ _ _ JFu_ClaimsData.decode2
#print axioms claims

theorem source {H : Type} (D : aspis_core.Digest32 H) (expanded : Slice U8) (pre : r1_wire.Prefix)
    (sem : r1_semantic.Verified H) (hash : H)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre))
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value D
      JFs_PublicSerialization.value pre
      (⟨AspisV8R19.SqueezeOracleBridge.encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript H)
      JFm_Begin.challenges none=ok (.Ok sem)) :
    (∀ p : Fin 3,RowCanonical (sem.claims.val[p.val]'(by have h:=sem.claims.property;change sem.claims.val.length=3 at h;omega))) ∧
      RowCanonical sem.extra ∧ RowCanonical sem.before_z1 := by
  obtain ⟨r25,r26,claim,read25,extra,read26,before⟩ := JGi_FinishFields.source
    AspisS1ExtractedRoundChildren.children JGe_Boundaries.value D JFs_PublicSerialization.value pre _ _ none sem finish
  have concrete := JFu_Claims.source expanded pre expand parse
  have same : sem.claims=JFu_ClaimsData.claims := core.result.Result.Ok.inj (Result.ok.inj (claim.symm.trans concrete))
  refine ⟨?_,decoded _ _ _ extra,decoded _ _ _ before⟩
  intro p
  simpa only [same] using claims p
#print axioms source
end AspisR1.JGi_ClaimArrays
