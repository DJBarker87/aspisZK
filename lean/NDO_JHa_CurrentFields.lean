import NDO_JHa_Powers
import NDO_JGp_PrepareCuts
import NDO_JGp_SemanticIdentity
import NDO_JHa_RetainedFields
set_option autoImplicit false
namespace AspisR1.JHa_CurrentFields
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition

theorem source {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (JGp_PrepareLayout.installed base query geo)
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof hash none input=ok (.Ok p,scratch)) :
    Tx1Q_Carriers.e p.gamma=JFq_Gamma.scalar ∧
      Tx1Q_Carriers.e p.kappa=JFq_Kappa.scalar ∧
      Tx1Q_Carriers.arr Tx1Q_Carriers.e p.alpha=JFo_Prepared.value.alpha := by
  obtain ⟨initial,expanded,view,sem,expand,wide,viewsem,verify,newCall⟩ :=
    JGp_PrepareCuts.source base query geo _ hash _ p input scratch success
  have semantic := JGp_SemanticIdentity.source D hash initial expanded sem expand verify
  obtain ⟨other,call,variant,y1,round0,folded,round1,finalMessage,inactive⟩ := JGg_ViewOpening.source expanded
  have same : other=view := core.result.Result.Ok.inj (Result.ok.inj (call.symm.trans wide))
  subst other
  obtain ⟨out,rs,prepared,outEq,scratchEq⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed _ sem view hash input scratch p newCall
  have oldVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [variant]
    rfl
  have value := JHa_RetainedFields.source D hash (retainedSem sem) (retainedView view) out
    (mapArray retainedE input) rs semantic.2 oldVariant y1 inactive round0 folded round1 finalMessage prepared
  rw [←outEq]
  obtain ⟨gamma,kappa,alpha⟩ := value
  constructor
  · change Tx1Q_Carriers.e (currentE out.gamma)=_
    rw [gamma]
    rfl
  constructor
  · change Tx1Q_Carriers.e (currentE out.kappa)=_
    rw [kappa]
    rfl
  · change Tx1Q_Carriers.arr Tx1Q_Carriers.e (mapArray currentE out.alpha)=_
    rw [alpha]
    rfl
#print axioms source
end AspisR1.JHa_CurrentFields
