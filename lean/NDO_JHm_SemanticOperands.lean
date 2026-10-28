import NDO_JHl_SemanticIdentity
import NDO_JGi_FinishFields
set_option autoImplicit false
namespace AspisR1.JHm_SemanticOperands
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition S1SemanticCarrier
open BorrowedClaimPrepared AspisR1ClaimPreparedBridge
open AspisV8R19.SqueezeOracleBridge

theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (initial expanded : Slice U8) (sem : r1_semantic.Verified H)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored initial=ok (.Ok (),expanded))
    (verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      expanded hash=ok (.Ok sem)) :
    sem.claims=mapArray (mapArray currentQ) JFu_ClaimsData.claims ∧
    sem.extra=mapArray currentQ JFu_ClaimsData.a3 ∧
    ∃ before : Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize,
      AspisS1ExtractedRoundChildren.decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok before) ∧
      sem.before_z1=mapArray currentQ before := by
  obtain ⟨other,pre,out,otherExpand,parse,finished,roots,state,alpha,z⟩ :=
    JHl_SemanticFields.source D hash JGn_TerminalIdentified.identified
  have same := PSem_ExpansionUnique.carrier_unique JFw_RealExpansion.stored
    JFw_RealExpansion.initial initial other expanded otherExpand expand
  subst other
  have run := JGi_CurrentSemantic.source D hash expanded pre out otherExpand parse finished
  have es : currentSem out=sem := core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans verify))
  obtain ⟨r25,r26,claims,read25,extra,read26,before⟩ :=
    JGi_FinishFields.source _ _ _ _ _ _ _ _ out finished
  have records := JFr_PrefixRecords.source expanded pre otherExpand parse
  have rec25 := JFr_RecordsAt.source pre records 25#u8 (by change 25<27;omega) JFw_NativeRow25.record rfl
  have rec26 := JFr_RecordsAt.source pre records 26#u8 (by change 26<27;omega) JFw_NativeRow26.record rfl
  have same25 : r25=JFu_Q25Source.record := core.result.Result.Ok.inj (Result.ok.inj (read25.symm.trans rec25))
  have same26 : r26=JFu_Q26Source.record := core.result.Result.Ok.inj (Result.ok.inj (read26.symm.trans rec26))
  rw [same25] at extra
  rw [same26] at before
  have cs : out.claims=JFu_ClaimsData.claims := core.result.Result.Ok.inj
    (Result.ok.inj (claims.symm.trans (JFu_Claims.source expanded pre otherExpand parse)))
  have ex : out.extra=JFu_ClaimsData.a3 := core.result.Result.Ok.inj
    (Result.ok.inj (extra.symm.trans JFu_ClaimsData.decode3))
  rw [←es]
  exact ⟨by change mapArray (mapArray currentQ) out.claims=_;rw [cs],
    by change mapArray currentQ out.extra=_;rw [ex],out.before_z1,before,rfl⟩
#print axioms source
end AspisR1.JHm_SemanticOperands
