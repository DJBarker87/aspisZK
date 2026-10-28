import NDO_JHm_SemanticOperands
import NDO_JHm_ClaimOperands
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_RetainedOperands
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition S1SemanticCarrier
open BorrowedClaimPrepared AspisR1ClaimPreparedBridge JGr_Geometry

/-- The concrete rows of the SAME semantic return, transported to the claim ABI. -/
theorem source (initial expanded : Slice U8) (sem : r1_semantic.Verified Unit)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored initial=ok (.Ok (),expanded))
    (verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      digest (toCurrentPublic JFs_PublicSerialization.value) expanded ()=ok (.Ok sem)) :
    ∃ before : Array AspisR1PublicPreparation.aspis_core.field.QM31 29#usize,
      AspisS1ExtractedRoundChildren.decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok before) ∧
      (toClaimSem (retainedSem sem)).claims=mapArray (mapArray toClaimQ) JFu_ClaimsData.claims ∧
      (toClaimSem (retainedSem sem)).extra=mapArray toClaimQ JFu_ClaimsData.a3 ∧
      (toClaimSem (retainedSem sem)).before_z1=mapArray toClaimQ before := by
  obtain ⟨claims,extra,before,decode,beforeEq⟩ :=
    JHm_SemanticOperands.source JGn_TerminalIdentified.shaDictionary () initial expanded sem expand verify
  refine ⟨before,decode,?_,?_,?_⟩
  · change mapArray (mapArray toClaimQ) (mapArray (mapArray retainedQ) sem.claims)=_
    rw [claims]
    simp only [mapArray,List.map_map,Function.comp_def]
    rfl
  · change mapArray toClaimQ (mapArray retainedQ sem.extra)=_
    rw [extra]
    simp only [mapArray,List.map_map,Function.comp_def]
    rfl
  · change mapArray toClaimQ (mapArray retainedQ sem.before_z1)=_
    rw [beforeEq]
    simp only [mapArray,List.map_map,Function.comp_def]
    rfl
#print axioms source
end AspisR1.JHm_RetainedOperands
end
