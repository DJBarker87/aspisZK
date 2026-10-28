import NDO_JGn_CurrentPreparation
import NDO_PSem_ExpansionUnique
import NDO_JHl_SemanticFields
set_option autoImplicit false
namespace AspisR1.JHl_SemanticIdentity
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
    sem.alpha=mapArray currentQ JFm_PartialAlpha.a10 ∧
      sem.z=mapArray currentPoint (Array.make 2#usize [JFu_CircleExact.z0,JFu_CircleExact.z1]) := by
  obtain ⟨other,pre,out,otherExpand,parse,finished,roots,state,alpha,z⟩ :=
    JHl_SemanticFields.source D hash JGn_TerminalIdentified.identified
  have same := PSem_ExpansionUnique.carrier_unique JFw_RealExpansion.stored
    JFw_RealExpansion.initial initial other expanded otherExpand expand
  subst other
  have run := JGi_CurrentSemantic.source D hash expanded pre out otherExpand parse finished
  have es : currentSem out=sem := core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans verify))
  rw [←es]
  change mapArray currentQ out.alpha=_ ∧ mapArray currentPoint out.z=_
  rw [alpha,z]
  exact ⟨rfl,rfl⟩
#print axioms source
end AspisR1.JHl_SemanticIdentity
