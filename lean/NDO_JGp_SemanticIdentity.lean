import NDO_JGn_CurrentPreparation
import NDO_PSem_ExpansionUnique
set_option autoImplicit false
namespace AspisR1.JGp_SemanticIdentity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition S1SemanticCarrier
open AspisV8R19.SqueezeOracleBridge

theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (initial expanded : Slice U8) (sem : r1_semantic.Verified H)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored initial=ok (.Ok (),expanded))
    (verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      expanded hash=ok (.Ok sem)) :
    sem.roots=Array.make 2#usize [JFp_InitBytes.root,JFq_Root1.value] ∧
      sem.transcript.state=encodeState JFu_Q26Source.ratchet := by
  obtain ⟨other,pre,view,otherExpand,parse,yexpand,wide,variant,y1eq,round0,root,round1,finalMessage,inactive,calls,finish⟩ :=
    JGg_OpeningFixture.inhabited D hash
  have same := PSem_ExpansionUnique.carrier_unique JFw_RealExpansion.stored
    JFw_RealExpansion.initial initial other expanded otherExpand expand
  subst other
  obtain ⟨out,finished,roots,state⟩ := finish JGn_TerminalIdentified.identified
  have run := JGi_CurrentSemantic.source D hash expanded pre out otherExpand parse finished
  have es : currentSem out=sem := core.result.Result.Ok.inj (Result.ok.inj (run.symm.trans verify))
  rw [←es]
  exact ⟨roots,state⟩
#print axioms source
end AspisR1.JGp_SemanticIdentity
