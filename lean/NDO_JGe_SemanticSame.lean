import NDO_JGe_Semantic
set_option autoImplicit false
namespace AspisR1.JGe_SemanticSame
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre))
    (identified : JGe_TerminalCondition.Identified) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ sem : r1_semantic.Verified Hash,
      FinishModel.finish children JGe_Boundaries.value D0 JFs_PublicSerialization.value pre
        (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
        JFm_Begin.challenges none=ok (.Ok sem) ∧
      sem.roots=Array.make 2#usize [JFp_InitBytes.root,JFq_Root1.value] ∧
      sem.transcript.state=encodeState JFu_Q26Source.ratchet := by
  obtain ⟨other,parsed,sem,expandedCall,parseCall,finish,roots,state⟩ := JGe_Semantic.source D hash identified
  have sameExpanded : other=expanded := congrArg Prod.snd (Result.ok.inj (expandedCall.symm.trans expand))
  subst other
  have samePre : parsed=pre := core.result.Result.Ok.inj (Result.ok.inj (parseCall.symm.trans parse))
  subst parsed
  exact ⟨sem,finish,roots,state⟩
#print axioms source
end AspisR1.JGe_SemanticSame
