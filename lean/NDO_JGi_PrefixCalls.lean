import NDO_JGg_OpeningFixture
set_option autoImplicit false
namespace AspisR1.JGi_PrefixCalls
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_semantic.public_transcript D0 JFs_PublicSerialization.value hash pre.c1_root=
      ok (.Ok (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript H)) ∧
    r1_wire.begin D0 pre (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript H)=
      ok (.Ok JFm_Begin.challenges,(⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript H)) := by
  obtain ⟨other,y1,parsed,view,claims,cs,mask,old,rest⟩ := JFu_FinishInputs.inhabited D JGe_Boundaries.value hash
  have sameExpanded : other=expanded := congrArg Prod.snd (Result.ok.inj (old.1.symm.trans expand))
  subst other
  have samePre : parsed=pre := core.result.Result.Ok.inj (Result.ok.inj (old.2.1.symm.trans parse))
  subst parsed
  exact ⟨old.2.2.2.2.2.2.1,old.2.2.2.2.2.2.2.1⟩
#print axioms source
end AspisR1.JGi_PrefixCalls
