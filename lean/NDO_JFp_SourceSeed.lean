import NDO_JFp_SHADigest
import NDO_JFp_PrefixRoot
set_option autoImplicit false
namespace AspisR1.JFp_SourceSeed
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1NativeCompact AspisS1ValuesOwnedInstallation
open AspisV8R19.SqueezeOracleBridge

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (expanded : Slice U8) (pre : r1_wire.Prefix)
    (expand : compact.expand_semantic nativeValues JFw_RealExpansion.stored
      JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre)) :
    r1_semantic.public_transcript
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
        (F3V_OracleDictionary.current JFp_SHADigest.digest D))
      JFs_PublicSerialization.value hash pre.c1_root=ok (.Ok
        (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  rw [JFp_PrefixRoot.source expanded pre expand parse]
  exact JFp_SHADigest.source D hash

#print axioms source
end AspisR1.JFp_SourceSeed
