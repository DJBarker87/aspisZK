import NDO_JGg_OpeningLinks
import NDO_JGe_SemanticSame
set_option autoImplicit false
namespace AspisR1.JGg_OpeningSeed
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (sem : r1_semantic.Verified Hash) (view : verifier.View)
    (state : sem.transcript.state=encodeState JFu_Q26Source.ratchet) (variant : view.variant=.S2) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    transcript.Transcript.new D0 hash sem.transcript.state view.variant=
      ok (⟨encodeState JGe_OpeningInit.state,hash⟩ : transcript.Transcript Hash) := by
  rw [state,variant]
  exact JGe_OpeningInit.source D hash
#print axioms source
end AspisR1.JGg_OpeningSeed
