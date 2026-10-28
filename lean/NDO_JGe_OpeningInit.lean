import NDO_JGe_Init
import NDO_JFu_Q26Source
import RPz7_ExtractedDigest32Callers
set_option autoImplicit false
namespace AspisR1.JGe_OpeningInit
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

def state : State := JFp_SHADigest.output JGe_Init.result

theorem input : (flatten (CallerStep.reseedParts
    (encodeState JFu_Q26Source.ratchet) .S2)).map Fin.val=JGe_Init.message := by rfl
#print axioms input

theorem hash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
    (CallerStep.reseedParts (encodeState JFu_Q26Source.ratchet) .S2)=encodeState state := by
  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
  rw [input,JGe_Init.checked]
  rfl
#print axioms hash

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    transcript.Transcript.new D0 hash (encodeState JFu_Q26Source.ratchet) .S2=
      ok (⟨encodeState state,hash⟩ : transcript.Transcript Hash) := by
  dsimp only
  rw [CallerStep.opening_new_eq]
  change (do let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
             (CallerStep.reseedParts (encodeState JFu_Q26Source.ratchet) .S2))
             ok (⟨s,hash⟩ : transcript.Transcript Hash))=_
  rw [JGe_OpeningInit.hash,bind_tc_ok]
#print axioms source
end AspisR1.JGe_OpeningInit
