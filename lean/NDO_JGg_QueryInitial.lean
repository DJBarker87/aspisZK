import NDO_JGg_QueryFirst
import NDO_JGg_QueryArrays
set_option autoImplicit false
namespace AspisR1.JGg_QueryInitial
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge JGg_QuerySplit
attribute [local irreducible] later

theorem source {Hash A : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (k : transcript.Transcript Hash → Blocks → Blocks → Result A) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    initial D0 (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript Hash)
      31#u8 JGg_Opening31.payload k=
    later D0 hash JGg_QueryArrays.b1 JGg_QueryArrays.a1 (encodeState JGg_Opening31.next0)
      (k (⟨encodeState JGg_Opening31.absorbed,hash⟩ : transcript.Transcript Hash)) := by
  dsimp only
  have read : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.absorbed) 1#u8)=ok (encodeState JGg_Opening31.block0) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.readHash0]
  have advance : (AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)).digest hash
      (TranscriptStep.readParts (encodeState JGg_Opening31.absorbed) 2#u8)=ok (encodeState JGg_Opening31.next0) := by
    change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=_
    rw [JGg_Opening31.advanceHash0]
  have first := JGg_QueryFirst.source _
    (⟨encodeState JGg_Opening31.before,hash⟩ : transcript.Transcript Hash)
    (⟨encodeState JGg_Opening31.absorbed,hash⟩ : transcript.Transcript Hash) 31#u8 JGg_Opening31.payload
    (encodeState JGg_Opening31.block0) (encodeState JGg_Opening31.next0)
    (JGg_Opening31.absorb D hash) read advance k
  simpa only [JGg_QueryArrays.back_a,JGg_QueryArrays.back_b] using first
#print axioms source
end AspisR1.JGg_QueryInitial
